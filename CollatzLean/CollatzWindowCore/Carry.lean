import CollatzLean.CollatzOrbitCore.InfiniteOrbit
import CollatzLean.CollatzFirstLayer.CarrySynchronization



/-!
# q-windowとfirst-carry

qだけ離れた二つの実軌道値にfirst-carry三分岐を適用し、captureが
q-windowの総2除算数を真に減らし、synchronized carryが保存することを示す。
これはcapture正規化に用いる自然数単調量である。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- 位置`i`から長さ`q`のwindowが消費する総2除算数。 -/
def windowTwoSteps (O : OddOrbit) (i q : ℕ) : ℕ :=
  twoSteps (O.segmentWord i q)

/-- 長さ1のwindow総指数はその位置の指数。 -/
@[simp] theorem windowTwoSteps_one (O : OddOrbit) (i : ℕ) :
    O.windowTwoSteps i 1 = O.exponent i := by
  simp [windowTwoSteps, segmentWord, twoSteps]

/-- q-windowを一段ずらしたときのexactな指数収支。 -/
theorem windowTwoSteps_shift_balance
    (O : OddOrbit) (i q : ℕ) :
    O.exponent i + O.windowTwoSteps (i + 1) q =
      O.windowTwoSteps i q + O.exponent (i + q) := by
  have hleft := congrArg twoSteps (O.segmentWord_add i 1 q)
  have hright := congrArg twoSteps (O.segmentWord_add i q 1)
  rw [twoSteps_append] at hleft hright
  calc
    O.exponent i + O.windowTwoSteps (i + 1) q
        = twoSteps (O.segmentWord i (1 + q)) := by
            symm
            simpa [windowTwoSteps] using hleft
    _ = twoSteps (O.segmentWord i (q + 1)) := by
          congr 1
          simp [Nat.add_comm]
    _ = O.windowTwoSteps i q + O.exponent (i + q) := by
          simpa [windowTwoSteps] using hright

/-- qだけ離れた二値の正の完全2進差分。 -/
structure WindowDifferenceData
    (O : OddOrbit) (i q : ℕ) where
  depth : ℕ
  oddPart : ℕ
  difference :
    O.value (i + q) = O.value i + 2 ^ depth * oddPart
  oddPart_odd : Odd oddPart

namespace WindowDifferenceData

/-- 正の奇数部分を持つwindow差は正順序。 -/
theorem value_lt
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    O.value i < O.value (i + q) := by
  rw [D.difference]
  apply Nat.lt_add_of_pos_right
  apply Nat.mul_pos
  · exact Nat.pow_pos (by omega)
  · rcases D.oddPart_odd with ⟨k, hk⟩
    omega

end WindowDifferenceData

/-- lower側の次指数が差深さより大きいcaptured carry。 -/
structure CapturedWindowAt
    (O : OddOrbit) (i q : ℕ) extends WindowDifferenceData O i q where
  captured : depth < O.exponent i

/-- lower側の次指数が差深さより小さいsynchronized carry。 -/
structure SynchronizedWindowAt
    (O : OddOrbit) (i q : ℕ) extends WindowDifferenceData O i q where
  synchronized : O.exponent i < depth

/-- lower側の次指数が差深さに一致するdeferred carry。 -/
structure DeferredWindowAt
    (O : OddOrbit) (i q : ℕ) extends WindowDifferenceData O i q where
  deferred : depth = O.exponent i


/-- ordered windowのfirst-carry完全三分岐。 -/
inductive WindowCarryOutcome
    (O : OddOrbit) (i q : ℕ) : Type
  | captured (data : CapturedWindowAt O i q)
  | synchronized (data : SynchronizedWindowAt O i q)
  | deferred (data : DeferredWindowAt O i q)

/-- 完全2進差分を持つ任意のordered windowを三枝へ分類する。 -/
theorem windowCarryOutcome_nonempty
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    Nonempty (WindowCarryOutcome O i q) := by
  rcases lt_trichotomy D.depth (O.exponent i) with hcap | heq | hsync
  · exact ⟨WindowCarryOutcome.captured
      { toWindowDifferenceData := D
        captured := hcap }⟩
  · exact ⟨WindowCarryOutcome.deferred
      { toWindowDifferenceData := D
        deferred := heq }⟩
  · exact ⟨WindowCarryOutcome.synchronized
      { toWindowDifferenceData := D
        synchronized := hsync }⟩

/-- first-carry outcomeを古典選択で一つ取り出す。 -/
noncomputable def windowCarryOutcome
    {O : OddOrbit} {i q : ℕ}
    (D : WindowDifferenceData O i q) :
    WindowCarryOutcome O i q :=
  Classical.choice (windowCarryOutcome_nonempty D)

namespace CapturedWindowAt

/-- captureでは上側位置のactual指数が差深さにexactに一致する。 -/
theorem upperExponent_eq_depth
    {O : OddOrbit} {i q : ℕ}
    (C : CapturedWindowAt O i q) :
    O.exponent (i + q) = C.depth := by
  let r := O.exponent i - C.depth
  have hr : 0 < O.exponent i - C.depth := by
    exact Nat.sub_pos_of_lt C.captured
  have he : O.exponent i = C.depth + r := by
    dsimp [r]
    omega
  have hlower :
      3 * O.value i + 1 =
        2 ^ (C.depth + r) * O.value (i + 1) := by
    rw [← he]
    exact (O.step i).symm
  obtain ⟨b, hb⟩ :=
    first_carry_strict
      hr C.difference C.oddPart_odd
      hlower (O.value_odd (i + 1))
  have hactual :
      ExactTwoFactor
        (3 * O.value (i + q) + 1)
        (O.exponent (i + q))
        (O.value (i + q + 1)) := by
    refine ⟨?_, O.value_odd _⟩
    simpa [Nat.add_assoc] using (O.step (i + q)).symm
  exact (exactTwoFactor_exponent_unique hactual hb)

/-- captureではwindow終端の指数がwindow始端の指数より真に小さい。 -/
theorem upperExponent_lt_lowerExponent
    {O : OddOrbit} {i q : ℕ}
    (C : CapturedWindowAt O i q) :
    O.exponent (i + q) < O.exponent i := by
  rw [C.upperExponent_eq_depth]
  exact C.captured

/-- captured carryはq-window総指数を真に減らす。 -/
theorem windowTwoSteps_strict_decrease
    {O : OddOrbit} {i q : ℕ}
    (C : CapturedWindowAt O i q) :
    O.windowTwoSteps (i + 1) q < O.windowTwoSteps i q := by
  have hbalance :=
    O.windowTwoSteps_shift_balance i q
  have hexponent :=
    C.upperExponent_lt_lowerExponent
  omega

end CapturedWindowAt


/-- 連続capture区間では、終端window総指数と区間長の和が初期値以下。 -/
theorem windowTwoSteps_add_length_le_of_all_captured
    {O : OddOrbit} {q start T : ℕ}
    (h : ∀ k : ℕ, k < T →
      Nonempty (CapturedWindowAt O (start + k) q)) :
    O.windowTwoSteps (start + T) q + T ≤
      O.windowTwoSteps start q := by
  induction T generalizing start with
  | zero => simp
  | succ T ih =>
      rcases h 0 (by omega) with ⟨C⟩
      have hfirst :
          O.windowTwoSteps (start + 1) q <
            O.windowTwoSteps start q := by
        simpa using C.windowTwoSteps_strict_decrease
      have htail : ∀ k : ℕ, k < T →
          Nonempty (CapturedWindowAt O ((start + 1) + k) q) := by
        intro k hk
        have hs := h (k + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      have hrest := ih (start := start + 1) htail
      have hindex : start + (T + 1) = (start + 1) + T := by omega
      rw [hindex]
      omega

/-- captureだけが永久に続くことはできない。 -/
theorem not_all_windows_captured
    (O : OddOrbit) (q start : ℕ) :
    ¬ (∀ k : ℕ, Nonempty (CapturedWindowAt O (start + k) q)) := by
  intro h
  let T := O.windowTwoSteps start q + 1
  have hbound :=
    windowTwoSteps_add_length_le_of_all_captured
      (O := O) (q := q) (start := start) (T := T)
      (by
        intro k hk
        exact h k)
  dsimp [T] at hbound
  omega

namespace SynchronizedWindowAt

/-- synchronized carryでは上側位置もlower側と同じ指数を使う。 -/
theorem upperExponent_eq_lower
    {O : OddOrbit} {i q : ℕ}
    (C : SynchronizedWindowAt O i q) :
    O.exponent (i + q) = O.exponent i := by
  let e := O.exponent i
  let a := O.value (i + 1)
  have hlower : 3 * O.value i + 1 = 2 ^ e * a := by
    dsimp [e, a]
    exact (O.step i).symm
  let S : SynchronizedCarry
      (O.value i) (O.value (i + q)) C.depth e a C.oddPart :=
    synchronized_carry_of_depth_lt
      C.synchronized C.difference C.oddPart_odd
      hlower (O.value_odd (i + 1))
  have hactual :
      ExactTwoFactor
        (3 * O.value (i + q) + 1)
        (O.exponent (i + q))
        (O.value (i + q + 1)) := by
    refine ⟨?_, O.value_odd _⟩
    simpa [Nat.add_assoc] using (O.step (i + q)).symm
  have hsync :
      ExactTwoFactor
        (3 * O.value (i + q) + 1)
        e S.upperNext :=
    S.upperFactor
  have hu := exactTwoFactor_exponent_unique hactual hsync
  simpa [e] using hu

/-- synchronized carryはq-window総指数を保存する。 -/
theorem windowTwoSteps_eq
    {O : OddOrbit} {i q : ℕ}
    (C : SynchronizedWindowAt O i q) :
    O.windowTwoSteps (i + 1) q = O.windowTwoSteps i q := by
  have hbalance := O.windowTwoSteps_shift_balance i q
  rw [C.upperExponent_eq_lower] at hbalance
  omega

end SynchronizedWindowAt


end OddOrbit
end CollatzSecondLayer2
