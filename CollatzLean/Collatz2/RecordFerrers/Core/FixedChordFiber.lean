import CollatzLean.Collatz2.Geometry.RankPath
import CollatzLean.Collatz2.Geometry.CriticalProfile
/-!
# Record–Ferrers Phase A: fixed-chord fiber

既存の `Word` を一切置換せず、同じ exponent pair `(p,H)` を持つ valid word を
一つの fiber としてまとめる pure Record–Ferrers API。

この段階では record point / record block はまだ導入しない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- fixed `(oddSteps,twoSteps)=(p,H)` 上の genuine positive exponent word。 -/
structure FiberPoint (p H : ℕ) where
  word : Word
  valid : Valid word
  oddSteps_eq : oddSteps word = p
  twoSteps_eq : twoSteps word = H

namespace FiberPoint

/-- cut `k` の cumulative two-depth。 -/
def height {p H : ℕ} (x : FiberPoint p H) (k : ℕ) : ℕ :=
  prefixTwoDepth x.word k

@[simp] theorem height_zero {p H : ℕ} (x : FiberPoint p H) :
    x.height 0 = 0 := by
  simp [height, prefixTwoDepth]

/-- valid word では文字数以下の prefix cut は、その cut index 以上の two-depth を持つ。 -/
theorem oddSteps_le_twoSteps_of_valid
    {w : Word}
    (hValid : Valid w) :
    oddSteps w ≤ twoSteps w := by
  revert hValid
  induction w with
  | nil =>
      intro _
      simp [oddSteps, twoSteps]
  | cons e w ih =>
      intro hValid
      have he : 0 < e := hValid e (by simp)
      have hTail : Valid w := by
        intro a ha
        exact hValid a (by simp [ha])
      have hIH := ih hTail
      simp only [oddSteps_cons, twoSteps_cons]
      omega

/-- valid 性は arbitrary prefix に降りる。 -/
theorem valid_take
    {w : Word}
    (hValid : Valid w)
    (k : ℕ) :
    Valid (w.take k) := by
  have hWhole : Valid (w.take k ++ w.drop k) := by
    simpa using hValid
  exact hWhole.prefix

/-- valid 性は arbitrary suffix に降りる。 -/
theorem valid_drop
    {w : Word}
    (hValid : Valid w)
    (k : ℕ) :
    Valid (w.drop k) := by
  have hWhole : Valid (w.take k ++ w.drop k) := by
    simpa using hValid
  exact hWhole.suffix

/--
既存 record layer に依存しない prefix-depth の add/drop formula。
Phase A の deformation transport の基礎にする。
-/
theorem prefixTwoDepth_add_drop
    (w : Word)
    (a r : ℕ) :
    prefixTwoDepth w (a + r) =
      prefixTwoDepth w a + prefixTwoDepth (w.drop a) r := by
  unfold prefixTwoDepth
  have hTake :
      w.take (a + r) = w.take a ++ (w.drop a).take r := by
    induction a generalizing w with
    | zero => simp
    | succ a ih =>
        cases w with
        | nil => simp
        | cons x w => simp [Nat.succ_add, ih]
  rw [hTake, twoSteps_append]

/-- valid word の cut index は cumulative depth 以下。 -/
theorem index_le_prefixTwoDepth
    {w : Word}
    (hValid : Valid w)
    {k : ℕ}
    (hk : k ≤ oddSteps w) :
    k ≤ prefixTwoDepth w k := by
  have hTakeValid := valid_take hValid k
  have hBasic := oddSteps_le_twoSteps_of_valid hTakeValid
  have hkLen : k ≤ w.length := by
    simpa [oddSteps] using hk
  have hLen : (w.take k).length = k :=
    List.length_take_of_le hkLen
  simpa [oddSteps, prefixTwoDepth, hLen] using hBasic

/-- fixed-chord point の proper/terminal cut は index 以上の depth を持つ。 -/
theorem index_le_height
    {p H : ℕ}
    (x : FiberPoint p H)
    {k : ℕ}
    (hk : k ≤ p) :
    k ≤ x.height k := by
  apply index_le_prefixTwoDepth x.valid
  rw [x.oddSteps_eq]
  exact hk

/-- terminal cut の height は exact に `H`。 -/
@[simp] theorem height_terminal
    {p H : ℕ}
    (x : FiberPoint p H) :
    x.height p = H := by
  unfold height prefixTwoDepth
  have hpLen : p = x.word.length := by
    simpa [oddSteps] using x.oddSteps_eq.symm
  simpa [hpLen] using x.twoSteps_eq

/-- cut `k` の後ろには少なくとも `p-k` 個の positive exponent が残る。 -/
theorem height_add_remaining_le_terminal
    {p H : ℕ}
    (x : FiberPoint p H)
    {k : ℕ}
    (hk : k ≤ p) :
    x.height k + (p - k) ≤ H := by
  have hWordLen : x.word.length = p := by
    simpa [oddSteps] using x.oddSteps_eq
  have hkLen : k ≤ x.word.length := by
    omega
  have hSplit :
      twoSteps x.word =
        prefixTwoDepth x.word k + twoSteps (x.word.drop k) := by
    have h := twoSteps_append (x.word.take k) (x.word.drop k)
    rw [List.take_append_drop] at h
    simpa [prefixTwoDepth] using h
  have hDropValid := valid_drop x.valid k
  have hDropBasic := oddSteps_le_twoSteps_of_valid hDropValid
  have hWordLen : x.word.length = p := by
    simpa [oddSteps] using x.oddSteps_eq
  have hDropLen : oddSteps (x.word.drop k) = p - k := by
    unfold oddSteps
    rw [List.length_drop, hWordLen]
  rw [hDropLen] at hDropBasic
  rw [x.twoSteps_eq] at hSplit
  unfold height
  omega

/--
Ferrers column coordinate。positive exponent 1 を各 step から取り除いた prefix excess。
-/
def excessAt
    {p H : ℕ}
    (x : FiberPoint p H)
    (k : ℕ) : ℕ :=
  x.height k - k

@[simp] theorem excessAt_zero
    {p H : ℕ}
    (x : FiberPoint p H) :
    x.excessAt 0 = 0 := by
  simp [excessAt]

/-- `height = index + excess` の exact decomposition。 -/
theorem height_eq_index_add_excess
    {p H : ℕ}
    (x : FiberPoint p H)
    {k : ℕ}
    (hk : k ≤ p) :
    x.height k = k + x.excessAt k := by
  unfold excessAt
  have hle := x.index_le_height hk
  omega

/-- Ferrers excess profile は cut index に沿って nondecreasing。 -/
theorem excess_mono
    {p H : ℕ}
    (x : FiberPoint p H)
    {k l : ℕ}
    (hkl : k ≤ l)
    (hl : l ≤ p) :
    x.excessAt k ≤ x.excessAt l := by
  let r := l - k
  have hkr : k + r = l := by
    dsimp [r]
    omega
  have hkLe : k ≤ p := le_trans hkl hl
  have hDropOdd : oddSteps (x.word.drop k) = p - k := by
    unfold oddSteps
    rw [List.length_drop]
    simpa [oddSteps] using congrArg (fun n => n - k) x.oddSteps_eq
  have hrLe : r ≤ oddSteps (x.word.drop k) := by
    rw [hDropOdd]
    dsimp [r]
    omega
  have hRise :=
    index_le_prefixTwoDepth (valid_drop x.valid k) hrLe
  have hDepth := prefixTwoDepth_add_drop x.word k r
  rw [hkr] at hDepth
  have hkHeight := x.index_le_height hkLe
  have hlHeight := x.index_le_height hl
  unfold excessAt height
  omega

/-- fixed `(p,H)` fiber は rectangle height `H-p` の中に入る。 -/
theorem excess_le_rectangleHeight
    {p H : ℕ}
    (x : FiberPoint p H)
    {k : ℕ}
    (hk : k ≤ p) :
    x.excessAt k ≤ H - p := by
  have hRemain := x.height_add_remaining_le_terminal hk
  have hIndex := x.index_le_height hk
  unfold excessAt
  omega

/--
full prefix-height profile は fixed-chord valid word の complete invariant。
既存 lossless `(p,H,B)` decoder を使って word equality まで戻す。
-/
theorem word_eq_of_height_eq
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hHeight : ∀ k : ℕ, k < p → x.height k = y.height k) :
    x.word = y.word := by
  have hB : affineConst x.word = affineConst y.word := by
    rw [← affinePathSum_eq_affineConst,
        ← affinePathSum_eq_affineConst]
    unfold affinePathSum
    rw [x.oddSteps_eq, y.oddSteps_eq]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < p := Finset.mem_range.mp hk
    unfold affinePathTerm
    rw [x.oddSteps_eq, y.oddSteps_eq]
    change
      2 ^ x.height k * 3 ^ (p - (k + 1)) =
        2 ^ y.height k * 3 ^ (p - (k + 1))
    rw [hHeight k hkLt]
  have hpEq :
      oddSteps x.word = oddSteps y.word := by
    calc
      oddSteps x.word = p := x.oddSteps_eq
      _ = oddSteps y.word := y.oddSteps_eq.symm
  have hHEq :
      twoSteps x.word = twoSteps y.word := by
    calc
      twoSteps x.word = H := x.twoSteps_eq
      _ = twoSteps y.word := y.twoSteps_eq.symm
  exact
    valid_word_unique_of_oddSteps_twoSteps_affineConst
      x.valid y.valid hpEq hHEq hB

/-- fixed-chord point equality は proper prefix heights だけで判定できる。 -/
theorem ext
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hHeight : ∀ k : ℕ, k < p → x.height k = y.height k) :
    x = y := by
  have hw := word_eq_of_height_eq hHeight
  cases x with
  | mk xw xv xp xH =>
      cases y with
      | mk yw yv yp yH =>
          dsimp at hw
          subst yw
          rfl

end FiberPoint

end RecordFerrers
end Collatz2
