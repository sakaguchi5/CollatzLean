import CollatzLean.Collatz3.Semantics.Runs


/-!
# Collatz3: thin infinite odd-only orbit

無限軌道の primitive data は、各時刻の値・2除算指数と、一段ごとの `OddStep` だけ。
FutureMinimum や標準選択、first-passage、Record--Ferrers はここには入れない。

有限区間を既存の `Runs` へ落とす bridge は derived theorem として与える。
-/

namespace Collatz3

/-- actual odd-only Collatz の無限軌道。 -/
structure OddOrbit where
  value : ℕ → ℕ
  exponent : ℕ → ℕ
  step : ∀ n : ℕ, OddStep (exponent n) (value n) (value (n + 1))

namespace OddOrbit

/-- 各軌道値は奇数。 -/
theorem value_odd
    (O : OddOrbit)
    (n : ℕ) :
    Odd (O.value n) :=
  (O.step n).start_odd

/-- 各 odd-only 指数は正。 -/
theorem exponent_pos
    (O : OddOrbit)
    (n : ℕ) :
    0 < O.exponent n :=
  (O.step n).exponent_pos

/-- 位置 `i` から `q` odd steps の exponent word。 -/
def segmentWord (O : OddOrbit) : ℕ → ℕ → Word
  | _i, 0 => []
  | i, q + 1 => O.exponent i :: O.segmentWord (i + 1) q

@[simp] theorem segmentWord_zero
    (O : OddOrbit)
    (i : ℕ) :
    O.segmentWord i 0 = [] :=
  rfl

@[simp] theorem segmentWord_succ
    (O : OddOrbit)
    (i q : ℕ) :
    O.segmentWord i (q + 1) =
      O.exponent i :: O.segmentWord (i + 1) q :=
  rfl

/-- segment word の odd-step 数は指定長そのもの。 -/
@[simp] theorem segmentWord_oddSteps
    (O : OddOrbit)
    (i q : ℕ) :
    Word.oddSteps (O.segmentWord i q) = q := by
  induction q generalizing i with
  | zero =>
      rfl
  | succ q ih =>
      simp [segmentWord, ih]

/-- 無限軌道の有限 segment は既存の `Runs` relation を実現する。 -/
theorem runsSegment
    (O : OddOrbit)
    (i q : ℕ) :
    Runs (O.segmentWord i q) (O.value i) (O.value (i + q)) := by
  induction q generalizing i with
  | zero =>
      simpa [segmentWord] using Runs.nil (O.value i)
  | succ q ih =>
      have hTail := ih (i := i + 1)
      have hTail' :
          Runs (O.segmentWord (i + 1) q)
            (O.value (i + 1))
            (O.value (i + (q + 1))) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail
      exact Runs.cons (O.step i) hTail'

/-- segment word は actual run 由来なので valid。 -/
theorem segmentWord_valid
    (O : OddOrbit)
    (i q : ℕ) :
    Word.Valid (O.segmentWord i q) :=
  (O.runsSegment i q).valid

/--
ある時刻で `1` に到達したなら、その後の odd-only 軌道はずっと `1`。
自明な `1 → 1` step と一段決定性だけから導く。
-/
theorem value_eq_one_add_of_value_eq_one
    (O : OddOrbit)
    {n : ℕ}
    (hn : O.value n = 1) :
    ∀ q : ℕ, O.value (n + q) = 1 := by
  intro q
  induction q with
  | zero =>
      simpa using hn
  | succ q ih =>
      have hStep := O.step (n + q)
      rw [ih] at hStep
      have hEnd := OddStep.end_eq_one_of_start_eq_one hStep
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEnd

/-- `1` に到達した時刻以後の任意の位置の値は `1`。 -/
theorem value_eq_one_of_hit_of_le
    (O : OddOrbit)
    {n m : ℕ}
    (hn : O.value n = 1)
    (hnm : n ≤ m) :
    O.value m = 1 := by
  have hIndex : n + (m - n) = m :=
    Nat.add_sub_of_le hnm
  rw [← hIndex]
  exact O.value_eq_one_add_of_value_eq_one hn (m - n)

/--
時刻 `i<j` で同じ値に戻ったなら、その後の値列は幅 `j-i` で pointwise に周期的。
一段決定性を前向きに帰納して導く。
-/
theorem value_add_period_eq_of_repeat
    (O : OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j) :
    ∀ q : ℕ,
      O.value (i + q + (j - i)) = O.value (i + q) := by
  intro q
  induction q with
  | zero =>
      have hIndex : i + 0 + (j - i) = j := by omega
      rw [hIndex]
      simpa using heq.symm
  | succ q ih =>
      have hFuture := O.step (i + q + (j - i))
      have hCurrent := O.step (i + q)
      rw [ih] at hFuture
      have hEnd := (OddStep.deterministic hFuture hCurrent).2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEnd

/--
repeat 開始以後の任意の base から見ても、任意の後続値は一周期幅内の値に代表できる。
これが周期枝で tail minimum を有限探索へ落とすための有限代表補題。
-/
theorem exists_periodRepresentativeFrom_repeat
    (O : OddOrbit)
    {i j base : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j)
    (hBase : i ≤ base) :
    ∀ q : ℕ,
      ∃ r : ℕ,
        base ≤ r ∧
        r < base + (j - i) ∧
        O.value (base + q) = O.value r := by
  let d : ℕ := j - i
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt hij
  have hPeriodAt :
      ∀ a : ℕ, i ≤ a → O.value (a + d) = O.value a := by
    intro a hia
    have hShift := O.value_add_period_eq_of_repeat hij heq (a - i)
    have hIndex : i + (a - i) = a := Nat.add_sub_of_le hia
    rw [hIndex] at hShift
    simpa [d] using hShift
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hqd : q < d
      · refine ⟨base + q, by omega, ?_, rfl⟩
        dsimp [d] at hqd ⊢
        omega
      · have hdq : d ≤ q := Nat.le_of_not_gt hqd
        let q' : ℕ := q - d
        have hq'lt : q' < q := by
          dsimp [q']
          omega
        rcases ih q' hq'lt with ⟨r, hrBase, hrEnd, hRep⟩
        have hBaseQ : i ≤ base + q' := by omega
        have hStep := hPeriodAt (base + q') hBaseQ
        have hIndex : base + q' + d = base + q := by
          dsimp [q']
          omega
        rw [hIndex] at hStep
        exact ⟨r, hrBase, hrEnd, hStep.trans hRep⟩

/--
時刻 `i<j` で同じ値に戻ったなら、周期幅 `j-i` ごとにその基点値が何度でも再現する。
各反復は同じ長さの finite run の決定性だけで得る。
-/
theorem value_eq_repeat_base_mul_period
    (O : OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j) :
    ∀ k : ℕ,
      O.value (i + k * (j - i)) = O.value i := by
  let d : ℕ := j - i
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt hij
  have hIndex : i + d = j := by
    dsimp [d]
    exact Nat.add_sub_of_le (Nat.le_of_lt hij)
  have hReturn :
      Runs (O.segmentWord i d) (O.value i) (O.value i) := by
    have hSeg := O.runsSegment i d
    rw [hIndex, ← heq] at hSeg
    exact hSeg
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      let t : ℕ := i + k * d
      have hActual := O.runsSegment t d
      have hStart : O.value t = O.value i := by
        simpa [t, d] using ih
      rw [hStart] at hActual
      have hDet :=
        Runs.word_end_eq_of_common_start_same_oddSteps
          hReturn hActual
          (by simp)
      have hEnd : O.value (t + d) = O.value i :=
        hDet.2.symm
      simpa [t, d, Nat.succ_mul, Nat.add_assoc] using hEnd

end OddOrbit
end Collatz3
