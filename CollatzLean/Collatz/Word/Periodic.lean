import CollatzLean.Collatz.Word.Affine

/-!
# 有限アフィン語の周期反復排除

有効なexpanding語を自然数上で同じ語のまま無限反復実現することはできない。
無限軌道型には依存しない。
-/

namespace Collatz
namespace Word

/-- expanding語の正defect。 -/
def expandingDefect (w : Collatz.Word) (x : ℕ) : ℕ :=
  (3 ^ w.oddSteps - 2 ^ w.twoSteps) * x + w.affineConst

/-- 同じ有限語を自然数列上で無限反復実現できること。 -/
def HasInfiniteRepeatedRealization (w : Collatz.Word) : Prop :=
  ∃ x : ℕ → ℕ, ∀ n : ℕ, w.Realizes (x n) (x (n + 1))

/-- 非空語のaffine定数は正。 -/
theorem affineConst_pos_of_nonempty
    {w : Collatz.Word} (hne : w ≠ []) : 0 < w.affineConst := by
  cases w with
  | nil => contradiction
  | cons e w =>
      simp only [affineConst_cons]
      have hpow : 0 < 3 ^ oddSteps w := Nat.pow_pos (by omega)
      omega

/-- expanding語は非空。 -/
theorem nonempty_of_expanding
    {w : Collatz.Word} (h : w.Expanding) : w ≠ [] := by
  intro hnil
  subst w
  simp [Expanding, oddSteps, twoSteps] at h

/-- 一回の実現はexpanding defectをexactに輸送する。 -/
theorem Expanding.defect_transport
    {w : Collatz.Word} {x y : ℕ}
    (hE : w.Expanding) (hR : w.Realizes x y) :
    2 ^ w.twoSteps * w.expandingDefect y =
      3 ^ w.oddSteps * w.expandingDefect x := by
  let C : ℕ := 2 ^ w.twoSteps
  let A : ℕ := 3 ^ w.oddSteps
  let B : ℕ := w.affineConst
  let d : ℕ := A - C
  have hCA : C < A := by simpa [C, A, Expanding] using hE
  have hA : A = C + d := by dsimp [d]; omega
  have hrun : C * y = A * x + B := by simpa [C, A, B, Realizes] using hR
  change C * (d * y + B) = A * (d * x + B)
  rw [hA] at hrun ⊢
  calc
    C * (d * y + B) = d * (C * y) + C * B := by ring
    _ = d * ((C + d) * x + B) + C * B := by rw [hrun]
    _ = (C + d) * (d * x + B) := by ring

/-- defect輸送式を有限回反復した等式。 -/
theorem Expanding.repeated_defect_balance
    {w : Collatz.Word}
    (hE : w.Expanding)
    {x : ℕ → ℕ}
    (hR : ∀ n : ℕ, w.Realizes (x n) (x (n + 1))) :
    ∀ n : ℕ,
      (2 ^ w.twoSteps) ^ n * w.expandingDefect (x n) =
        (3 ^ w.oddSteps) ^ n * w.expandingDefect (x 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := hE.defect_transport (hR n)
      calc
        (2 ^ w.twoSteps) ^ (n + 1) * w.expandingDefect (x (n + 1))
            = (2 ^ w.twoSteps) ^ n *
                (2 ^ w.twoSteps * w.expandingDefect (x (n + 1))) := by
                  rw [pow_succ]
                  ring
        _ = (2 ^ w.twoSteps) ^ n *
              (3 ^ w.oddSteps * w.expandingDefect (x n)) := by rw [hstep]
        _ = 3 ^ w.oddSteps *
              ((2 ^ w.twoSteps) ^ n * w.expandingDefect (x n)) := by ring
        _ = 3 ^ w.oddSteps *
              ((3 ^ w.oddSteps) ^ n * w.expandingDefect (x 0)) := by rw [ih]
        _ = (3 ^ w.oddSteps) ^ (n + 1) * w.expandingDefect (x 0) := by
              rw [pow_succ]
              ring

/-- `n`回反復できるなら初期defectは`(2^H)^n`で割り切れる。 -/
theorem Expanding.basePow_dvd_initialDefect
    {w : Collatz.Word}
    (hE : w.Expanding)
    {x : ℕ → ℕ}
    (hR : ∀ n : ℕ, w.Realizes (x n) (x (n + 1)))
    (n : ℕ) :
    (2 ^ w.twoSteps) ^ n ∣ w.expandingDefect (x 0) := by
  have hbalance := hE.repeated_defect_balance hR n
  have hdvdProduct :
      (2 ^ w.twoSteps) ^ n ∣
        (3 ^ w.oddSteps) ^ n * w.expandingDefect (x 0) :=
    ⟨w.expandingDefect (x n), hbalance.symm⟩
  have hbaseCoprime : Nat.Coprime (2 ^ w.twoSteps) (3 ^ w.oddSteps) :=
    (by decide : Nat.Coprime 2 3).pow w.twoSteps w.oddSteps
  have hpowersCoprime := hbaseCoprime.pow n n
  exact hpowersCoprime.dvd_of_dvd_mul_left hdvdProduct

private theorem nat_lt_twoPow_succ (n : ℕ) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
      omega

private theorem twoPow_le_basePow {C : ℕ} (hC : 2 ≤ C) :
    ∀ n : ℕ, 2 ^ n ≤ C ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul ih hC

/-- 有効なexpanding語は自然数上で無限反復実現できない。 -/
theorem Valid.no_infiniteRepeatedRealization_of_expanding
    {w : Collatz.Word}
    (hvalid : w.Valid) (hE : w.Expanding) :
    ¬ w.HasInfiniteRepeatedRealization := by
  rintro ⟨x, hR⟩
  have hnonempty : w ≠ [] := nonempty_of_expanding hE
  have htwoStepsPos : 0 < w.twoSteps := twoSteps_pos_of_valid_nonempty hvalid hnonempty
  have hbase : 2 ≤ 2 ^ w.twoSteps := by
    obtain ⟨r, hr⟩ : ∃ r : ℕ, w.twoSteps = r + 1 :=
      ⟨w.twoSteps - 1, by omega⟩
    rw [hr, pow_succ]
    have hpowPos : 0 < 2 ^ r := Nat.pow_pos (by omega)
    omega
  let D : ℕ := w.expandingDefect (x 0)
  have hDpos : 0 < D := by
    have hBpos : 0 < w.affineConst := affineConst_pos_of_nonempty hnonempty
    dsimp [D, expandingDefect]
    omega
  let k : ℕ := D + 1
  have hdvd : (2 ^ w.twoSteps) ^ k ∣ D := by
    simpa [D, k] using hE.basePow_dvd_initialDefect hR k
  have hdivisor_le : (2 ^ w.twoSteps) ^ k ≤ D := Nat.le_of_dvd hDpos hdvd
  have hD_lt_two : D < 2 ^ k := by simpa [k] using nat_lt_twoPow_succ D
  have htwo_le_base : 2 ^ k ≤ (2 ^ w.twoSteps) ^ k := twoPow_le_basePow hbase k
  omega

end Word
end Collatz
