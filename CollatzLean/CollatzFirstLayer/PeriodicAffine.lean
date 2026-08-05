import CollatzLean.CollatzFirstLayer.Affine
import Mathlib.Tactic.Ring

/-!
# 有限アフィン語の周期反復排除

有限指数語 `w` の一回の実現

`2^H y = 3^p x + B_w`

を同じ語のまま自然数上で無限に反復できるかを調べる。
語が有効かつ膨張するとき、defectの輸送式から初期defectが任意に高い
`(2^H)`冪で割り切れることになり、正の有限自然数性と矛盾する。

このファイルは無限軌道型には依存せず、有限語・自然数列・アフィン実現式だけを扱う。
-/

namespace CollatzFirstLayer
namespace ExpWord

/--
膨張語の正のdefect。

`D_w(x) = (3^p - 2^H) x + B_w`。
-/
def expandingDefect (w : ExpWord) (x : ℕ) : ℕ :=
  (3 ^ oddSteps w - 2 ^ twoSteps w) * x + affineConst w

/-- 同じ有限語を自然数列上で無限に反復実現できること。 -/
def HasInfiniteRepeatedRealization (w : ExpWord) : Prop :=
  ∃ x : ℕ → ℕ,
    ∀ n : ℕ, Realizes w (x n) (x (n + 1))

/-- 非空語のアフィン定数は正。 -/
theorem affineConst_pos_of_nonempty
    {w : ExpWord}
    (hne : w ≠ []) :
    0 < affineConst w := by
  cases w with
  | nil => contradiction
  | cons e w =>
      simp only [affineConst_cons]
      have hpow : 0 < 3 ^ oddSteps w :=
        Nat.pow_pos (by omega)
      omega

/-- 膨張語は非空。 -/
theorem nonempty_of_expanding
    {w : ExpWord}
    (h : Expanding w) :
    w ≠ [] := by
  intro hnil
  subst w
  simp [Expanding, oddSteps, twoSteps] at h

/--
一回のアフィン実現はdefectを

`2^H D_w(y) = 3^p D_w(x)`

に従って輸送する。
-/
theorem expandingDefect_transport
    {w : ExpWord} {x y : ℕ}
    (hexpanding : Expanding w)
    (hrealizes : Realizes w x y) :
    2 ^ twoSteps w * expandingDefect w y =
      3 ^ oddSteps w * expandingDefect w x := by
  let C : ℕ := 2 ^ twoSteps w
  let A : ℕ := 3 ^ oddSteps w
  let B : ℕ := affineConst w
  let d : ℕ := A - C
  have hCA : C < A := by
    simpa [C, A, Expanding] using hexpanding
  have hA : A = C + d := by
    dsimp [d]
    omega
  have hrun : C * y = A * x + B := by
    simpa [C, A, B, Realizes] using hrealizes
  change C * (d * y + B) = A * (d * x + B)
  rw [hA] at hrun ⊢
  calc
    C * (d * y + B)
        = d * (C * y) + C * B := by ring
    _ = d * ((C + d) * x + B) + C * B := by rw [hrun]
    _ = (C + d) * (d * x + B) := by ring

/-- defect輸送式を有限回反復した等式。 -/
theorem repeatedRealization_defect_balance
    {w : ExpWord}
    (hexpanding : Expanding w)
    {x : ℕ → ℕ}
    (hrealizes : ∀ n : ℕ, Realizes w (x n) (x (n + 1))) :
    ∀ n : ℕ,
      (2 ^ twoSteps w) ^ n * expandingDefect w (x n) =
        (3 ^ oddSteps w) ^ n * expandingDefect w (x 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep :=
        expandingDefect_transport
          hexpanding
          (hrealizes n)
      calc
        (2 ^ twoSteps w) ^ (n + 1) *
            expandingDefect w (x (n + 1))
            =
          (2 ^ twoSteps w) ^ n *
            (2 ^ twoSteps w * expandingDefect w (x (n + 1))) := by
              rw [pow_succ]
              ring
        _ =
          (2 ^ twoSteps w) ^ n *
            (3 ^ oddSteps w * expandingDefect w (x n)) := by
              rw [hstep]
        _ =
          3 ^ oddSteps w *
            ((2 ^ twoSteps w) ^ n * expandingDefect w (x n)) := by
              ring
        _ =
          3 ^ oddSteps w *
            ((3 ^ oddSteps w) ^ n * expandingDefect w (x 0)) := by
              rw [ih]
        _ =
          (3 ^ oddSteps w) ^ (n + 1) *
            expandingDefect w (x 0) := by
              rw [pow_succ]
              ring

/--
同じ膨張語を`n`回反復実現できるなら、初期defectは`(2^H)^n`で割り切れる。
-/
theorem repeatedRealization_basePow_dvd_initialDefect
    {w : ExpWord}
    (hexpanding : Expanding w)
    {x : ℕ → ℕ}
    (hrealizes : ∀ n : ℕ, Realizes w (x n) (x (n + 1)))
    (n : ℕ) :
    (2 ^ twoSteps w) ^ n ∣ expandingDefect w (x 0) := by
  have hbalance :=
    repeatedRealization_defect_balance
      hexpanding hrealizes n
  have hdvdProduct :
      (2 ^ twoSteps w) ^ n ∣
        (3 ^ oddSteps w) ^ n * expandingDefect w (x 0) := by
    exact ⟨expandingDefect w (x n), hbalance.symm⟩
  have h23 : Nat.Coprime 2 3 := by decide
  have hbaseCoprime :
      Nat.Coprime
        (2 ^ twoSteps w)
        (3 ^ oddSteps w) :=
    h23.pow (twoSteps w) (oddSteps w)
  have hpowersCoprime :
      Nat.Coprime
        ((2 ^ twoSteps w) ^ n)
        ((3 ^ oddSteps w) ^ n) :=
    hbaseCoprime.pow n n
  exact hpowersCoprime.dvd_of_dvd_mul_left hdvdProduct

/-- `n < 2^(n+1)`。最終矛盾で使う初等評価。 -/
private theorem nat_lt_twoPow_succ (n : ℕ) :
    n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ (n + 1) :=
        Nat.pow_pos (by omega)
      omega

/-- `2 ≤ C`なら`2^n ≤ C^n`。 -/
private theorem twoPow_le_basePow
    {C : ℕ}
    (hC : 2 ≤ C) :
    ∀ n : ℕ, 2 ^ n ≤ C ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul ih hC

/--
有効な膨張語を、自然数上で同じ語のまま無限反復実現することはできない。
-/
theorem no_infiniteRepeatedRealization_of_valid_expanding
    {w : ExpWord}
    (hvalid : Valid w)
    (hexpanding : Expanding w) :
    ¬ HasInfiniteRepeatedRealization w := by
  rintro ⟨x, hrealizes⟩
  have hnonempty : w ≠ [] :=
    nonempty_of_expanding hexpanding
  have htwoStepsPos : 0 < twoSteps w :=
    twoSteps_pos_of_valid_nonempty hvalid hnonempty
  have hbase : 2 ≤ 2 ^ twoSteps w := by
    obtain ⟨r, hr⟩ : ∃ r : ℕ, twoSteps w = r + 1 :=
      ⟨twoSteps w - 1, by omega⟩
    rw [hr, pow_succ]
    have hpowPos : 0 < 2 ^ r := Nat.pow_pos (by omega)
    omega
  let D : ℕ := expandingDefect w (x 0)
  have hDpos : 0 < D := by
    have hBpos : 0 < affineConst w :=
      affineConst_pos_of_nonempty hnonempty
    dsimp [D, expandingDefect]
    omega
  let k : ℕ := D + 1
  have hdvd : (2 ^ twoSteps w) ^ k ∣ D := by
    simpa [D, k] using
      repeatedRealization_basePow_dvd_initialDefect
        hexpanding hrealizes k
  have hdivisor_le : (2 ^ twoSteps w) ^ k ≤ D :=
    Nat.le_of_dvd hDpos hdvd
  have hD_lt_two : D < 2 ^ k := by
    simpa [k] using nat_lt_twoPow_succ D
  have htwo_le_base :
      2 ^ k ≤ (2 ^ twoSteps w) ^ k :=
    twoPow_le_basePow hbase k
  omega

end ExpWord
end CollatzFirstLayer
