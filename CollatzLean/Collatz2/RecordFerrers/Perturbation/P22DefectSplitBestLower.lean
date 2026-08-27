import CollatzLean.Collatz2.RecordFerrers.Perturbation.P21AdjacentCutRealization

/-!
# Record–Ferrers 摂動理論 22: defect split と lower-best 位相

隣接 pair の outer length `L` を内部 cut `x` で

  L = x + (L-x)

と分けたとき、P09/P21 の one-bit defect が発生するための純算術条件は

  criticalCarry x (L-x) = 0

である。

本ファイルでは、この条件を `log₂ 3` の実数演算を導入せずに exact に数論化する。
positive `n` について

  criticalHeight n = floor (n * log₂ 3)

なので

  3^n / 2^(criticalHeight n)

は `n * log₂ 3` の小数部分と同じ順序を持つ。そこで

  phase(x) < phase(L)

を division なしの cross-product

  3^x * 2^(criticalHeight L)
    < 3^L * 2^(criticalHeight x)

で定義する。

この順序で `L` がそれ以前の全 positive denominator より小さい phase を持つことを
`CriticalLowerBestDenominator L` と呼ぶ。これは

  floor(L * log₂ 3) / L

が、分母 `L` までの下側近似の中で numerator error

  L * log₂ 3 - floor(L * log₂ 3)

を strict record minimum にするという one-sided best approximation of the second kind の
純整数版である。

主定理は

  defect split が存在する
    ↔ L は lower-best denominator ではない

という exact equivalence である。

continued fraction の convergent / semiconvergent との同値は、このファイルでは使わない。
ここでは carry と lower-best 位相の対応だけを閉じる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
`x` の critical lower phase が `L` の phase より strict に小さいこと。

実数 division を使わず、positive quantity の cross-product だけで定義する。
-/
def CriticalLowerPhaseLess (x L : ℕ) : Prop :=
  3 ^ x * 2 ^ criticalHeight L <
    3 ^ L * 2 ^ criticalHeight x

/--
outer length `L` の内部 split `x` が one-bit carry defect を作ること。
-/
def DefectSplit (L x : ℕ) : Prop :=
  0 < x ∧
    x < L ∧
    criticalCarry x (L - x) = 0

/--
`L` が lower phase の strict record minimum denominator であること。

positive `x < L` に phase の小さいものが一つもない、という exact finite condition。
-/
def CriticalLowerBestDenominator (L : ℕ) : Prop :=
  0 < L ∧
    ∀ x : ℕ,
      0 < x →
      x < L →
      ¬ CriticalLowerPhaseLess x L

/--
任意の `k` で、critical roof の直上の 2 冪は `3^k` より strict に大きい。

既存の weak inequality と odd/even parity から equality を排除する。
-/
theorem threePow_lt_twoPow_criticalHeight_succ_strict
    {k : ℕ} :
    3 ^ k < 2 ^ (criticalHeight k + 1) := by
  have hLe :
      3 ^ k ≤ 2 ^ (criticalHeight k + 1) :=
    threePow_le_twoPow_criticalHeight_succ k
  have hNe :
      3 ^ k ≠ 2 ^ (criticalHeight k + 1) := by
    intro hEq
    have hOdd : Odd (3 ^ k) :=
      (show Odd (3 : ℕ) by decide).pow
    rcases hOdd with ⟨a, ha⟩
    have hEven :
        ∃ b : ℕ,
          2 ^ (criticalHeight k + 1) = 2 * b := by
      refine ⟨2 ^ criticalHeight k, ?_⟩
      rw [pow_succ]
      ring
    rcases hEven with ⟨b, hb⟩
    rw [ha, hb] at hEq
    omega
  exact lt_of_le_of_ne hLe hNe

/--
非終端 cut `x < L` では、
carry zero と lower-phase descent が exact に同値。

`x = 0` も許される。

carry zero なら

  criticalHeight L
    = criticalHeight x + criticalHeight (L-x)

となり、phase comparison は補区間 `L-x` に対する

  2^(criticalHeight (L-x)) < 3^(L-x)

へ帰着する。

carry one なら critical roof の直上 inequality により
phase order が strict に逆転する。
-/
theorem criticalCarry_eq_zero_iff_criticalLowerPhaseLess
    {L x : ℕ}
    (hxLt : x < L) :
    criticalCarry x (L - x) = 0 ↔
      CriticalLowerPhaseLess x L := by
  let y := L - x
  have hyPos : 0 < y := by
    dsimp [y]
    omega
  have hxy : x + y = L := by
    dsimp [y]
    omega
  constructor
  · intro hCarry
    have hAdd := criticalHeight_add_eq x y
    rw [hCarry] at hAdd
    simp only [Nat.add_zero] at hAdd
    rw [hxy] at hAdd
    have hCritY :
        2 ^ criticalHeight y < 3 ^ y :=
      criticalHeight_pow_lt_threePow hyPos
    unfold CriticalLowerPhaseLess
    calc
      3 ^ x * 2 ^ criticalHeight L
          =
        (3 ^ x * 2 ^ criticalHeight x) *
          2 ^ criticalHeight y := by
            rw [hAdd, pow_add]
            ring
      _ <
        (3 ^ x * 2 ^ criticalHeight x) * 3 ^ y := by
          exact
            (Nat.mul_lt_mul_left
              (by positivity :
                0 < 3 ^ x * 2 ^ criticalHeight x)).2 hCritY
      _ = 3 ^ L * 2 ^ criticalHeight x := by
          rw [← hxy, pow_add]
          ring
  · intro hPhase
    rcases criticalCarry_eq_zero_or_one x y with hZero | hOne
    · exact hZero
    · have hAdd := criticalHeight_add_eq x y
      rw [hOne, hxy] at hAdd
      have hUpperY :
          3 ^ y < 2 ^ (criticalHeight y + 1) :=
        threePow_lt_twoPow_criticalHeight_succ_strict
      have hReverse :
          3 ^ L * 2 ^ criticalHeight x <
            3 ^ x * 2 ^ criticalHeight L := by
        calc
          3 ^ L * 2 ^ criticalHeight x
              =
            (3 ^ x * 2 ^ criticalHeight x) * 3 ^ y := by
              rw [← hxy, pow_add]
              ring
          _ <
            (3 ^ x * 2 ^ criticalHeight x) *
              2 ^ (criticalHeight y + 1) := by
                exact
                  (Nat.mul_lt_mul_left
                    (by positivity :
                      0 < 3 ^ x * 2 ^ criticalHeight x)).2 hUpperY
          _ = 3 ^ x *
              (2 ^ criticalHeight x *
                2 ^ (criticalHeight y + 1)) := by ring
          _ = 3 ^ x *
              2 ^ (criticalHeight x + (criticalHeight y + 1)) := by
                rw [← pow_add]
          _ = 3 ^ x * 2 ^ criticalHeight L := by
              have hExp :
                  criticalHeight x + (criticalHeight y + 1) =
                    criticalHeight L := by
                omega
              rw [hExp]
      unfold CriticalLowerPhaseLess at hPhase
      exact (Nat.lt_asymm hPhase hReverse).elim

/--
## 主定理 1: Defect Split ⇔ Not Best-Lower

positive outer length `L` について

  ∃ 0 < x < L, criticalCarry x (L-x) = 0

であることと、`L` が lower-phase の strict record denominator ではないことは同値。

これは `floor(L log₂3)/L` の one-sided lower-best 性を pure carry 条件へ戻す exact bridge。
-/
theorem exists_defectSplit_iff_not_criticalLowerBest
    {L : ℕ}
    (hLPos : 0 < L) :
    (∃ x : ℕ, DefectSplit L x) ↔
      ¬ CriticalLowerBestDenominator L := by
  constructor
  · rintro ⟨x, hx⟩
    rcases hx with ⟨hxPos, hxLt, hCarry⟩
    intro hBest
    have hPhase : CriticalLowerPhaseLess x L :=
      (criticalCarry_eq_zero_iff_criticalLowerPhaseLess hxLt).1 hCarry
    exact hBest.2 x hxPos hxLt hPhase
  · intro hNotBest
    by_contra hNoSplit
    apply hNotBest
    refine ⟨hLPos, ?_⟩
    intro x hxPos hxLt hPhase
    have hCarry : criticalCarry x (L - x) = 0 :=
      (criticalCarry_eq_zero_iff_criticalLowerPhaseLess hxLt).2 hPhase
    apply hNoSplit
    refine ⟨x, ?_⟩
    exact ⟨hxPos, hxLt, hCarry⟩

/--
rigid branch の carry-only characterization。

lower-best denominator であることは、全 proper split が carry one であることと exact に同値。
したがって P22 以後は flexible branch と rigid branch を carry だけで場合分けできる。
-/
theorem criticalLowerBest_iff_all_proper_carry_one
    {L : ℕ}
    (hLPos : 0 < L) :
    CriticalLowerBestDenominator L ↔
      ∀ x : ℕ,
        0 < x →
        x < L →
        criticalCarry x (L - x) = 1 := by
  constructor
  · intro hBest x hxPos hxLt
    have hNotZero : criticalCarry x (L - x) ≠ 0 := by
      intro hZero
      have hPhase : CriticalLowerPhaseLess x L :=
        (criticalCarry_eq_zero_iff_criticalLowerPhaseLess hxLt).1 hZero
      exact hBest.2 x hxPos hxLt hPhase
    rcases criticalCarry_eq_zero_or_one x (L - x) with hZero | hOne
    · exact False.elim (hNotZero hZero)
    · exact hOne
  · intro hAll
    refine ⟨hLPos, ?_⟩
    intro x hxPos hxLt hPhase
    have hZero : criticalCarry x (L - x) = 0 :=
      (criticalCarry_eq_zero_iff_criticalLowerPhaseLess hxLt).2 hPhase
    have hOne := hAll x hxPos hxLt
    omega

end RecordFerrers
end Collatz2
