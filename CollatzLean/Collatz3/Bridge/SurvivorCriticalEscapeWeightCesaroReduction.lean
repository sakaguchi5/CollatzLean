import CollatzLean.Collatz3.Bridge.SurvivorCriticalEscapeWeight
import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog

/-!
# Collatz3 Bridge: 2021 Lemma 41 の Cesàro 問題を irrational rotation へ還元

2021 年論文 Lemma 41 の列

`t_i = 2^floor((i-1) log₂ 3) / 3^i`

は、`m=i-1` と置けば現在の

`criticalEscapeWeight m = 2^beattyIndex(m) / 3^(m+1)`

と exact に同じ列である。

現行 repo では既に

`beattyIndex m = floor(m log₂ 3)`

および `log₂ 3` の無理数性が証明されているので、Lemma 41 の残る解析内容は
純粋な irrational rotation / Weyl 等分布の Cesàro 定理だけである。

重要:
このファイルは、その generic Weyl 定理を 未証明の原理や追加仮定として捏造しない。
現行 mathlib には必要な pointwise equidistribution theorem が無いため、
ここでは Collatz 固有部分を exact に除去し、Lemma 41 本体と Weyl 層の境界を theorem として保存する。

後続では generic irrational-rotation Cesàro theorem を独立に形式化し、
この reduction に差し込めばよい。
-/

namespace Collatz3
namespace Bridge

open Filter

/--
2021 Lemma 41 の `i=m+1` 項と `criticalEscapeWeight m` は exact に一致する。
-/
theorem criticalEscapeWeight_eq_lemma41_term
    (m : ℕ) :
    criticalEscapeWeight m =
      (2 : ℝ) ^ ⌊(m : ℝ) * Real.logb 2 3⌋₊ /
        (3 : ℝ) ^ (m + 1) := by
  unfold criticalEscapeWeight
  rw [beattyIndex_eq_natFloor_logb_two_three]

/--
有限 Cesàro sum も 2021 Lemma 41 の floor 表示と exact に一致する。
-/
theorem criticalEscapeWeight_cesaro_eq_lemma41_floor_sum
    (N : ℕ) :
    (∑ m ∈ Finset.range N, criticalEscapeWeight m) / (N : ℝ) =
      (∑ m ∈ Finset.range N,
          ((2 : ℝ) ^ ⌊(m : ℝ) * Real.logb 2 3⌋₊ /
            (3 : ℝ) ^ (m + 1))) / (N : ℝ) := by
  apply congrArg (fun x : ℝ => x / (N : ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  exact criticalEscapeWeight_eq_lemma41_term m

/--
Lemma 41 の desired Cesàro convergence は、現在の `criticalEscapeWeight` 表現と
paper の floor 表現で完全に同値。

この theorem 自体は Weyl 等分布を仮定しない単なる exact reduction である。
-/
theorem criticalEscapeWeight_cesaro_tendsto_iff_lemma41_floor
    :
    Tendsto
        (fun N : ℕ =>
          (∑ m ∈ Finset.range N, criticalEscapeWeight m) / (N : ℝ))
        atTop
        (nhds (1 / (6 * Real.log 2) : ℝ)) ↔
      Tendsto
        (fun N : ℕ =>
          (∑ m ∈ Finset.range N,
              ((2 : ℝ) ^ ⌊(m : ℝ) * Real.logb 2 3⌋₊ /
                (3 : ℝ) ^ (m + 1))) / (N : ℝ))
        atTop
        (nhds (1 / (6 * Real.log 2) : ℝ)) := by
  have hFun :
      (fun N : ℕ =>
        (∑ m ∈ Finset.range N, criticalEscapeWeight m) / (N : ℝ)) =
      (fun N : ℕ =>
        (∑ m ∈ Finset.range N,
            ((2 : ℝ) ^ ⌊(m : ℝ) * Real.logb 2 3⌋₊ /
              (3 : ℝ) ^ (m + 1))) / (N : ℝ)) := by
    funext N
    exact criticalEscapeWeight_cesaro_eq_lemma41_floor_sum N
  rw [hFun]

/-- Lemma 41 に必要な回転 slope `log₂ 3` は既に無理数。 -/
theorem criticalEscapeWeight_lemma41_slope_irrational :
    Irrational (Real.logb 2 3) :=
  irrational_logb_two_three

end Bridge
end Collatz3
