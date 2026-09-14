import CollatzLean.Collatz3.CSTConditional.ACCounting
import CollatzLean.Collatz3.Bridge.SurvivorDefectLogGrowth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: linear defect lower bound から future-minimum / actual growth へ

高レベルの「A 型」という名称自体は primitive definition に固定しない。
ここでは必要な量的内容だけを、二つの自然数 `K, N` を持つ薄い条件

`m ≤ K * δ_m`  (`N ≤ m`)

として保存する。

これは `δ_m` が odd-step index `m` に対して少なくとも線形規模で成長することの
整数版 witness である。

Global CST 下では標準 future-minimum 列の defect は一 transition ごとに据え置きか `+1` なので、
この条件から次を derived theorem として導く。

* future-minimum index は transition 数に対して線形上界を持つ。
* 従って future-minimum block length の有限和、すなわち平均 block 長は一様に制御される。
* 十分長い区間では defect growth 自体が transition 数に対して線形下界を持つ。
* defect--log exact bridge と合わせると actual `log₂` value growth も transition 数に対して線形成長する。
  これは actual value の指数成長を意味する。

新しい orbit packet / state / alphabet は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
A 型側で必要な量的仮定だけを保存する thin predicate。

`N` 以後の odd-step index `m` で

`m ≤ K * infiniteSurvivorDefect(m)`。

`K > 0` も同じ witness に含める。
高レベルの漸近分類そのものはこの definition に固定しない。
-/
def LinearDefectLowerBound
    (O : Collatz3.OddOrbit)
    (K N : ℕ) : Prop :=
  0 < K ∧
    ∀ m : ℕ,
      N ≤ m →
        m ≤ K * infiniteSurvivorDefect O.exponent m

namespace FutureMinima

/--
`lengthWord` の有限和は selector index の actual 差そのもの。

新しい集約量を定義せず、既存 `lengthWord` から必要なときに導く。
-/
theorem lengthWord_sum_eq_index_sub
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (n q : ℕ) :
    (F.lengthWord n q).sum =
      F.index (n + q) - F.index n := by
  induction q generalizing n with
  | zero =>
      simp [lengthWord]
  | succ q ih =>
      rw [lengthWord]
      simp only [List.sum_cons]
      rw [ih (n := n + 1)]
      have h01 : F.index n ≤ F.index (n + 1) :=
        Nat.le_of_lt (F.index_strict (Nat.lt_succ_self n))
      have h1end : F.index (n + 1) ≤ F.index (n + (q + 1)) := by
        apply F.index_strict.monotone
        omega
      have hIndex :
          n + 1 + q = n + (q + 1) := by
        omega
      rw [hIndex]
      omega

/--
Global CST 下では `q` 本の標準 future-minimum transition で defect は高々 `q` しか増えない。

既存 `defectGrowth ≤ q` を endpoint defect の形へ戻した wrapper。
-/
theorem defect_end_le_start_add_transitions_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    infiniteSurvivorDefect O.exponent (F.index (n + q)) ≤
      infiniteSurvivorDefect O.exponent (F.index n) + q := by
  have hGrowth :=
    F.defectGrowth_le_transitions_of_globalCST
      G S hStandard n q
  have hNondec :=
    F.defect_end_eq_start_add_count_A_of_globalCST
      G S hStandard n q
  omega

/--
linear defect lower bound が開始 future minimum 以後で有効なら、`q` transitions 後の
selector index は

`K * (startDefect + q)`

以下。

つまり A 型側では future minima は arbitrarily sparse にはなれない。
-/
theorem index_le_mul_startDefect_add_transitions_of_linearDefect
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {K N n q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ F.index n) :
    F.index (n + q) ≤
      K * (infiniteSurvivorDefect O.exponent (F.index n) + q) := by
  have hIndexMono : F.index n ≤ F.index (n + q) := by
    apply F.index_strict.monotone
    omega
  have hEndLate : N ≤ F.index (n + q) :=
    le_trans hLate hIndexMono
  have hLinearEnd := hLinear.2 (F.index (n + q)) hEndLate
  have hDefect :=
    F.defect_end_le_start_add_transitions_of_globalCST
      G S hStandard n q
  exact
    le_trans hLinearEnd (Nat.mul_le_mul_left K hDefect)

/--
前定理を actual block-length sum へ移した形。

`Σ r_t ≤ K * (startDefect + q)`。
-/
theorem lengthWord_sum_le_mul_startDefect_add_transitions_of_linearDefect
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {K N n q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ F.index n) :
    (F.lengthWord n q).sum ≤
      K * (infiniteSurvivorDefect O.exponent (F.index n) + q) := by
  rw [F.lengthWord_sum_eq_index_sub n q]
  have hIndex :=
    F.index_le_mul_startDefect_add_transitions_of_linearDefect (q := q)
      G S hStandard hLinear hLate
  exact le_trans (Nat.sub_le _ _) hIndex

/--
`q` が開始 defect 以上なら、future-minimum index は純粋に transition 数の線形上界

`F.index(n+q) ≤ 2 K q`

を持つ。

これは「A 型では future minima が線形個数必要」という有限整数版。
-/
theorem index_le_two_mul_K_mul_transitions_of_linearDefect
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {K N n q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ F.index n)
    (hq : infiniteSurvivorDefect O.exponent (F.index n) ≤ q) :
    F.index (n + q) ≤ 2 * K * q := by
  have hIndex :=
    F.index_le_mul_startDefect_add_transitions_of_linearDefect (q := q)
      G S hStandard hLinear hLate
  have hSmall :
      infiniteSurvivorDefect O.exponent (F.index n) + q ≤ 2 * q := by
    omega
  have hScaled := Nat.mul_le_mul_left K hSmall
  calc
    F.index (n + q)
        ≤ K * (infiniteSurvivorDefect O.exponent (F.index n) + q) := hIndex
    _ ≤ K * (2 * q) := hScaled
    _ = 2 * K * q := by ring

/--
同じ条件で block-length sum も

`Σ r_t ≤ 2 K q`

となる。
従って `q>0` なら平均 block 長は `2K` 以下という有限和の形で表現できる。
-/
theorem lengthWord_sum_le_two_mul_K_mul_transitions_of_linearDefect
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {K N n q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ F.index n)
    (hq : infiniteSurvivorDefect O.exponent (F.index n) ≤ q) :
    (F.lengthWord n q).sum ≤ 2 * K * q := by
  rw [F.lengthWord_sum_eq_index_sub n q]
  have hIndex :=
    F.index_le_two_mul_K_mul_transitions_of_linearDefect
      G S hStandard hLinear hLate hq
  exact le_trans (Nat.sub_le _ _) hIndex

/--
Global CST 下の標準 future-minimum 区間で、actual `log₂` value growth は
natural defect growth から高々 `1` の margin 損失だけを引いた量より strict に大きい。

これは unconditional defect--log bridge を AC 非減少性へ接続した wrapper。
-/
theorem defectGrowth_sub_one_lt_logValueGap_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    (((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) - 1) <
      Real.logb 2 (O.value (F.index (n + q)) : ℝ) -
        Real.logb 2 (O.value (F.index n) : ℝ) := by
  have hIndexLe : F.index n ≤ F.index (n + q) := by
    apply F.index_strict.monotone
    omega
  have hIndexAdd :
      F.index n + (F.index (n + q) - F.index n) = F.index (n + q) :=
    Nat.add_sub_of_le hIndexLe
  have hDefectEq :=
    F.defect_end_eq_start_add_count_A_of_globalCST
      G S hStandard n q
  have hNondec :
      infiniteSurvivorDefect O.exponent (F.index n) ≤
        infiniteSurvivorDefect O.exponent (F.index (n + q)) := by
    omega
  have hSegment :=
    O.survivorSegment_natDefectGrowth_sub_one_lt_logValueGap
      S
      (F.index n)
      (F.index (n + q) - F.index n)
      (by simpa [hIndexAdd] using hNondec)
  simpa [hIndexAdd] using hSegment

/--
linear defect lower bound の late tail で、区間長 `q` が開始 defect を十分上回るなら

`q ≤ 2 K * defectGrowth`。

つまり A 型側では sufficiently long future-minimum interval の defect growth も
transition 数に対して線形下界を持つ。
-/
theorem transitions_le_two_mul_K_mul_defectGrowth_of_linearDefect
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {K N n q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ F.index n)
    (hLarge :
      2 * K * infiniteSurvivorDefect O.exponent (F.index n) ≤ q) :
    q ≤
      2 * K *
        (infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n)) := by
  let d : ℕ :=
    infiniteSurvivorDefect O.exponent (F.index (n + q)) -
      infiniteSurvivorDefect O.exponent (F.index n)
  have hIndexMono : F.index n ≤ F.index (n + q) := by
    apply F.index_strict.monotone
    omega
  have hEndLate : N ≤ F.index (n + q) :=
    le_trans hLate hIndexMono
  have hLinearEnd := hLinear.2 (F.index (n + q)) hEndLate
  have hIndexGe := F.index_ge (n + q)
  have hqIndex : q ≤ F.index (n + q) := by omega
  have hqDefect :
      q ≤ K * infiniteSurvivorDefect O.exponent (F.index (n + q)) :=
    le_trans hqIndex hLinearEnd
  have hDefectEq :=
    F.defect_end_eq_start_add_count_A_of_globalCST
      G S hStandard n q
  have hNondec :
      infiniteSurvivorDefect O.exponent (F.index n) ≤
        infiniteSurvivorDefect O.exponent (F.index (n + q)) := by
    omega
  have hDecomp :
      infiniteSurvivorDefect O.exponent (F.index (n + q)) =
        infiniteSurvivorDefect O.exponent (F.index n) + d := by
    dsimp [d]
    omega
  rw [hDecomp, Nat.mul_add] at hqDefect
  have hLarge' :
      2 * (K * infiniteSurvivorDefect O.exponent (F.index n)) ≤ q := by
    simpa [Nat.mul_assoc] using hLarge
  have hMain : q ≤ 2 * (K * d) := by
    omega
  simpa [d, Nat.mul_assoc] using hMain

/--
前定理と defect--log bridge を合成した A 型側の actual growth estimate。

`q` future-minimum transitions に対して

`q / (2K) - 1 < log₂(value_end / value_start)`。

従って late tail の actual future-minimum value は transition 数に対して指数的に増える。
式は `log₂` のまま保存し、不要な `Real.rpow` primitive は導入しない。
-/
theorem transitions_div_two_mul_K_sub_one_lt_logValueGap_of_linearDefect
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {K N n q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ F.index n)
    (hLarge :
      2 * K * infiniteSurvivorDefect O.exponent (F.index n) ≤ q) :
    (q : ℝ) / (2 * (K : ℝ)) - 1 <
      Real.logb 2 (O.value (F.index (n + q)) : ℝ) -
        Real.logb 2 (O.value (F.index n) : ℝ) := by
  let d : ℕ :=
    infiniteSurvivorDefect O.exponent (F.index (n + q)) -
      infiniteSurvivorDefect O.exponent (F.index n)
  have hGrowth :=
    F.transitions_le_two_mul_K_mul_defectGrowth_of_linearDefect
      G S hStandard hLinear hLate hLarge
  have hGrowthD : q ≤ 2 * K * d := by
    simpa [d] using hGrowth
  have hGrowthR :
      (q : ℝ) ≤ 2 * (K : ℝ) * (d : ℝ) := by
    exact_mod_cast hGrowthD
  have hKPosNat : 0 < K := hLinear.1
  have hKPos : (0 : ℝ) < 2 * (K : ℝ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast hKPosNat)
  have hDiv :
      (q : ℝ) / (2 * (K : ℝ)) ≤ (d : ℝ) := by
    apply (div_le_iff₀ hKPos).2
    nlinarith [hGrowthR]
  have hLog :=
    F.defectGrowth_sub_one_lt_logValueGap_of_globalCST
      G S hStandard n q
  have hLog' :
      (d : ℝ) - 1 <
        Real.logb 2 (O.value (F.index (n + q)) : ℝ) -
          Real.logb 2 (O.value (F.index n) : ℝ) := by
    simpa [d] using hLog
  linarith

end FutureMinima
end OddOrbit
end Collatz3
