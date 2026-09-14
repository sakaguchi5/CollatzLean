import CollatzLean.Collatz3.CSTConditional.ALinearGrowth
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscape
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: linear defect から normalized escape の実数極限へ

`ALinearGrowth` で置いた薄い条件

`m ≤ K * δ_m`  (`N ≤ m`)

を normalized escape coordinate

`R_m = 2^D_m * value(m) / 3^m`

へ接続する。

このファイルの中心は、A 型側で `R_m` が有限の正の実数極限を持つことを
有限 block estimate から導くことである。

`K*(N+q)` 以後の長さ `K` の block では linear defect lower bound により
各位置の defect が少なくとも `q` なので、各 normalized increment は

`1 / (3 * 2^q)`

以下になる。従って block 全体の増加量は

`(K/3) * (1/2)^q`

以下であり、geometric tail によって `R_m` は一様に上から抑えられる。

`R_m` 自体は unconditional に strict monotone なので、実数の bounded monotone convergence から
有限正極限 `L` を得る。

さらに

* `R_m / L → 1`
* `Σ_{k<m} 2^D_k / 3^(k+1) → L - x_0`
* `affineConst(segmentWord 0 m) / 3^m → L - x_0`

を derived theorem として得る。

最後の finite affine numerator は同時に `2^D_m` で割り切れるため、
後続の「real limit と natural 2-adic realization の衝突」へ接続できる。
ここではその衝突自体はまだ主張しない。

なお、この layer で実際に使う仮定は infinite coefficient survivor と
`LinearDefectLowerBound` だけであり、Global CST は追加で使わない。
Global CST は前段で A 型候補をこの形へ追い込む役割を担う。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional
open Filter

private theorem one_div_three_twoPow_eq_geometric
    (q : ℕ) :
    1 / (3 * (2 : ℝ) ^ q) =
      (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ q := by
  rw [div_pow]
  simp only [one_pow]
  field_simp

/--
linear defect lower bound の late block 内では、block 番号 `q` が current defect 以下になる。

`K*(N+q) ≤ m` と `m ≤ K*δ_m` を positive `K` で cancel するだけの整数補題。
-/
theorem blockIndex_le_defect_of_linearDefect
    (O : Collatz3.OddOrbit)
    {K N q m : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hm : K * (N + q) ≤ m) :
    q ≤ infiniteSurvivorDefect O.exponent m := by
  have hK : 0 < K := hLinear.1
  have hScale : N + q ≤ K * (N + q) := by
    exact Nat.le_mul_of_pos_left (N + q) hK
  have hLate : N ≤ m := by
    have hN : N ≤ N + q := by omega
    exact le_trans hN (le_trans hScale hm)
  have hMain := hLinear.2 m hLate
  have hKq :
      K * q ≤ K * infiniteSurvivorDefect O.exponent m := by
    calc
      K * q ≤ K * (N + q) := Nat.mul_le_mul_left K (by omega)
      _ ≤ m := hm
      _ ≤ K * infiniteSurvivorDefect O.exponent m := hMain
  exact Nat.le_of_mul_le_mul_left hKq hK

/--
`q` 番目の late block 内の各 normalized increment は geometric cap 以下。
-/
theorem normalizedEscapeIncrement_le_blockGeometric_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N q t : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    O.normalizedEscapeIncrement (K * (N + q) + t) ≤
      (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ q := by
  have hd :
      q ≤ infiniteSurvivorDefect O.exponent (K * (N + q) + t) :=
    O.blockIndex_le_defect_of_linearDefect
      hLinear (by omega)
  have hCap :=
    O.normalizedEscapeIncrement_le_of_le_defect S hd
  rw [one_div_three_twoPow_eq_geometric q] at hCap
  exact hCap

/--
late block 一個、すなわち連続 `K` odd steps の normalized increment 総和は

`(K/3) * (1/2)^q`

以下。
-/
theorem normalizedEscapeIncrement_blockSum_le_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    (∑ t ∈ Finset.range K,
        O.normalizedEscapeIncrement (K * (N + q) + t)) ≤
      ((K : ℝ) / 3) * (1 / 2 : ℝ) ^ q := by
  calc
    (∑ t ∈ Finset.range K,
        O.normalizedEscapeIncrement (K * (N + q) + t))
        ≤ ∑ _t ∈ Finset.range K,
            ((1 / 3 : ℝ) * (1 / 2 : ℝ) ^ q) := by
          apply Finset.sum_le_sum
          intro t _ht
          exact
            O.normalizedEscapeIncrement_le_blockGeometric_of_linearDefect
              S hLinear
    _ = (K : ℝ) * ((1 / 3 : ℝ) * (1 / 2 : ℝ) ^ q) := by
          simp
    _ = ((K : ℝ) / 3) * (1 / 2 : ℝ) ^ q := by
          ring

/--
late block endpoint 間の normalized escape 増加量も同じ geometric cap 以下。
-/
theorem normalizedEscapeCoordinate_blockStep_le_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    O.normalizedEscapeCoordinate (K * (N + (q + 1))) ≤
      O.normalizedEscapeCoordinate (K * (N + q)) +
        ((K : ℝ) / 3) * (1 / 2 : ℝ) ^ q := by
  have hTel :=
    O.normalizedEscapeCoordinate_add_eq_add_sum_range
      (K * (N + q)) K
  have hSum :=
    O.normalizedEscapeIncrement_blockSum_le_of_linearDefect
      S hLinear (q := q)
  have hIndex :
      K * (N + q) + K = K * (N + (q + 1)) := by
    ring
  rw [hIndex] at hTel
  rw [hTel]
  linarith

/--
late block endpoints の finite geometric bound。

`q` blocks 後でも総増加量は

`(2K/3) * (1 - (1/2)^q)`

以下。
-/
theorem normalizedEscapeCoordinate_blockEndpoint_le_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (q : ℕ) :
    O.normalizedEscapeCoordinate (K * (N + q)) ≤
      O.normalizedEscapeCoordinate (K * N) +
        (2 * (K : ℝ) / 3) *
          (1 - (1 / 2 : ℝ) ^ q) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hStep :=
        O.normalizedEscapeCoordinate_blockStep_le_of_linearDefect
          S hLinear (q := q)
      calc
        O.normalizedEscapeCoordinate (K * (N + (q + 1)))
            ≤ O.normalizedEscapeCoordinate (K * (N + q)) +
                ((K : ℝ) / 3) * (1 / 2 : ℝ) ^ q := hStep
        _ ≤ (O.normalizedEscapeCoordinate (K * N) +
              (2 * (K : ℝ) / 3) * (1 - (1 / 2 : ℝ) ^ q)) +
                ((K : ℝ) / 3) * (1 / 2 : ℝ) ^ q :=
              add_le_add_left ih _
        _ = O.normalizedEscapeCoordinate (K * N) +
              (2 * (K : ℝ) / 3) *
                (1 - (1 / 2 : ℝ) ^ (q + 1)) := by
              rw [pow_succ]
              ring

/--
linear defect lower bound の下では normalized escape coordinate 全体が一様に上から有界。

粗いが十分な bound として

`R_m ≤ R_(K N) + 2K/3`

を使う。
-/
theorem normalizedEscapeCoordinate_le_uniform_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (m : ℕ) :
    O.normalizedEscapeCoordinate m ≤
      O.normalizedEscapeCoordinate (K * N) + 2 * (K : ℝ) / 3 := by
  have hK : 0 < K := hLinear.1
  have hScale :
      N + (m + 1) ≤ K * (N + (m + 1)) := by
    exact Nat.le_mul_of_pos_left (N + (m + 1)) hK
  have hm : m ≤ K * (N + (m + 1)) := by
    have : m ≤ N + (m + 1) := by omega
    exact le_trans this hScale
  have hMono := O.normalizedEscapeCoordinate_monotone
  have hEnd :=
    O.normalizedEscapeCoordinate_blockEndpoint_le_of_linearDefect
      S hLinear (m + 1)
  have hPow : 0 ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
  have hOne : 1 - (1 / 2 : ℝ) ^ (m + 1) ≤ 1 := by linarith
  have hCoeff : 0 ≤ 2 * (K : ℝ) / 3 := by positivity
  calc
    O.normalizedEscapeCoordinate m
        ≤ O.normalizedEscapeCoordinate (K * (N + (m + 1))) := hMono hm
    _ ≤ O.normalizedEscapeCoordinate (K * N) +
          (2 * (K : ℝ) / 3) *
            (1 - (1 / 2 : ℝ) ^ (m + 1)) := hEnd
    _ ≤ O.normalizedEscapeCoordinate (K * N) +
          (2 * (K : ℝ) / 3) * 1 := by
            exact add_le_add_right (mul_le_mul_of_nonneg_left hOne hCoeff) _
    _ = O.normalizedEscapeCoordinate (K * N) + 2 * (K : ℝ) / 3 := by ring

/-- linear defect lower bound の下では normalized escape coordinate の range は上に有界。 -/
theorem normalizedEscapeCoordinate_bddAbove_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    BddAbove (Set.range O.normalizedEscapeCoordinate) := by
  refine ⟨O.normalizedEscapeCoordinate (K * N) + 2 * (K : ℝ) / 3, ?_⟩
  rintro y ⟨m, rfl⟩
  exact O.normalizedEscapeCoordinate_le_uniform_of_linearDefect S hLinear m

/--
A 型の量的条件 `LinearDefectLowerBound` の下では normalized escape coordinate は
有限正の実数極限 `L` を持つ。

`R_m` は unconditional に monotone、前定理で bounded above なので bounded monotone convergence の直接適用。
-/
theorem exists_normalizedEscapeLimit_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    ∃ L : ℝ,
      0 < L ∧
      Tendsto O.normalizedEscapeCoordinate atTop (nhds L) ∧
      ∀ m : ℕ, O.normalizedEscapeCoordinate m ≤ L := by
  let L : ℝ := ⨆ m : ℕ, O.normalizedEscapeCoordinate m
  have hMono := O.normalizedEscapeCoordinate_monotone
  have hBdd := O.normalizedEscapeCoordinate_bddAbove_of_linearDefect S hLinear
  have hT0 := tendsto_atTop_ciSup hMono hBdd
  have hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L) := by
    simpa [L] using hT0
  have hLe0 : O.normalizedEscapeCoordinate 0 ≤ L :=
    hMono.ge_of_tendsto hT 0
  have hLPos : 0 < L :=
    lt_of_lt_of_le (O.normalizedEscapeCoordinate_pos 0) hLe0
  refine ⟨L, hLPos, hT, ?_⟩
  intro m
  exact hMono.ge_of_tendsto hT m

/--
normalized escape limit は初期 normalized coordinate より strict に大きい。

最初の increment が正であることを使う。
-/
theorem normalizedEscapeLimit_start_lt
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    (O.value 0 : ℝ) < L := by
  have hMono := O.normalizedEscapeCoordinate_monotone
  have hOneLe : O.normalizedEscapeCoordinate 1 ≤ L :=
    hMono.ge_of_tendsto hT 1
  have hRise :
      O.normalizedEscapeCoordinate 0 < O.normalizedEscapeCoordinate 1 :=
    O.normalizedEscapeCoordinate_strictMono (by omega)
  rw [O.normalizedEscapeCoordinate_zero] at hRise
  exact lt_of_lt_of_le hRise hOneLe

/--
極限 `L>0` に対して `R_m/L → 1`。

これは

`value(m) ~ L * 3^m / 2^D_m`

という A 型 actual orbit の normalized asymptotic law そのもの。
-/
theorem normalizedEscapeCoordinate_div_limit_tendsto_one
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hL : 0 < L)
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto (fun m : ℕ => O.normalizedEscapeCoordinate m / L)
      atTop (nhds 1) := by
  have h := hT.div_const L
  simpa [hL.ne'] using h

/--
finite normalized translation sum

`Σ_{k<m} 2^D_k / 3^(k+1)`

は `L - x_0` へ収束する。
-/
theorem normalizedEscapeIncrement_partialSum_tendsto
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun m : ℕ =>
        ∑ k ∈ Finset.range m, O.normalizedEscapeIncrement k)
      atTop
      (nhds (L - (O.value 0 : ℝ))) := by
  have hFun :
      (fun m : ℕ =>
        ∑ k ∈ Finset.range m, O.normalizedEscapeIncrement k) =
      (fun m : ℕ => O.normalizedEscapeCoordinate m - (O.value 0 : ℝ)) := by
    funext m
    have hEq := O.normalizedEscapeCoordinate_eq_start_add_sum m
    linarith
  rw [hFun]
  exact hT.sub_const (O.value 0 : ℝ)

/--
finite prefix affine translation の normalized ratio も同じ `L-x_0` へ収束する。
-/
theorem affineConst_div_threePow_tendsto_normalizedEscapeLimit_sub_start
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun m : ℕ =>
        (Word.affineConst (O.segmentWord 0 m) : ℝ) / (3 : ℝ) ^ m)
      atTop
      (nhds (L - (O.value 0 : ℝ))) := by
  have hFun :
      (fun m : ℕ =>
        (Word.affineConst (O.segmentWord 0 m) : ℝ) / (3 : ℝ) ^ m) =
      (fun m : ℕ => O.normalizedEscapeCoordinate m - (O.value 0 : ℝ)) := by
    funext m
    have hEq := O.normalizedEscapeCoordinate_eq_start_add_affineConst_div m
    linarith
  rw [hFun]
  exact hT.sub_const (O.value 0 : ℝ)

/--
Stage 3 のまとめ。

linear defect survivor には有限正の real escape constant `L` が存在し、

* `R_m → L`,
* `R_m/L → 1`,
* normalized affine translation は `L-x_0 > 0` へ収束,
* 同じ finite affine numerator は各 depth で `2^D_m` により割り切れる,

が同時に成り立つ。

最後の divisibility が後続の natural 2-adic stabilization との接続点である。
ここではまだ両 completion の矛盾は主張しない。
-/
theorem exists_realEscapeLimit_with_finite_twoAdicCompatibility_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    ∃ L : ℝ,
      0 < L ∧
      (O.value 0 : ℝ) < L ∧
      Tendsto O.normalizedEscapeCoordinate atTop (nhds L) ∧
      Tendsto (fun m : ℕ => O.normalizedEscapeCoordinate m / L)
        atTop (nhds 1) ∧
      Tendsto
        (fun m : ℕ =>
          (Word.affineConst (O.segmentWord 0 m) : ℝ) / (3 : ℝ) ^ m)
        atTop
        (nhds (L - (O.value 0 : ℝ))) ∧
      (∀ m : ℕ,
        2 ^ infinitePrefixDepth O.exponent m ∣
          3 ^ m * O.value 0 + Word.affineConst (O.segmentWord 0 m)) := by
  rcases O.exists_normalizedEscapeLimit_of_linearDefect S hLinear with
    ⟨L, hL, hT, _hUpper⟩
  have hStart := O.normalizedEscapeLimit_start_lt hT
  have hRatio := O.normalizedEscapeCoordinate_div_limit_tendsto_one hL hT
  have hAffine :=
    O.affineConst_div_threePow_tendsto_normalizedEscapeLimit_sub_start hT
  refine ⟨L, hL, hStart, hT, hRatio, hAffine, ?_⟩
  intro m
  exact O.twoPow_prefixDepth_dvd_affineNumerator m

end OddOrbit
end Collatz3
