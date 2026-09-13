import CollatzLean.Collatz3.Bridge.CriticalSurvivorDecay
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.FieldSimp

/-!
# Collatz3 Bridge: first-crossing Kraft 無限和と actual-start density の exact 値

前ファイルまでで、depth `n` の first-crossing mass と survivor mass に対して

`crossing mass through depth N + survivor mass = 1/2`

という有限 Kraft 恒等式を得た。また survivor mass は 0 へ収束する。
したがって physical depth で足し上げた first-crossing mass の総和は正確に `1/2` である。

次に critical terminal depth

`H_m = criticalTwoDepth m`

は `m` に関して strict mono であり、generic first crossing は必ずただ一つの `H_m` に現れる。
そこで正の order `m = j+1` を

`j ↦ H_(j+1) - 2`

で physical-depth series `n ↦ firstCrossingParityMass (n+2)` の添字へ埋め込む。
像の外では first-crossing code が存在しないため項は 0 である。
mathlib の injective reindexing theorem を使うと、

`sum_{m>=1} N_m / 2^H_m = 1/2`

が exact に従う。

さらに actual critical start の一つの residue fiber は modulus

`M_m = 2^(H_m+1)`

を持つので、その fixed-width density mass は `N_m/M_m`。
これは Kraft mass のちょうど半分であり、全 order の和は

`sum_{m>=1} N_m / M_m = 1/4`

となる。

ここで証明しているのは first-crossing start residue の密度恒等式であり、
Collatz 予想の収束そのものを仮定も結論もしない。
-/

namespace Collatz3
namespace Bridge

open scoped BigOperators
open scoped Topology
open Filter

/-- physical depth `2,3,...` を `0,1,...` から読む first-crossing mass series。 -/
noncomputable def firstCrossingDepthMassSeq (n : ℕ) : ℝ :=
  firstCrossingParityMass (n + 2)

/-- physical-depth first-crossing mass の各項は非負。 -/
theorem firstCrossingDepthMassSeq_nonneg
    (n : ℕ) :
    0 ≤ firstCrossingDepthMassSeq n := by
  unfold firstCrossingDepthMassSeq firstCrossingParityMass
  positivity

/-- finite Kraft 恒等式と survivor decay から、physical-depth partial sums は `1/2` へ行く。 -/
theorem tendsto_firstCrossingParityMassPartial_half :
    Tendsto firstCrossingParityMassPartial atTop (𝓝 ((1 : ℝ) / 2)) := by
  have h :=
    (tendsto_const_nhds.sub tendsto_survivorParityRatio_zero :
      Tendsto
        (fun N : ℕ => (1 : ℝ) / 2 - survivorParityRatio (N + 1))
        atTop
        (𝓝 ((1 : ℝ) / 2 - 0)))
  have h' :
      Tendsto
        (fun N : ℕ => (1 : ℝ) / 2 - survivorParityRatio (N + 1))
        atTop
        (𝓝 ((1 : ℝ) / 2)) := by
    simpa using h
  apply h'.congr'
  exact Filter.Eventually.of_forall fun N => by
    have hKraft := firstCrossingParityMassPartial_add_survivor N
    linarith

/--
physical depth `2,3,...` で読んだ有限和は、
既存の first-crossing partial mass と一致する。
-/
theorem firstCrossingDepthMassSeq_partialSum
    (n : ℕ) :
    (∑ i ∈ Finset.range n, firstCrossingDepthMassSeq i) =
      firstCrossingParityMassPartial n := by
  unfold firstCrossingDepthMassSeq
  -- ここで firstCrossingParityMassPartial の定義だけを展開する。
  unfold firstCrossingParityMassPartial
  rfl

/-- physical depth で見た first-crossing mass の `HasSum` は正確に `1/2`。 -/
theorem hasSum_firstCrossingDepthMassSeq :
    HasSum firstCrossingDepthMassSeq ((1 : ℝ) / 2) := by
  apply
    (hasSum_iff_tendsto_nat_of_nonneg
      firstCrossingDepthMassSeq_nonneg
      ((1 : ℝ) / 2)).2
  have hEq :
      (fun n : ℕ =>
        ∑ i ∈ Finset.range n, firstCrossingDepthMassSeq i)
        =
      firstCrossingParityMassPartial := by
    funext n
    exact firstCrossingDepthMassSeq_partialSum n
  rw [hEq]
  exact tendsto_firstCrossingParityMassPartial_half

/-- physical depth での exact infinite Kraft equality。 -/
theorem tsum_firstCrossingDepthMassSeq :
    (∑' n : ℕ, firstCrossingDepthMassSeq n) = (1 : ℝ) / 2 :=
  hasSum_firstCrossingDepthMassSeq.tsum_eq

/-- positive order `j+1` の critical depth を physical series の zero-based index に直す。 -/
def criticalDepthIndex (j : ℕ) : ℕ :=
  Critical.criticalTwoDepth (j + 1) - 2

/-- positive order の critical terminal depth は少なくとも `2`。 -/
theorem two_le_criticalTwoDepth_succ
    (j : ℕ) :
    2 ≤ Critical.criticalTwoDepth (j + 1) := by
  have h :
      Critical.criticalTwoDepth 0 <
        Critical.criticalTwoDepth (j + 1) :=
    criticalTwoDepth_strictMono (Nat.zero_lt_succ j)
  have hZero : Critical.criticalTwoDepth 0 = 1 := by
    simp [Critical.criticalTwoDepth]
  rw [hZero] at h
  omega

/-- `criticalDepthIndex` へ 2 を戻すと元の critical depth になる。 -/
@[simp] theorem criticalDepthIndex_add_two
    (j : ℕ) :
    criticalDepthIndex j + 2 = Critical.criticalTwoDepth (j + 1) := by
  unfold criticalDepthIndex
  exact Nat.sub_add_cancel (two_le_criticalTwoDepth_succ j)

/-- positive order から physical-depth index への写像は単射。 -/
theorem criticalDepthIndex_injective :
    Function.Injective criticalDepthIndex := by
  intro i j hij
  have hDepth :
      Critical.criticalTwoDepth (i + 1) =
        Critical.criticalTwoDepth (j + 1) := by
    calc
      Critical.criticalTwoDepth (i + 1) = criticalDepthIndex i + 2 := by
        symm
        exact criticalDepthIndex_add_two i
      _ = criticalDepthIndex j + 2 := by rw [hij]
      _ = Critical.criticalTwoDepth (j + 1) := criticalDepthIndex_add_two j
  have hOrder : i + 1 = j + 1 := criticalTwoDepth_injective hDepth
  omega

/-- positive order `m=j+1` の Kraft mass `N_m / 2^H_m`。 -/
noncomputable def criticalPartitionKraftMass (j : ℕ) : ℝ :=
  (criticalPartitionCount (j + 1) : ℝ) /
    (2 ^ Critical.criticalTwoDepth (j + 1) : ℝ)

/-- critical-depth image 上では physical-depth mass は partition Kraft mass と一致する。 -/
theorem firstCrossingDepthMassSeq_criticalDepthIndex
    (j : ℕ) :
    firstCrossingDepthMassSeq (criticalDepthIndex j) =
      criticalPartitionKraftMass j := by
  unfold firstCrossingDepthMassSeq criticalPartitionKraftMass
  rw [criticalDepthIndex_add_two]
  exact firstCrossingParityMass_criticalDepth (by omega)

/--
critical-depth image の外では generic first-crossing code は存在せず、mass は 0。
-/
theorem firstCrossingDepthMassSeq_eq_zero_of_not_range
    {n : ℕ}
    (hn : n ∉ Set.range criticalDepthIndex) :
    firstCrossingDepthMassSeq n = 0 := by
  have hEmpty : IsEmpty (FirstCrossingParityCode (n + 2)) := by
    constructor
    intro C
    have hm : 0 < C.1.length :=
      parityComposition_length_pos (by omega) C.1
    have hDepth := C.2.criticalTwoDepth_eq
    have hPred : C.1.length - 1 + 1 = C.1.length := by
      omega
    have hIdx : criticalDepthIndex (C.1.length - 1) = n := by
      unfold criticalDepthIndex
      rw [hPred, ← hDepth]
      omega
    exact hn ⟨C.1.length - 1, hIdx⟩
  have hCard : firstCrossingParityCount (n + 2) = 0 := by
    unfold firstCrossingParityCount
    exact Finite.card_eq_zero_iff.mpr hEmpty
  unfold firstCrossingDepthMassSeq firstCrossingParityMass
  rw [hCard]
  simp

/--
physical-depth series を strict critical-depth image へ reindex した `HasSum`。
像の外が 0 なので総和は変わらない。
-/
theorem hasSum_firstCrossingDepthMassSeq_comp_criticalDepthIndex :
    HasSum
      (firstCrossingDepthMassSeq ∘ criticalDepthIndex)
      ((1 : ℝ) / 2) := by
  rw [criticalDepthIndex_injective.hasSum_iff
    (fun n hn => firstCrossingDepthMassSeq_eq_zero_of_not_range hn)]
  exact hasSum_firstCrossingDepthMassSeq

/--
restricted partition count の exact infinite Kraft equality。

`m=1,2,...` を `j=0,1,...` として読む。
-/
theorem hasSum_criticalPartitionKraftMass :
    HasSum criticalPartitionKraftMass ((1 : ℝ) / 2) := by
  exact
    HasSum.congr_fun
      hasSum_firstCrossingDepthMassSeq_comp_criticalDepthIndex
      (fun j => by
        simpa [Function.comp_apply] using
          (firstCrossingDepthMassSeq_criticalDepthIndex j).symm)

/-- `sum_{m>=1} N_m / 2^H_m = 1/2` の `tsum` 形。 -/
theorem tsum_criticalPartitionKraftMass :
    (∑' j : ℕ, criticalPartitionKraftMass j) = (1 : ℝ) / 2 :=
  hasSum_criticalPartitionKraftMass.tsum_eq

/-- `m=1,2,...` を `j+1` で直接書いた exact Kraft equality。 -/
theorem tsum_criticalPartitionCount_div_twoPow :
    (∑' j : ℕ,
      (criticalPartitionCount (j + 1) : ℝ) /
        (2 ^ Critical.criticalTwoDepth (j + 1) : ℝ)) =
      (1 : ℝ) / 2 := by
  simpa [criticalPartitionKraftMass] using tsum_criticalPartitionKraftMass

/-- 正の order `m=j+1` の actual critical-start residue density mass。 -/
noncomputable def criticalActualStartDensityMass (j : ℕ) : ℝ :=
  (criticalPartitionCount (j + 1) : ℝ) /
    (criticalStartModulus (j + 1) : ℝ)

/-- modulus は Kraft denominator よりちょうど 2 倍大きい。 -/
theorem criticalActualStartDensityMass_eq_half_mul_kraft
    (j : ℕ) :
    criticalActualStartDensityMass j =
      ((1 : ℝ) / 2) * criticalPartitionKraftMass j := by
  unfold criticalActualStartDensityMass criticalPartitionKraftMass criticalStartModulus
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_succ]
  have hpow : (2 ^ Critical.criticalTwoDepth (j + 1) : ℝ) ≠ 0 := by
    positivity
  field_simp [hpow]

/-- actual-start density mass series の exact `HasSum` は `1/4`。 -/
theorem hasSum_criticalActualStartDensityMass :
    HasSum criticalActualStartDensityMass ((1 : ℝ) / 4) := by
  have h := hasSum_criticalPartitionKraftMass.mul_left ((1 : ℝ) / 2)
  have hValue : ((1 : ℝ) / 2) * ((1 : ℝ) / 2) = (1 : ℝ) / 4 := by
    norm_num
  rw [hValue] at h
  exact
    HasSum.congr_fun h
      (fun j => criticalActualStartDensityMass_eq_half_mul_kraft j)

/-- `sum_{m>=1} N_m / M_m = 1/4` の `tsum` 形。 -/
theorem tsum_criticalActualStartDensityMass :
    (∑' j : ℕ, criticalActualStartDensityMass j) = (1 : ℝ) / 4 :=
  hasSum_criticalActualStartDensityMass.tsum_eq

/-- `m=1,2,...` の fixed-width actual-start density mass を直接書いた exact equality。 -/
theorem tsum_criticalPartitionCount_div_startModulus :
    (∑' j : ℕ,
      (criticalPartitionCount (j + 1) : ℝ) /
        (criticalStartModulus (j + 1) : ℝ)) =
      (1 : ℝ) / 4 := by
  simpa [criticalActualStartDensityMass] using
    tsum_criticalActualStartDensityMass

/--
添字 `m=1,2,...` を明示した読み方。
`criticalPartitionKraftMass (m-1)` は `N_m / 2^H_m`、
`criticalActualStartDensityMass (m-1)` は `N_m / M_m` である。
-/
theorem criticalPartitionKraftMass_pred
    {m : ℕ}
    (hm : 0 < m) :
    criticalPartitionKraftMass (m - 1) =
      (criticalPartitionCount m : ℝ) /
        (2 ^ Critical.criticalTwoDepth m : ℝ) := by
  unfold criticalPartitionKraftMass
  have hPred : m - 1 + 1 = m := by omega
  rw [hPred]

/-- actual-start density mass の同じ positive-order 読み。 -/
theorem criticalActualStartDensityMass_pred
    {m : ℕ}
    (hm : 0 < m) :
    criticalActualStartDensityMass (m - 1) =
      (criticalPartitionCount m : ℝ) /
        (criticalStartModulus m : ℝ) := by
  unfold criticalActualStartDensityMass
  have hPred : m - 1 + 1 = m := by omega
  rw [hPred]

end Bridge
end Collatz3
