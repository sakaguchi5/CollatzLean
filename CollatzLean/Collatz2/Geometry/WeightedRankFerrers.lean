import CollatzLean.Collatz2.Geometry.RankQuotient
import CollatzLean.Collatz2.Geometry.WeightedRankSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Collatz2 Geometry: weighted rank の Ferrers decomposition

rank residue / quotient

  d_k = r_k + p*q_k

と rank unit `u` の inverse `v=u⁻¹` を使う。
`u^p=2` なので

  u^(-d_k) = v^r_k * (v^p)^q_k.

ここで

  baseResidueWeight(k) = v^r_k
  halfUnitValue = v^p

と置く。`q_k` は

  stripRank(k)/p + extraDepth(k)

なので、wide strip の deterministic wrap と path sinking を同じ half-depth として扱える。

さらに weighted sum を

  baseline + cell correction

へ exact に分解する。
-/

namespace Collatz2
namespace Word

/-- residue `r_k` が担う baseline unit weight。 -/
def baseResidueWeight
    {w : Word}
    (R : RankUnitData w)
    (k : ℕ) : ZMod (terminalGap w) :=
  (↑(R.unit⁻¹) : ZMod (terminalGap w)) ^ rankResidue w k

/-- `v^p`。rank quotient が一つ増えるごとに掛かる half-unit value。 -/
def halfUnitValue
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  (↑(R.unit⁻¹) : ZMod (terminalGap w)) ^ oddSteps w

namespace RankUnitData

/-- `halfUnitValue` は mod gap で 2 の inverse として振る舞う。 -/
theorem halfUnitValue_mul_two_eq_one
    {w : Word}
    (R : RankUnitData w) :
    halfUnitValue R *
        ((2 : ℕ) : ZMod (terminalGap w)) = 1 := by
  have hTwo := R.unit_pow_oddSteps
  let u : ZMod (terminalGap w) := ↑R.unit
  let v : ZMod (terminalGap w) := ↑(R.unit⁻¹)
  have hvu : v * u = 1 := by
    dsimp [u, v]
    simp
  change v ^ oddSteps w *
      ((2 : ℕ) : ZMod (terminalGap w)) = 1
  rw [← hTwo]
  change v ^ oddSteps w * u ^ oddSteps w = 1
  rw [← mul_pow, hvu]
  simp

/--
Stage 3: each inverse rank weight factors into residue weight and half-depth.
-/
theorem inverseRankWeight_eq_baseResidueWeight_mul_halfUnitValue_pow
    {w : Word}
    (R : RankUnitData w)
    (k : ℕ) :
    inverseRankWeight R k =
      baseResidueWeight R k *
        halfUnitValue R ^ rankQuotient w k := by
  have hDecomp :=
    chordRank_eq_rankResidue_add_oddSteps_mul_rankQuotient w k
  unfold inverseRankWeight baseResidueWeight halfUnitValue
  rw [hDecomp, pow_add, pow_mul]

end RankUnitData

/-- residue/quotient で書いた weighted sum。 -/
def ferrersWeightedSum
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k =>
      baseResidueWeight R k *
        halfUnitValue R ^ rankQuotient w k)

namespace RankUnitData

/-- weighted rank sum は Ferrers residue/quotient form と exact に一致する。 -/
theorem weightedRankSum_eq_ferrersWeightedSum
    {w : Word}
    (R : RankUnitData w) :
    weightedRankSum R = ferrersWeightedSum R := by
  unfold weightedRankSum ferrersWeightedSum
  apply Finset.sum_congr rfl
  intro k hk
  exact R.inverseRankWeight_eq_baseResidueWeight_mul_halfUnitValue_pow k

end RankUnitData

/-- `k=1,...,p-1` の permutation-weighted half-depth sum。 -/
def properPermutationWeightedHalfDepthSum
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w - 1))
    (fun j =>
      baseResidueWeight R (j + 1) *
        halfUnitValue R ^ rankQuotient w (j + 1))

namespace RankUnitData

/--
Stage 4a: `k=0` term を 1 として分離する。

  W = 1 + proper permutation-weighted half-depth sum.
-/
theorem weightedRankSum_eq_one_add_properPermutationWeightedHalfDepthSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w) :
    weightedRankSum R =
      1 + properPermutationWeightedHalfDepthSum R := by
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hF.nonempty
  have hpEq : oddSteps w = (oddSteps w - 1) + 1 := by
    omega
  rw [R.weightedRankSum_eq_ferrersWeightedSum]
  unfold ferrersWeightedSum properPermutationWeightedHalfDepthSum
  rw [hpEq, Finset.sum_range_succ']
  simp [baseResidueWeight, halfUnitValue,add_comm]

end RankUnitData

/-! ## primitive residue permutation -/

/--
primitive exponent slope では rank residue は proper cuts 上で injective。
-/
theorem FirstCrossing.rankResidue_injective_of_coprime
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k l : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w)
    (hlPos : 0 < l)
    (hlLt : l < oddSteps w)
    (hEq : rankResidue w k = rankResidue w l) :
    k = l := by
  apply hF.chordRankResidue_injective hcop hkPos hkLt hlPos hlLt
  calc
    chordRankResidue w k
        = ((rankResidue w k : ℕ) : ZMod (oddSteps w)) :=
          (rankResidue_cast_eq_chordRankResidue k).symm
    _ = ((rankResidue w l : ℕ) : ZMod (oddSteps w)) := by rw [hEq]
    _ = chordRankResidue w l :=
          rankResidue_cast_eq_chordRankResidue l

/--
primitive slope では proper rank residues は exact に `1,...,p-1` を一度ずつ取る。
reduced 性は不要。
-/
theorem FirstCrossing.exists_unique_proper_cut_of_rankResidue
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {q : ℕ}
    (hqPos : 0 < q)
    (hqLt : q < oddSteps w) :
    ∃! k : ℕ,
      0 < k ∧ k < oddSteps w ∧ rankResidue w k = q := by
  let p := oddSteps w
  let H := twoSteps w
  have hpPos : 0 < p := by
    dsimp [p, oddSteps]
    exact List.length_pos_iff.mpr hF.nonempty
  haveI : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  let U : (ZMod p)ˣ :=
    ZMod.unitOfCoprime H (by simpa [p, H] using hcop)
  let z : ZMod p :=
    (↑(U⁻¹) : ZMod p) * ((q : ℕ) : ZMod p)
  let k : ℕ := z.val
  have hkLt : k < p := by
    simpa [k] using ZMod.val_lt z
  have hqCastNe : (((q : ℕ) : ZMod p)) ≠ 0 := by
    intro hq0
    have hVal := congrArg ZMod.val hq0
    have hqEq : q = 0 := by
      simpa [ZMod.val_natCast,
        Nat.mod_eq_of_lt (by simpa [p] using hqLt), p] using hVal
    omega
  have hzNe : z ≠ 0 := by
    intro hz
    have hMul :=
      congrArg
        (fun t : ZMod p => (↑U : ZMod p) * t)
        hz
    have hq0 : (((q : ℕ) : ZMod p)) = 0 := by
      simpa [z, ← mul_assoc] using hMul
    exact hqCastNe hq0
  have hkPos : 0 < k := by
    have hkNe : k ≠ 0 := by
      intro hk0
      apply hzNe
      apply (ZMod.val_eq_zero z).mp
      simpa [k] using hk0
    exact Nat.pos_of_ne_zero hkNe
  have hkCast : ((k : ℕ) : ZMod p) = z := by
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, k]
  have hHU :
      ((H : ℕ) : ZMod p) = (↑U : ZMod p) := by
    simp [U]
  have hHk :
      (((H * k : ℕ) : ZMod p)) = ((q : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, hHU, hkCast]
    simp [z, ← mul_assoc]
  have hResid :=
    hF.rankResidue_cast_eq_twoSteps_mul (by simpa [p] using hkLt)
  have hRankCast :
      ((rankResidue w k : ℕ) : ZMod p) = ((q : ℕ) : ZMod p) := by
    simpa [p, H] using hResid.trans hHk
  have hRankLt : rankResidue w k < p := by
    unfold rankResidue
    exact Nat.mod_lt _ hpPos
  have hVal := congrArg ZMod.val hRankCast
  have hRankEq : rankResidue w k = q := by
    simpa [ZMod.val_natCast,
      Nat.mod_eq_of_lt hRankLt,
      Nat.mod_eq_of_lt (by simpa [p] using hqLt), p] using hVal
  refine ⟨k, ?_, ?_⟩
  · exact ⟨hkPos, by simpa [p] using hkLt, hRankEq⟩
  · intro s hs
    rcases hs with ⟨hsPos, hsLt, hsEq⟩
    symm
    apply hF.rankResidue_injective_of_coprime
      hcop hkPos (by simpa [p] using hkLt) hsPos hsLt
    exact hRankEq.trans hsEq.symm

/-! ## baseline + Ferrers cell correction -/

/-- residue permutation だけを残した baseline sum。 -/
def baselineResidueSum
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k => baseResidueWeight R k)

/-- 一つの quotient column に対応する geometric cell sum。 -/
def halfCellColumnSum
    {w : Word}
    (R : RankUnitData w)
    (q : ℕ) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range q)
    (fun j => halfUnitValue R ^ j)

/-- baseline から実際の half-depth weight への差。 -/
def ferrersCellCorrection
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k =>
      baseResidueWeight R k *
        (halfUnitValue R ^ rankQuotient w k - 1))

/-- factor `(half-1)` を外した Ferrers cell sum。 -/
def ferrersCellSum
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k =>
      baseResidueWeight R k *
        halfCellColumnSum R (rankQuotient w k))

private theorem pow_eq_one_add_sub_one_mul_halfCellColumnSum
    {N : ℕ}
    (x : ZMod N)
    (q : ℕ) :
    x ^ q =
      1 + (x - 1) *
        Finset.sum (Finset.range q) (fun j => x ^ j) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [pow_succ, Finset.sum_range_succ, ih]
      ring

/-- Ferrers weighted sum は baseline + exact correction。 -/
theorem ferrersWeightedSum_eq_baseline_add_cellCorrection
    {w : Word}
    (R : RankUnitData w) :
    ferrersWeightedSum R =
      baselineResidueSum R + ferrersCellCorrection R := by
  unfold ferrersWeightedSum baselineResidueSum ferrersCellCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- cell correction は `(half-1)` と Ferrers cell sum の積。 -/
theorem ferrersCellCorrection_eq_halfSubOne_mul_ferrersCellSum
    {w : Word}
    (R : RankUnitData w) :
    ferrersCellCorrection R =
      (halfUnitValue R - 1) * ferrersCellSum R := by
  unfold ferrersCellCorrection ferrersCellSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hPow :=
    pow_eq_one_add_sub_one_mul_halfCellColumnSum
      (halfUnitValue R) (rankQuotient w k)
  unfold halfCellColumnSum
  rw [hPow]
  ring

namespace RankUnitData

/--
Stage 4b: weighted sum の exact baseline + Ferrers-cell form。
-/
theorem weightedRankSum_eq_baseline_add_halfSubOne_mul_ferrersCellSum
    {w : Word}
    (R : RankUnitData w) :
    weightedRankSum R =
      baselineResidueSum R +
        (halfUnitValue R - 1) * ferrersCellSum R := by
  calc
    weightedRankSum R = ferrersWeightedSum R :=
      R.weightedRankSum_eq_ferrersWeightedSum
    _ = baselineResidueSum R + ferrersCellCorrection R :=
      ferrersWeightedSum_eq_baseline_add_cellCorrection R
    _ = baselineResidueSum R +
          (halfUnitValue R - 1) * ferrersCellSum R := by
          rw [ferrersCellCorrection_eq_halfSubOne_mul_ferrersCellSum]

end RankUnitData
end Word
end Collatz2
