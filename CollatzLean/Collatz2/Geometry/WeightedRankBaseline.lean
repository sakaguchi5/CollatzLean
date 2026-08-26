import CollatzLean.Collatz2.Geometry.WeightedRankFerrers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Collatz2 Geometry: primitive baseline geometric sum

primitive FirstCrossing では proper rank residues が `1,...,p-1` の permutation をなし、
`k=0` の residue は 0 である。従って cut-indexed baseline

  baselineResidueSum = sum_k v^(rankResidue(k))

は exact に

  1 + v + ... + v^(p-1)

となる。

ここで `v = u⁻¹`、`half = v^p` なので

  (v-1) * baselineResidueSum = half - 1

も exact に得る。
-/

namespace Collatz2
namespace Word

/-- rank unit inverse の underlying value。 -/
def inverseUnitValue
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  (↑(R.unit⁻¹) : ZMod (terminalGap w))

@[simp] theorem baseResidueWeight_eq_inverseUnitValue_pow
    {w : Word}
    (R : RankUnitData w)
    (k : ℕ) :
    baseResidueWeight R k = inverseUnitValue R ^ rankResidue w k := by
  rfl

@[simp] theorem halfUnitValue_eq_inverseUnitValue_pow
    {w : Word}
    (R : RankUnitData w) :
    halfUnitValue R = inverseUnitValue R ^ oddSteps w := by
  rfl

/-- primitive slope の proper cut は residue 0 を取らない。 -/
theorem FirstCrossing.rankResidue_ne_zero_of_coprime
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    rankResidue w k ≠ 0 := by
  intro hzero
  let p := oddSteps w
  let H := twoSteps w
  have hpPos : 0 < p := by
    dsimp [p, oddSteps]
    exact List.length_pos_iff.mpr hF.nonempty
  have : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  have hResid :=
    hF.rankResidue_cast_eq_twoSteps_mul (by simpa [p] using hkLt)
  have hMulZero : (((H * k : ℕ) : ZMod p)) = 0 := by
    have hRankZero :
        (((rankResidue w k : ℕ) : ZMod p)) = 0 := by
      rw [hzero]
      simp
    simpa [p, H] using hResid.symm.trans hRankZero
  let U : (ZMod p)ˣ :=
    ZMod.unitOfCoprime H (by simpa [p, H] using hcop)
  have hHU :
      ((H : ℕ) : ZMod p) = (↑U : ZMod p) := by
    simp [U]
  have hUk :
      (↑U : ZMod p) * ((k : ℕ) : ZMod p) = 0 := by
    simpa [Nat.cast_mul, hHU] using hMulZero
  have hCancel :=
    congrArg
      (fun z : ZMod p => (↑(U⁻¹) : ZMod p) * z)
      hUk
  have hkZero : ((k : ℕ) : ZMod p) = 0 := by
    simpa [← mul_assoc] using hCancel
  have hVal := congrArg ZMod.val hkZero
  have hkEq : k = 0 := by
    simpa [ZMod.val_natCast,
      Nat.mod_eq_of_lt (by simpa [p] using hkLt), p] using hVal
  omega

/-- primitive slope では `0,...,p-1` 全体で rank residue map が injective。 -/
theorem FirstCrossing.rankResidue_injective_on_range_of_coprime
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k l : ℕ}
    (hkLt : k < oddSteps w)
    (hlLt : l < oddSteps w)
    (hEq : rankResidue w k = rankResidue w l) :
    k = l := by
  by_cases hk0 : k = 0
  · subst k
    by_cases hl0 : l = 0
    · exact hl0.symm
    · have hlPos : 0 < l := Nat.pos_of_ne_zero hl0
      have hLZero : rankResidue w l = 0 := by
        simpa using hEq.symm
      exact False.elim
        ((hF.rankResidue_ne_zero_of_coprime hcop hlPos hlLt) hLZero)
  · by_cases hl0 : l = 0
    · subst l
      have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      have hKZero : rankResidue w k = 0 := by
        simpa using hEq
      exact False.elim
        ((hF.rankResidue_ne_zero_of_coprime hcop hkPos hkLt) hKZero)
    · exact
        hF.rankResidue_injective_of_coprime
          hcop
          (Nat.pos_of_ne_zero hk0) hkLt
          (Nat.pos_of_ne_zero hl0) hlLt
          hEq

/-- primitive slope では rank residues の image は exact に `range p`。 -/
theorem FirstCrossing.image_rankResidue_range_eq_range
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    (Finset.range (oddSteps w)).image (rankResidue w) =
      Finset.range (oddSteps w) := by
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hF.nonempty
  ext r
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨k, hkMem, rfl⟩
    exact Finset.mem_range.mpr hF.rankResidue_lt_oddSteps
  · intro hr
    have hrLt := Finset.mem_range.mp hr
    by_cases hr0 : r = 0
    · subst r
      refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
      · exact Finset.mem_range.mpr hpPos
      · simp
    · have hrPos : 0 < r := Nat.pos_of_ne_zero hr0
      obtain ⟨k, hkSpec, hkUnique⟩ :=
        hF.exists_unique_proper_cut_of_rankResidue hcop hrPos hrLt
      rcases hkSpec with ⟨hkPos, hkLt, hkEq⟩
      exact Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr hkLt, hkEq⟩

/-- primitive baseline を residue 順に並べ直した geometric sum。 -/
def geometricResidueSum
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun r => inverseUnitValue R ^ r)

/--
1. primitive baseline は exact に `1 + v + ... + v^(p-1)`。
-/
theorem RankUnitData.baselineResidueSum_eq_geometricResidueSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    baselineResidueSum R = geometricResidueSum R := by
  unfold baselineResidueSum geometricResidueSum
  simp only [baseResidueWeight_eq_inverseUnitValue_pow]
  have hImage := hF.image_rankResidue_range_eq_range hcop
  calc
    Finset.sum (Finset.range (oddSteps w))
        (fun k => inverseUnitValue R ^ rankResidue w k)
        = Finset.sum
            ((Finset.range (oddSteps w)).image (rankResidue w))
            (fun r => inverseUnitValue R ^ r) := by
              symm
              apply Finset.sum_image
              intro k hk l hl hEq
              exact hF.rankResidue_injective_on_range_of_coprime
                hcop
                (Finset.mem_range.mp hk)
                (Finset.mem_range.mp hl)
                hEq
    _ = Finset.sum (Finset.range (oddSteps w))
          (fun r => inverseUnitValue R ^ r) := by
            rw [hImage]

private theorem sub_one_mul_sum_range_pow
    {N : ℕ}
    (x : ZMod N)
    (p : ℕ) :
    (x - 1) * Finset.sum (Finset.range p) (fun r => x ^ r) =
      x ^ p - 1 := by
  induction p with
  | zero =>
      simp
  | succ p ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/--
2. primitive baseline の幾何級数 identity。

  (v-1) * baseline = half - 1.
-/
theorem RankUnitData.inverseUnitValue_sub_one_mul_baselineResidueSum_eq_half_sub_one
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    (inverseUnitValue R - 1) * baselineResidueSum R =
      halfUnitValue R - 1 := by
  rw [R.baselineResidueSum_eq_geometricResidueSum hF hcop]
  unfold geometricResidueSum
  rw [sub_one_mul_sum_range_pow]
  rfl

end Word
end Collatz2
