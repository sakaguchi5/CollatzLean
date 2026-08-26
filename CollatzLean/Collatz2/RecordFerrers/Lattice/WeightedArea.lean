import CollatzLean.Collatz2.RecordFerrers.Lattice.FirstCrossingLattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Record–Ferrers Phase A: weighted Ferrers area and affine valuation

`affineConst` を fixed-chord Ferrers shape の weighted area として読み直す。
meet / join に対する valuation identity も shape level で exact に証明する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- baseline exponent `1,1,...` に対応する cut weight。 -/
def baseAffineTerm (p k : ℕ) : ℕ :=
  2 ^ k * 3 ^ (p - (k + 1))

/-- column excess `y` が baseline に追加する exact weight。 -/
def excessAffineWeight (p k y : ℕ) : ℕ :=
  (2 ^ (k + y) - 2 ^ k) * 3 ^ (p - (k + 1))

/-- Ferrers shape 全体の weighted area。 -/
def weightedArea
    {p : ℕ}
    (S : FerrersShape p) : ℕ :=
  Finset.sum (Finset.range p)
    (fun k => excessAffineWeight p k (S.atNat k))

/-- baseline affine budget。 -/
def baseAffineConst (p : ℕ) : ℕ :=
  Finset.sum (Finset.range p) (fun k => baseAffineTerm p k)

/-- min/max は一つの column weight の二項和を保存する。 -/
theorem excessAffineWeight_min_add_max
    (p k a b : ℕ) :
    excessAffineWeight p k (min a b) +
        excessAffineWeight p k (max a b) =
      excessAffineWeight p k a + excessAffineWeight p k b := by
  by_cases hab : a ≤ b
  · simp [min_eq_left hab, max_eq_right hab]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [min_eq_right hba, max_eq_left hba, add_comm]

/-- weighted area は Ferrers meet/join に対する valuation。 -/
theorem weightedArea_meet_add_join
    {p : ℕ}
    (A B : FerrersShape p) :
    weightedArea (FerrersShape.meet A B) +
        weightedArea (FerrersShape.join A B) =
      weightedArea A + weightedArea B := by
  unfold weightedArea
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [FerrersShape.atNat_meet, FerrersShape.atNat_join]
  exact excessAffineWeight_min_add_max p k (A.atNat k) (B.atNat k)

/-- 一つの actual affine path term = baseline + Ferrers excess。 -/
theorem affinePathTerm_eq_base_add_excess
    {p H : ℕ}
    (x : FiberPoint p H)
    {k : ℕ}
    (hk : k < p) :
    affinePathTerm x.word k =
      baseAffineTerm p k +
        excessAffineWeight p k (x.toFerrersShape.atNat k) := by
  have hIndex := x.index_le_height (Nat.le_of_lt hk)
  have hHeight := x.height_eq_index_add_excess (Nat.le_of_lt hk)
  have hAt := x.toFerrersShape_atNat hk
  have hPowLe : 2 ^ k ≤ 2 ^ x.height k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hIndex
  have hSplit :
      2 ^ x.height k = 2 ^ k + (2 ^ x.height k - 2 ^ k) := by
    have h := Nat.sub_add_cancel hPowLe
    omega
  unfold affinePathTerm baseAffineTerm excessAffineWeight
  rw [x.oddSteps_eq, hAt, ← hHeight]
  change
    2 ^ x.height k * 3 ^ (p - (k + 1)) =
      2 ^ k * 3 ^ (p - (k + 1)) +
        (2 ^ x.height k - 2 ^ k) * 3 ^ (p - (k + 1))
  rw [hSplit]
  ring_nf
  simp

/--
fixed-chord word の genuine affine translation は
baseline + Ferrers weighted area に exact 分解する。
-/
theorem affineConst_eq_base_add_weightedArea
    {p H : ℕ}
    (x : FiberPoint p H) :
    affineConst x.word =
      baseAffineConst p + weightedArea x.toFerrersShape := by
  rw [← affinePathSum_eq_affineConst]
  unfold affinePathSum baseAffineConst weightedArea
  rw [x.oddSteps_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact affinePathTerm_eq_base_add_excess x (Finset.mem_range.mp hk)

/-- critical roof 自身の affine budget も同じ weighted-area 形を持つ。 -/
theorem criticalAffineConst_eq_base_add_weightedArea
    (p : ℕ) :
    criticalAffineConst p =
      baseAffineConst p + weightedArea (criticalShape p) := by
  unfold criticalAffineConst baseAffineConst weightedArea
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hkMem
  have hk : k < p := Finset.mem_range.mp hkMem
  have hIndex := index_le_criticalHeight k
  have hEq : criticalHeight k = k + criticalExcess k := by
    unfold criticalExcess
    omega
  have hPowLe : 2 ^ k ≤ 2 ^ criticalHeight k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hIndex
  have hSplit :
      2 ^ criticalHeight k =
        2 ^ k + (2 ^ criticalHeight k - 2 ^ k) := by
    have h := Nat.sub_add_cancel hPowLe
    omega
  unfold criticalAffineTerm baseAffineTerm excessAffineWeight
  have hAt : (criticalShape p).atNat k = criticalExcess k := by
    simp [FerrersShape.atNat, hk, criticalShape]
  rw [hAt, ← hEq]
  change
    2 ^ criticalHeight k * 3 ^ (p - (k + 1)) =
      2 ^ k * 3 ^ (p - (k + 1)) +
        (2 ^ criticalHeight k - 2 ^ k) * 3 ^ (p - (k + 1))
  rw [hSplit]
  ring_nf
  simp

/-- critical subshape では weighted area は critical weighted area 以下。 -/
theorem weightedArea_le_critical
    {p : ℕ}
    {S : FerrersShape p}
    (hS : IsCriticalSubshape S) :
    weightedArea S ≤ weightedArea (criticalShape p) := by
  unfold weightedArea
  apply Finset.sum_le_sum
  intro k hkMem
  have hk : k < p := Finset.mem_range.mp hkMem
  have hcol : S.atNat k ≤ (criticalShape p).atNat k := by
    simp only [FerrersShape.atNat, hk, ↓reduceDIte]
    exact hS ⟨k, hk⟩
  unfold excessAffineWeight
  have hExp : k + S.atNat k ≤ k + (criticalShape p).atNat k :=
    Nat.add_le_add_left hcol k
  have hPow :
      2 ^ (k + S.atNat k) ≤ 2 ^ (k + (criticalShape p).atNat k) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExp
  have hSub :
      2 ^ (k + S.atNat k) - 2 ^ k ≤
        2 ^ (k + (criticalShape p).atNat k) - 2 ^ k :=
    Nat.sub_le_sub_right hPow (2 ^ k)
  exact Nat.mul_le_mul_right _ hSub

/-- FirstCrossing word の affineConst upper bound を weighted-area inclusion から再取得。 -/
theorem affineConst_le_criticalAffineConst_of_shape
    {p H : ℕ}
    (x : FiberPoint p H)
    (hShape : IsCriticalSubshape x.toFerrersShape) :
    affineConst x.word ≤ criticalAffineConst p := by
  rw [affineConst_eq_base_add_weightedArea x,
      criticalAffineConst_eq_base_add_weightedArea p]
  exact Nat.add_le_add_left (weightedArea_le_critical hShape) _

/-- exact FiberShape decoder 上で affineConst = baseline + weighted area。 -/
theorem affineConst_toFiberPoint_eq_base_add_weightedArea
    {p H : ℕ}
    (S : FiberShape p H) :
    affineConst S.toFiberPoint.word =
      baseAffineConst p + weightedArea S.shape := by
  have h := affineConst_eq_base_add_weightedArea S.toFiberPoint
  rw [S.toFerrersShape_toFiberPoint] at h
  exact h

/--
fixed-chord Ferrers lattice 上の genuine affine translation valuation。
meet/join で `B(meet)+B(join)=B(A)+B(B)` が exact に成り立つ。
-/
theorem affineConst_fiberMeet_add_fiberJoin
    {p H : ℕ}
    (A B : FiberShape p H) :
    affineConst (FiberShape.meet A B).toFiberPoint.word +
        affineConst (FiberShape.join A B).toFiberPoint.word =
      affineConst A.toFiberPoint.word +
        affineConst B.toFiberPoint.word := by
  rw [affineConst_toFiberPoint_eq_base_add_weightedArea,
      affineConst_toFiberPoint_eq_base_add_weightedArea,
      affineConst_toFiberPoint_eq_base_add_weightedArea,
      affineConst_toFiberPoint_eq_base_add_weightedArea]
  have hVal := weightedArea_meet_add_join A.shape B.shape
  have hVal' :
      weightedArea (FiberShape.meet A B).shape +
          weightedArea (FiberShape.join A B).shape =
        weightedArea A.shape + weightedArea B.shape := by
    simpa [FiberShape.meet, FiberShape.join] using hVal
  omega

end RecordFerrers
end Collatz2
