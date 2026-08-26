import CollatzLean.Collatz2.RecordFerrers.Lattice.MetricCompletion

/-!
# Record–Ferrers RF-A+4: weighted potential theory

`affineConst = baseAffineConst + weightedArea` を、単なる表示公式から
order-preserving / injective potential へ強化する。

* column weight の monotonicity と one-cell increment
* weightedArea の fixed-fiber injectivity
* affineConst の strict monotonicity
* baseline `baseAffineConst p = 3^p - 2^p`
* fixed fiber / FirstCrossing の extremal bounds
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 一つの Ferrers column weight は column height に単調。 -/
theorem excessAffineWeight_mono
    (p k : ℕ)
    {a b : ℕ}
    (hab : a ≤ b) :
    excessAffineWeight p k a ≤ excessAffineWeight p k b := by
  unfold excessAffineWeight
  have hExp : k + a ≤ k + b := Nat.add_le_add_left hab k
  have hPow : 2 ^ (k + a) ≤ 2 ^ (k + b) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExp
  have hSub :
      2 ^ (k + a) - 2 ^ k ≤
        2 ^ (k + b) - 2 ^ k :=
    Nat.sub_le_sub_right hPow (2 ^ k)
  exact Nat.mul_le_mul_right _ hSub

/--
column を一 cell 上げたときの exact weight increment。
追加 cell の重みは `2^(k+y) * 3^(p-k-1)`。
-/
theorem excessAffineWeight_succ
    (p k y : ℕ) :
    excessAffineWeight p k (y + 1) =
      excessAffineWeight p k y +
        2 ^ (k + y) * 3 ^ (p - (k + 1)) := by
  have hBase : 2 ^ k ≤ 2 ^ (k + y) := by
    apply Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
    omega
  have hPow :
      2 ^ (k + (y + 1)) =
        2 ^ (k + y) + 2 ^ (k + y) := by
    have hIdx : k + (y + 1) = (k + y) + 1 := by
      omega
    rw [hIdx, pow_succ]
    ring
  have hCancel :
      (2 ^ (k + y) - 2 ^ k) + 2 ^ k =
        2 ^ (k + y) := by
    exact Nat.sub_add_cancel hBase
  have hSub :
      2 ^ (k + (y + 1)) - 2 ^ k =
        (2 ^ (k + y) - 2 ^ k) + 2 ^ (k + y) := by
    rw [hPow]
    rw [Nat.add_sub_assoc hBase]
    ac_rfl
  unfold excessAffineWeight
  rw [hSub]
  ring

/-- Ferrers inclusion は weighted area を単調にする。 -/
theorem weightedArea_mono
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B) :
    weightedArea A ≤ weightedArea B := by
  unfold weightedArea
  apply Finset.sum_le_sum
  intro k hkMem
  have hk : k < p := Finset.mem_range.mp hkMem
  have hCol : A.atNat k ≤ B.atNat k := by
    simpa [FerrersShape.atNat, hk] using hAB ⟨k, hk⟩
  exact excessAffineWeight_mono p k hCol

namespace FiberShape

/--
fixed `(p,H)` fiber では weighted area 一個が Ferrers shape を一意に決める。
`affineConst` の lossless 性と exact weighted-area formula の合成。
-/
theorem weightedArea_injective
    {p H : ℕ}
    {A B : FiberShape p H}
    (hArea : weightedArea A.shape = weightedArea B.shape) :
    A = B := by
  have hAffine :
      affineConst A.toFiberPoint.word =
        affineConst B.toFiberPoint.word := by
    rw [affineConst_toFiberPoint_eq_base_add_weightedArea,
        affineConst_toFiberPoint_eq_base_add_weightedArea,
        hArea]
  have hPoint : A.toFiberPoint = B.toFiberPoint :=
    fiberPoint_eq_of_same_affineConst hAffine
  apply FiberShape.ext_shape
  calc
    A.shape = A.toFiberPoint.toFerrersShape :=
      A.toFerrersShape_toFiberPoint.symm
    _ = B.toFiberPoint.toFerrersShape :=
      congrArg FiberPoint.toFerrersShape hPoint
    _ = B.shape := B.toFerrersShape_toFiberPoint

/-- fixed-fiber inclusion は weighted area を単調にする。 -/
theorem weightedArea_mono
    {p H : ℕ}
    {A B : FiberShape p H}
    (hAB : A.Le B) :
    weightedArea A.shape ≤ weightedArea B.shape :=
  RecordFerrers.weightedArea_mono hAB

/-- proper inclusion では weighted area は strict に増える。 -/
theorem weightedArea_strictMono
    {p H : ℕ}
    {A B : FiberShape p H}
    (hAB : A.Le B)
    (hNe : A ≠ B) :
    weightedArea A.shape < weightedArea B.shape := by
  have hLe := A.weightedArea_mono hAB
  have hAreaNe : weightedArea A.shape ≠ weightedArea B.shape := by
    intro hEq
    exact hNe (FiberShape.weightedArea_injective hEq)
  omega

/-- fixed-fiber inclusion は genuine affineConst を単調にする。 -/
theorem affineConst_mono
    {p H : ℕ}
    {A B : FiberShape p H}
    (hAB : A.Le B) :
    affineConst A.toFiberPoint.word ≤
      affineConst B.toFiberPoint.word := by
  rw [affineConst_toFiberPoint_eq_base_add_weightedArea,
      affineConst_toFiberPoint_eq_base_add_weightedArea]
  exact Nat.add_le_add_left (A.weightedArea_mono hAB) _

/-- proper Ferrers inclusion では affineConst が strict に増える。 -/
theorem affineConst_strictMono
    {p H : ℕ}
    {A B : FiberShape p H}
    (hAB : A.Le B)
    (hNe : A ≠ B) :
    affineConst A.toFiberPoint.word <
      affineConst B.toFiberPoint.word := by
  rw [affineConst_toFiberPoint_eq_base_add_weightedArea,
      affineConst_toFiberPoint_eq_base_add_weightedArea]
  have hStrict := A.weightedArea_strictMono hAB hNe
  omega

end FiberShape

/-- parameter `p` を一つ増やした baseline affine budget の recurrence。 -/
theorem baseAffineConst_succ
    (p : ℕ) :
    baseAffineConst (p + 1) =
      3 * baseAffineConst p + 2 ^ p := by
  unfold baseAffineConst
  rw [Finset.sum_range_succ]
  have hPrefix :
      Finset.sum (Finset.range p) (fun k => baseAffineTerm (p + 1) k) =
        3 * Finset.sum (Finset.range p) (fun k => baseAffineTerm p k) := by
    calc
      Finset.sum (Finset.range p) (fun k => baseAffineTerm (p + 1) k)
          = Finset.sum (Finset.range p) (fun k => 3 * baseAffineTerm p k) := by
              apply Finset.sum_congr rfl
              intro k hkMem
              have hk : k < p := Finset.mem_range.mp hkMem
              unfold baseAffineTerm
              have hSub :
                  p + 1 - (k + 1) = (p - (k + 1)) + 1 := by
                omega
              rw [hSub, pow_succ]
              ring
      _ = 3 * Finset.sum (Finset.range p) (fun k => baseAffineTerm p k) := by
            rw [Finset.mul_sum]
  rw [hPrefix]
  simp [baseAffineTerm]

/-- baseline budget の subtraction-free closed form。 -/
theorem baseAffineConst_add_twoPow
    (p : ℕ) :
    baseAffineConst p + 2 ^ p = 3 ^ p := by
  induction p with
  | zero =>
      simp [baseAffineConst]
  | succ p ih =>
      have hRec := baseAffineConst_succ p
      rw [hRec, pow_succ, pow_succ]
      omega

/-- baseline budget は `3^p - 2^p`。 -/
theorem baseAffineConst_eq_threePow_sub_twoPow
    (p : ℕ) :
    baseAffineConst p = 3 ^ p - 2 ^ p := by
  have h := baseAffineConst_add_twoPow p
  omega

/-- 任意 fixed fiber point の affineConst は baseline 以上。 -/
theorem affineConst_lower_bound
    {p H : ℕ}
    (x : FiberPoint p H) :
    3 ^ p - 2 ^ p ≤ affineConst x.word := by
  rw [affineConst_eq_base_add_weightedArea x,
      baseAffineConst_eq_threePow_sub_twoPow]
  omega

/-- contracting chord では critical roof terminal height は `H` より真に低い。 -/
theorem criticalHeight_lt_terminalDepth_of_contractingChord
    {p H : ℕ}
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    criticalHeight p < H := by
  by_contra hNot
  have hHLe : H ≤ criticalHeight p := Nat.le_of_not_gt hNot
  have hPowLe : 2 ^ H ≤ 2 ^ criticalHeight p :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hHLe
  have hCrit := criticalHeight_pow_lt_threePow hp
  unfold ContractingChord at hContract
  omega

/-- FirstCrossing fixed fiber では affineConst は baseline と critical budget の間。 -/
theorem affineConst_between_baseline_and_critical
    {p H : ℕ}
    (x : FiberPoint p H)
    (hF : FirstCrossing x.word) :
    3 ^ p - 2 ^ p ≤ affineConst x.word ∧
      affineConst x.word ≤ criticalAffineConst p := by
  refine ⟨affineConst_lower_bound x, ?_⟩
  have hUpper := affineConst_le_criticalAffineConst_of_firstCrossing hF
  simpa [x.oddSteps_eq] using hUpper

namespace FerrersShape

/-- all-zero Ferrers profile。 -/
def zero (p : ℕ) : FerrersShape p :=
  { column := fun _ => 0
    mono := by
      intro i j hij
      exact le_rfl }

@[simp] theorem zero_atNat
    (p k : ℕ) :
    (zero p).atNat k = 0 := by
  by_cases hk : k < p
  · simp [zero, FerrersShape.atNat, hk]
  · simp [FerrersShape.atNat, hk]

@[simp] theorem weightedArea_zero
    (p : ℕ) :
    weightedArea (zero p) = 0 := by
  unfold weightedArea
  simp [zero_atNat, excessAffineWeight]

end FerrersShape

namespace FiberShape

/-- fixed rectangle の unique bottom Ferrers shape。 -/
def bottom
    (p H : ℕ)
    (hp : 0 < p)
    (hpH : p ≤ H) : FiberShape p H :=
  { shape := FerrersShape.zero p
    p_pos := hp
    p_le_H := hpH
    first_zero := by simp [FerrersShape.zero]
    bounded := by
      intro i
      simp [FerrersShape.zero] }

/-- bottom は全 fixed-fiber shapes 以下。 -/
theorem bottom_le
    {p H : ℕ}
    (A : FiberShape p H) :
    (bottom p H A.p_pos A.p_le_H).Le A := by
  intro i
  simp [bottom, FerrersShape.zero]

@[simp] theorem weightedArea_bottom
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    weightedArea (bottom p H hp hpH).shape = 0 := by
  simp [bottom]

/-- baseline equality は unique bottom shape を特徴付ける。 -/
theorem affineConst_eq_base_iff_bottom
    {p H : ℕ}
    (A : FiberShape p H) :
    affineConst A.toFiberPoint.word = baseAffineConst p ↔
      A = bottom p H A.p_pos A.p_le_H := by
  constructor
  · intro hAffine
    have hFormula := affineConst_toFiberPoint_eq_base_add_weightedArea A
    have hAreaZero : weightedArea A.shape = 0 := by
      omega
    have hBottomArea :
        weightedArea (bottom p H A.p_pos A.p_le_H).shape = 0 := by
      simp
    apply FiberShape.weightedArea_injective
    exact hAreaZero.trans hBottomArea.symm
  · intro hEq
    rw [hEq, affineConst_toFiberPoint_eq_base_add_weightedArea]
    simp

/-- contracting fixed fiber の critical top shape。 -/
def criticalTop
    (p H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) : FiberShape p H := by
  have hCritLt : criticalHeight p < H :=
    criticalHeight_lt_terminalDepth_of_contractingChord hp hContract
  have hpCrit : p ≤ criticalHeight p := index_le_criticalHeight p
  have hpH : p ≤ H := by omega
  refine {
    shape := criticalShape p
    p_pos := hp
    p_le_H := hpH
    first_zero := ?_
    bounded := ?_
  }
  · simp [criticalShape, criticalExcess, criticalHeight]
  · intro i
    have hMono : criticalExcess i.1 ≤ criticalExcess p :=
      criticalExcess_mono (Nat.le_of_lt i.isLt)
    have hExP : criticalExcess p ≤ H - p := by
      unfold criticalExcess
      omega
    exact hMono.trans hExP

/-- critical top は全 FirstCrossing shapes の上端。 -/
theorem le_criticalTop_of_firstCrossing
    {p H : ℕ}
    (A : FiberShape p H)
    (hContract : ContractingChord p H)
    (hF : FirstCrossing A.toFiberPoint.word) :
    A.Le (criticalTop p H A.p_pos hContract) := by
  have hShape :=
    (A.firstCrossing_toFiberPoint_iff hContract).1 hF
  change A.shape.Le (criticalShape p)
  exact hShape

/-- critical top 自身は FirstCrossing。 -/
theorem criticalTop_firstCrossing
    {p H : ℕ}
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossing
      (criticalTop p H hp hContract).toFiberPoint.word := by
  apply
    ((criticalTop p H hp hContract).firstCrossing_toFiberPoint_iff
      hContract).2
  change (criticalShape p).Le (criticalShape p)
  exact FerrersShape.le_refl (criticalShape p)

/-- critical budget equality は unique critical top を特徴付ける。 -/
theorem affineConst_eq_critical_iff_top
    {p H : ℕ}
    (A : FiberShape p H)
    (hContract : ContractingChord p H) :
    affineConst A.toFiberPoint.word = criticalAffineConst p ↔
      A = criticalTop p H A.p_pos hContract := by
  constructor
  · intro hAffine
    have hA := affineConst_toFiberPoint_eq_base_add_weightedArea A
    have hC := criticalAffineConst_eq_base_add_weightedArea p
    have hArea :
        weightedArea A.shape = weightedArea (criticalShape p) := by
      omega
    apply FiberShape.weightedArea_injective
    simpa [criticalTop] using hArea
  · intro hEq
    rw [hEq, affineConst_toFiberPoint_eq_base_add_weightedArea,
        criticalAffineConst_eq_base_add_weightedArea]
    simp [criticalTop]

/-- lower extremum `3^p-2^p` の equality case も unique bottom。 -/
theorem affineConst_eq_lower_iff_bottom
    {p H : ℕ}
    (A : FiberShape p H) :
    affineConst A.toFiberPoint.word = 3 ^ p - 2 ^ p ↔
      A = bottom p H A.p_pos A.p_le_H := by
  rw [← baseAffineConst_eq_threePow_sub_twoPow]
  exact A.affineConst_eq_base_iff_bottom

end FiberShape

end RecordFerrers
end Collatz2
