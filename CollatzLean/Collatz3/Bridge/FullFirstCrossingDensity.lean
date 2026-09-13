import CollatzLean.Collatz3.Bridge.FullFirstCrossingCoarseFiber
import CollatzLean.Collatz3.Bridge.CriticalFixedWidthDensity
import Mathlib.Tactic.FieldSimp

/-!
# Collatz3 Bridge: full first-crossing の fixed-width exact density

coarse fiber classification により、fixed partition の全 terminal overshoot は
法 `2^H` の一本の arithmetic progression になる。

従って fixed width `m > 0` では full first-crossing start の自然密度は

`N_m / 2^H = 2 N_m / 2^(H+1)`

である。ここでは exact block counting から bounded discrepancy を作り、
既存の一般 `Tendsto` 補題へ渡す。
-/

namespace Collatz3
namespace Bridge

open Filter Topology

/-- cutoff inclusion。 -/
def fullActualCriticalStartBelowMap
    {m B C : ℕ}
    (hBC : B ≤ C) :
    FullActualCriticalStartBelow m B → FullActualCriticalStartBelow m C :=
  fun x => ⟨x.1, lt_of_lt_of_le x.2.1 hBC, x.2.2⟩

/-- cutoff inclusion は単射。 -/
theorem fullActualCriticalStartBelowMap_injective
    {m B C : ℕ}
    (hBC : B ≤ C) :
    Function.Injective
      (fullActualCriticalStartBelowMap (m := m) hBC) := by
  intro a b h
  apply Subtype.ext
  simpa [fullActualCriticalStartBelowMap] using
    congrArg (fun x : FullActualCriticalStartBelow m C => x.1) h

/-- full-start count は cutoff に関して単調。 -/
theorem fullActualCriticalStartCount_mono
    {m B C : ℕ}
    (hBC : B ≤ C) :
    fullActualCriticalStartCount m B ≤ fullActualCriticalStartCount m C := by
  let : Finite (FullActualCriticalStartBelow m C) :=
    fullActualCriticalStartBelow_finite m C
  exact
    Nat.card_le_card_of_injective
      (fullActualCriticalStartBelowMap (m := m) hBC)
      (fullActualCriticalStartBelowMap_injective (m := m) hBC)

/-- floor coarse block は cutoff 以下。 -/
theorem fullCrossingStartModulus_mul_div_le
    (m X : ℕ) :
    fullCrossingStartModulus m * (X / fullCrossingStartModulus m) ≤ X := by
  have h := Nat.mod_add_div X (fullCrossingStartModulus m)
  omega

/-- cutoff は次の coarse block より小さい。 -/
theorem lt_fullCrossingStartModulus_mul_div_add_one
    (m X : ℕ) :
    X < fullCrossingStartModulus m *
      (X / fullCrossingStartModulus m + 1) := by
  let M := fullCrossingStartModulus m
  have hM : 0 < M := by simp only [fullCrossingStartModulus_eq, Critical.criticalTwoDepth_eq,
                                    Order.lt_two_iff, zero_le, pow_succ_pos, M]
  have hmod : X % M < M := Nat.mod_lt X hM
  have hdiv : X % M + M * (X / M) = X := Nat.mod_add_div X M
  calc
    X = X % M + M * (X / M) := hdiv.symm
    _ < M + M * (X / M) := Nat.add_lt_add_right hmod _
    _ = M * (X / M + 1) := by ring

/-- arbitrary cutoff count は adjacent full coarse blocks の間にある。 -/
theorem fullActualCriticalStartCount_sandwich
    {m X : ℕ}
    (hm : 0 < m) :
    criticalPartitionCount m * (X / fullCrossingStartModulus m) ≤
        fullActualCriticalStartCount m X ∧
      fullActualCriticalStartCount m X ≤
        criticalPartitionCount m * (X / fullCrossingStartModulus m + 1) := by
  let q := X / fullCrossingStartModulus m
  constructor
  · calc
      criticalPartitionCount m * q
          = fullActualCriticalStartCount m (fullCrossingStartModulus m * q) :=
        (fullActualCriticalStartCount_block_eq hm q).symm
      _ ≤ fullActualCriticalStartCount m X :=
        fullActualCriticalStartCount_mono
          (fullCrossingStartModulus_mul_div_le m X)
  · calc
      fullActualCriticalStartCount m X
          ≤ fullActualCriticalStartCount m
              (fullCrossingStartModulus m * (q + 1)) :=
        fullActualCriticalStartCount_mono
          (le_of_lt (lt_fullCrossingStartModulus_mul_div_add_one m X))
      _ = criticalPartitionCount m * (q + 1) :=
        fullActualCriticalStartCount_block_eq hm (q + 1)

/-- full-start count の cross-multiplied discrepancy は一 coarse period 分以下。 -/
theorem fullActualCriticalStartCount_cross_discrepancy
    {m X : ℕ}
    (hm : 0 < m) :
    fullCrossingStartModulus m * fullActualCriticalStartCount m X ≤
        criticalPartitionCount m * X +
          fullCrossingStartModulus m * criticalPartitionCount m ∧
      criticalPartitionCount m * X ≤
        fullCrossingStartModulus m * fullActualCriticalStartCount m X +
          fullCrossingStartModulus m * criticalPartitionCount m := by
  let M := fullCrossingStartModulus m
  let N := criticalPartitionCount m
  let C := fullActualCriticalStartCount m X
  let q := X / M
  have hSand := fullActualCriticalStartCount_sandwich (m := m) (X := X) hm
  have hLower : N * q ≤ C := by simpa [M, N, C, q] using hSand.1
  have hUpper : C ≤ N * (q + 1) := by simpa [M, N, C, q] using hSand.2
  have hBlockLower : M * q ≤ X := by
    simpa [M, q] using fullCrossingStartModulus_mul_div_le m X
  have hBlockUpper : X ≤ M * (q + 1) := by
    exact le_of_lt (by
      simpa [M, q] using lt_fullCrossingStartModulus_mul_div_add_one m X)
  constructor
  · calc
      M * C ≤ M * (N * (q + 1)) := Nat.mul_le_mul_left M hUpper
      _ = N * (M * q) + M * N := by ring
      _ ≤ N * X + M * N :=
        Nat.add_le_add_right (Nat.mul_le_mul_left N hBlockLower) _
  · calc
      N * X ≤ N * (M * (q + 1)) := Nat.mul_le_mul_left N hBlockUpper
      _ = M * (N * q) + M * N := by ring
      _ ≤ M * C + M * N :=
        Nat.add_le_add_right (Nat.mul_le_mul_left M hLower) _

/-- `X` 未満の full first-crossing starts の割合。 -/
noncomputable def fullFixedWidthCriticalStartRatio
    (m X : ℕ) : ℝ :=
  (fullActualCriticalStartCount m X : ℝ) / (X : ℝ)

/-- full first-crossing の fixed-width density `N_m / 2^H`。 -/
noncomputable def fullFixedWidthCriticalStartDensity
    (m : ℕ) : ℝ :=
  (criticalPartitionCount m : ℝ) /
    (fullCrossingStartModulus m : ℝ)

/-- fixed width full first-crossing ratio は exact density へ収束。 -/
theorem fullFixedWidthCriticalStartRatio_tendsto
    {m : ℕ}
    (hm : 0 < m) :
    Tendsto
      (fullFixedWidthCriticalStartRatio m)
      atTop
      (𝓝 (fullFixedWidthCriticalStartDensity m)) := by
  unfold fullFixedWidthCriticalStartRatio fullFixedWidthCriticalStartDensity
  exact
    tendsto_ratio_of_nat_cross_discrepancy
      (fullCrossingStartModulus m)
      (criticalPartitionCount m)
      (fullCrossingStartModulus_pos m)
      (fullActualCriticalStartCount m)
      (fun X => fullActualCriticalStartCount_cross_discrepancy
        (m := m) (X := X) hm)

/-- full density は従来の minimal-terminal density のちょうど2倍。 -/
theorem fullFixedWidthCriticalStartDensity_eq_two_mul_minimal
    (m : ℕ) :
    fullFixedWidthCriticalStartDensity m =
      2 * fixedWidthCriticalStartDensity m := by
  unfold fullFixedWidthCriticalStartDensity fixedWidthCriticalStartDensity
  have hF : (fullCrossingStartModulus m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fullCrossingStartModulus_pos m)
  have hRel := criticalStartModulus_eq_two_mul_fullCrossingStartModulus m
  have hRelR :
      (criticalStartModulus m : ℝ) =
        2 * (fullCrossingStartModulus m : ℝ) := by
    exact_mod_cast hRel
  rw [hRelR]
  field_simp [hF]

/-- requested form: full density = `2 N_m / M_m`。 -/
theorem fullFixedWidthCriticalStartDensity_eq_two_partitionCount_div_criticalModulus
    (m : ℕ) :
    fullFixedWidthCriticalStartDensity m =
      (2 * (criticalPartitionCount m : ℝ)) /
        (criticalStartModulus m : ℝ) := by
  rw [fullFixedWidthCriticalStartDensity_eq_two_mul_minimal]
  unfold fixedWidthCriticalStartDensity
  ring

end Bridge
end Collatz3
