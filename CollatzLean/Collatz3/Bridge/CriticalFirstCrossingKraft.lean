import CollatzLean.Collatz3.Bridge.CriticalSurvivorParity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: first-crossing tree の finite Kraft 恒等式

parity survivor tree の cardinal recurrence

`2 S_n = S_(n+1) + F_(n+1)`

を `2^n` で正規化すると、各 depth で失われる mass が first-crossing mass になる。

このファイルでは

`sum_{r=2}^{n+1} F_r / 2^r + S_(n+1) / 2^(n+1) = 1/2`

という exact finite Kraft identity を証明する。

さらに critical depth `H_m = criticalTwoDepth m` では

`F_(H_m) = criticalPartitionCount m = N_m`

を exact equivalence から得る。
-/

namespace Collatz3
namespace Bridge

open scoped BigOperators

/-- critical terminal depth は幅に関して strict mono。 -/
theorem criticalTwoDepth_strictMono : StrictMono Critical.criticalTwoDepth := by
  apply strictMono_nat_of_lt_succ
  intro m
  unfold Critical.criticalTwoDepth
  have h := Critical.beattyIndex_lt_succ m
  omega

/-- critical terminal depth は幅を一意に決める。 -/
theorem criticalTwoDepth_injective : Function.Injective Critical.criticalTwoDepth :=
  criticalTwoDepth_strictMono.injective

/--
critical depth `H_m` の generic first-crossing code と order `m` admissible code の exact equivalence。
-/
def firstCrossingAtCriticalDepthEquivAdmissible
    (m : ℕ) :
    FirstCrossingParityCode (Critical.criticalTwoDepth m) ≃
      AdmissibleParityCode m where
  toFun C := by
    have hDepth := C.2.criticalTwoDepth_eq
    have hLen : C.1.length = m := by
      apply criticalTwoDepth_injective
      exact hDepth.symm
    refine ⟨C.1, ?_⟩
    constructor
    · exact hLen
    · intro k hk
      have hk' : k < C.1.length := by simpa [hLen] using hk
      exact C.2.sizeUpTo_le_beatty hk'
  invFun A := by
    refine ⟨A.1, ?_⟩
    constructor
    · rw [A.2.length_eq]
      exact criticalTwoDepth_previous_safe m
    · constructor
      · rw [A.2.length_eq]
        exact criticalTwoDepth_terminal_crosses m
      · intro k hk
        have hkM : k < m := by
          simpa [A.2.length_eq] using hk
        exact admissibleParityCode_power_prefix A hkM
  left_inv C := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

/-- critical depth における first-crossing 数は `N_m`。 -/
theorem firstCrossingParityCount_criticalDepth
    {m : ℕ}
    (hm : 0 < m) :
    firstCrossingParityCount (Critical.criticalTwoDepth m) =
      criticalPartitionCount m := by
  unfold firstCrossingParityCount
  calc
    Nat.card (FirstCrossingParityCode (Critical.criticalTwoDepth m)) =
        Nat.card (AdmissibleParityCode m) :=
      Nat.card_congr (firstCrossingAtCriticalDepthEquivAdmissible m)
    _ = criticalPartitionCount m :=
      natCard_admissibleParityCode_eq_criticalPartitionCount hm

/-- survivor の normalized mass。 -/
noncomputable def survivorParityRatio (n : ℕ) : ℝ :=
  (survivorParityCount n : ℝ) / (2 ^ n : ℝ)

/-- depth `n` で新しく first crossing する normalized mass。 -/
noncomputable def firstCrossingParityMass (n : ℕ) : ℝ :=
  (firstCrossingParityCount n : ℝ) / (2 ^ n : ℝ)

/-- depths `2,...,N+1` の first-crossing mass の有限和。 -/
noncomputable def firstCrossingParityMassPartial (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) (fun r => firstCrossingParityMass (r + 2))

/-- cardinal recurrence を normalized mass recurrence に直した exact identity。 -/
theorem survivorParityRatio_step
    {n : ℕ}
    (hn : 0 < n) :
    survivorParityRatio n =
      survivorParityRatio (n + 1) + firstCrossingParityMass (n + 1) := by
  have hNat := two_mul_survivorParityCount_eq hn
  have hReal :
      (2 : ℝ) * (survivorParityCount n : ℝ) =
        (survivorParityCount (n + 1) : ℝ) +
          (firstCrossingParityCount (n + 1) : ℝ) := by
    exact_mod_cast hNat
  unfold survivorParityRatio firstCrossingParityMass
  rw [← add_div]
  rw [pow_succ]
  have hTwoPow : (2 ^ n : ℝ) ≠ 0 := by positivity
  calc
    (survivorParityCount n : ℝ) / (2 ^ n : ℝ)
        = ((2 : ℝ) * (survivorParityCount n : ℝ)) /
            ((2 : ℝ) * (2 ^ n : ℝ)) := by
          field_simp [hTwoPow]
    _ =
        ((survivorParityCount (n + 1) : ℝ) +
          (firstCrossingParityCount (n + 1) : ℝ)) /
            ((2 : ℝ) * (2 ^ n : ℝ)) := by rw [hReal]
    _ =
        ((survivorParityCount (n + 1) : ℝ) +
          (firstCrossingParityCount (n + 1) : ℝ)) /
            (2 ^ (n + 1) : ℝ) := by rw [pow_succ]
                                    ring

/--
finite Kraft identity。

`N` 段分の crossing mass と、まだ残っている survivor mass の和は常に `1/2`。
-/
theorem firstCrossingParityMassPartial_add_survivor
    (N : ℕ) :
    firstCrossingParityMassPartial N + survivorParityRatio (N + 1) =
      (1 : ℝ) / 2 := by
  induction N with
  | zero =>
      simp [firstCrossingParityMassPartial, survivorParityRatio,
        survivorParityCount_one]
  | succ N ih =>
      rw [show firstCrossingParityMassPartial (N + 1) =
          firstCrossingParityMassPartial N +
            firstCrossingParityMass (N + 2) by
        unfold firstCrossingParityMassPartial
        rw [Finset.sum_range_succ]]
      have hStep := survivorParityRatio_step (n := N + 1) (by omega)
      linarith

/-- finite crossing mass は `1/2` 以下。 -/
theorem firstCrossingParityMassPartial_le_half
    (N : ℕ) :
    firstCrossingParityMassPartial N ≤ (1 : ℝ) / 2 := by
  have h := firstCrossingParityMassPartial_add_survivor N
  have hNonneg : 0 ≤ survivorParityRatio (N + 1) := by
    unfold survivorParityRatio
    positivity
  linarith

/-- critical depth の crossing mass は `N_m / 2^H_m`。 -/
theorem firstCrossingParityMass_criticalDepth
    {m : ℕ}
    (hm : 0 < m) :
    firstCrossingParityMass (Critical.criticalTwoDepth m) =
      (criticalPartitionCount m : ℝ) /
        (2 ^ Critical.criticalTwoDepth m : ℝ) := by
  unfold firstCrossingParityMass
  rw [firstCrossingParityCount_criticalDepth hm]

end Bridge
end Collatz3
