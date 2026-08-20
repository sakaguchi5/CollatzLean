import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreRightCarry

/-!
# Pure B: terminal core divisibility = right carry chain

`r` 段の right carry chain を「depth `j <= r` の全 3-power が core を割る」として
定義する。power divisibility は nested なので、最深 `3^r | core` と exact に同値。

前段の `v_3(core)=c-a` と合わせると、canonical B corridor は
`r=c-a` 段まで成功し `r+1` 段目で初めて失敗する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- integer `z` に対する長さ `r` の 3-adic right carry chain。 -/
def RightCarryChain
    (z : ℤ)
    (r : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ r → (3 : ℤ) ^ j ∣ z

/-- 最深 divisibility は全浅い divisibility を含む。 -/
theorem threePow_dvd_iff_rightCarryChain
    (z : ℤ)
    (r : ℕ) :
    (3 : ℤ) ^ r ∣ z ↔ RightCarryChain z r := by
  constructor
  · intro hr j hj
    rcases hr with ⟨u, hu⟩
    refine ⟨(3 : ℤ) ^ (r - j) * u, ?_⟩
    have hExp : r = j + (r - j) := by omega
    rw [hu, hExp, pow_add]
    ring_nf
    simp
  · intro h
    exact h r le_rfl

namespace PureBProfileObstruction

/-- terminal core 版。 -/
theorem terminalCore_divisibility_iff_rightCarryChain
    (P : PureBProfileObstruction)
    (r : ℕ) :
    (3 : ℤ) ^ r ∣ (P.terminalNoncriticalProfileCore : ℤ) ↔
      RightCarryChain (P.terminalNoncriticalProfileCore : ℤ) r := by
  exact threePow_dvd_iff_rightCarryChain _ _

/-- canonical corridor は `c-a` 段の carry chain を exact に持つ。 -/
theorem terminalCore_canonical_rightCarryChain
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    RightCarryChain
      (P.terminalNoncriticalProfileCore : ℤ)
      (P.terminalCriticalStart - P.criticalizationStart) := by
  apply
    (P.terminalCore_divisibility_iff_rightCarryChain
      (P.terminalCriticalStart - P.criticalizationStart)).1
  exact (P.terminalCore_exactThreeAdicOrder hStart).1

/-- canonical corridor の一段先では carry が失敗する。 -/
theorem terminalCore_rightCarryChain_fails_next
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ¬ RightCarryChain
      (P.terminalNoncriticalProfileCore : ℤ)
      (P.terminalCriticalStart - P.criticalizationStart + 1) := by
  intro h
  have hDeep :=
    (P.terminalCore_divisibility_iff_rightCarryChain
      (P.terminalCriticalStart - P.criticalizationStart + 1)).2 h
  exact (P.terminalCore_exactThreeAdicOrder hStart).2 hDeep

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
