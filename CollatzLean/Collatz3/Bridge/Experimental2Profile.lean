import CollatzLean.Collatz3.Bridge.Experimental2Beatty
import CollatzLean.Collatz3.Critical.RecordCarryExact

/-!
# Collatz3 Bridge: critical profile を generic roof path として読む

admissible critical profile の `profileHeight` は、
屋根 `beattyIndex` に対する Experimental2 の admissible roof path そのものである。

この bridge により、Critical 側で個別に証明していた

* local prefix failure,
* terminal minimality

を generic roof-path theorem から再取得できる。
-/

namespace Collatz3
namespace Bridge

/--
Critical の admissible profile height path を Experimental2 の generic roof path に上げる。
-/
theorem admissibleProfile_isExperimental2RoofPath
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h) :
    Experimental2.IsAdmissibleRoofPath
      Critical.beattyIndex m (Critical.profileHeight h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [Critical.profileHeight_of_lt h hk]
    unfold Critical.checkpoint
    exact Nat.sub_le _ _
  · intro k hk
    exact Critical.profileHeight_lt_succ A hk
  · unfold Experimental2.HasCriticalTerminal
    exact Critical.profileHeight_terminal h

/-- Critical の roof cut と Experimental2 の proper roof cut は同一条件。 -/
theorem criticalRoofCut_iff_experimental2ProperRoofCut
    {m : ℕ}
    (h : Critical.Profile m)
    (a : ℕ) :
    Critical.IsRoofCut h a ↔
      Experimental2.IsProperRoofCut
        Critical.beattyIndex m (Critical.profileHeight h) a := by
  rfl

/-- Critical の local depth と Experimental2 の local depth は definitionally 同一。 -/
@[simp] theorem criticalLocalDepth_eq_experimental2LocalDepth
    {m : ℕ}
    (h : Critical.Profile m)
    (a j : ℕ) :
    Critical.localDepth h a j =
      Experimental2.localDepth (Critical.profileHeight h) a j := by
  rfl

/--
Critical の local prefix failure law を generic roof-path theorem から回収する。

旧 theorem にあった `0 < j` は generic arithmetic には不要であり、
ここでは仮定から外れている。
-/
theorem localPrefixFailure_iff_via_experimental2
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a j : ℕ}
    (hStartRoof : Critical.IsRoofCut h a)
    (hEndLt : a + j < m) :
    Critical.beattyIndex j < Critical.localDepth h a j ↔
      Critical.IsRoofCut h (a + j) ∧
        Critical.beattyCarry a j = 1 := by
  have P := admissibleProfile_isExperimental2RoofPath A
  have hStart :
      Experimental2.IsProperRoofCut
        Critical.beattyIndex m (Critical.profileHeight h) a :=
    (criticalRoofCut_iff_experimental2ProperRoofCut h a).1 hStartRoof
  have G :=
    Experimental2.localFailure_iff_roofReturn_and_carryOne
      beattyIndex_hasUnitCarry P hStart hEndLt
  simpa [Critical.localDepth, Experimental2.localDepth,
    Critical.beattyCarry, Experimental2.roofCarry,
    Critical.IsRoofCut, Experimental2.IsProperRoofCut,
    Experimental2.IsOnRoof] using G

/--
Critical の terminal minimality law も generic exact-depth theorem の corollary になる。
-/
theorem terminalMinimal_iff_via_experimental2
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a r : ℕ}
    (hStartRoof : Critical.IsRoofCut h a)
    (hTerminal : a + r = m) :
    Critical.localDepth h a r = Critical.criticalTwoDepth r ↔
      Critical.beattyCarry a r = 0 := by
  have P := admissibleProfile_isExperimental2RoofPath A
  have hStart :
      Experimental2.IsProperRoofCut
        Critical.beattyIndex m (Critical.profileHeight h) a :=
    (criticalRoofCut_iff_experimental2ProperRoofCut h a).1 hStartRoof
  have G :=
    Experimental2.terminalMinimal_iff_carryZero
      beattyIndex_hasUnitCarry P hStart hTerminal
  simpa [Critical.localDepth, Experimental2.localDepth,
    Critical.criticalTwoDepth, Experimental2.criticalDepth,
    Critical.beattyCarry, Experimental2.roofCarry] using G

/--
Critical の `NoPrematureCarryOneRoofReturn` は generic roof/carry 語彙だけでそのまま読める。
-/
theorem noPrematureCarryOneRoofReturn_iff_experimental2
    {m : ℕ}
    (h : Critical.Profile m)
    (a r : ℕ) :
    Critical.NoPrematureCarryOneRoofReturn h a r ↔
      ∀ j : ℕ,
        0 < j →
        j < r →
        ¬ (
          Experimental2.IsProperRoofCut
            Critical.beattyIndex m (Critical.profileHeight h) (a + j) ∧
          Experimental2.roofCarry Critical.beattyIndex a j = 1) := by
  rfl

end Bridge
end Collatz3
