import CollatzLean.Collatz3.Critical.BeattyCarry
import CollatzLean.Collatz3.Critical.RoofAnchor
import CollatzLean.Collatz3.Experimental2

/-!
# Collatz3 Bridge: Beatty roof の Experimental2 realization

`Critical.beattyIndex` が `Experimental2` の generic unit-carry roof を実現することを示す。

ここでは `beattyIndex` の 2冪/3冪による Collatz 固有算術を再証明しない。
既存の `Critical.BeattyCarry` を realization certificate として使い、
以後の slope / mechanical / carry-word 理論を `Experimental2` から受け取る。
-/

namespace Collatz3
namespace Bridge

/-- Beatty roof は generic 下側超加法性を満たす。 -/
theorem beattyIndex_isSuperadditiveRoof :
    Experimental2.IsSuperadditiveRoof Critical.beattyIndex := by
  intro a b
  exact Critical.beattyIndex_add_lower a b

/-- Beatty roof の additive excess は generic 上側一単位誤差を満たす。 -/
theorem beattyIndex_hasUnitUpperDefect :
    Experimental2.HasUnitUpperDefect Critical.beattyIndex := by
  intro a b
  exact Critical.beattyIndex_add_upper a b

/--
Collatz の `beattyIndex` は Experimental2 の `HasUnitCarry` の genuine realization。
-/
theorem beattyIndex_hasUnitCarry :
    Experimental2.HasUnitCarry Critical.beattyIndex :=
  ⟨beattyIndex_isSuperadditiveRoof, beattyIndex_hasUnitUpperDefect⟩

/-- Critical 側の Beatty carry と generic roof carry は definitionally 同一。 -/
@[simp] theorem experimental2_roofCarry_beattyIndex_eq
    (a b : ℕ) :
    Experimental2.roofCarry Critical.beattyIndex a b =
      Critical.beattyCarry a b := by
  rfl

/-- Critical 側の terminal two-depth と generic critical depth は同一。 -/
@[simp] theorem experimental2_criticalDepth_beattyIndex_eq
    (m : ℕ) :
    Experimental2.criticalDepth Critical.beattyIndex m =
      Critical.criticalTwoDepth m := by
  rfl

/--
旧 `beattyIndex_below_criticalChord` は generic unit-carry theorem から直接回収できる。

generic theorem は `m > 0` を必要としないので、この statement は少し強い。
-/
theorem beattyIndex_below_criticalChord_via_experimental2
    {m r : ℕ}
    (hr : 0 < r) :
    m * Critical.beattyIndex r <
      Critical.criticalTwoDepth m * r := by
  simpa using
    (beattyIndex_hasUnitCarry.below_criticalChord (m := m) (r := r) hr)

/-- Beatty roof 自身には exact roof slope が存在し、一意。 -/
theorem existsUnique_beattyIndex_roofSlope :
    ∃! σ : ℝ,
      Experimental2.IsRoofSlope Critical.beattyIndex σ :=
  beattyIndex_hasUnitCarry.existsUnique_roofSlope

/--
Beatty roof は lower / upper mechanical roof のどちらかとして realization される。
この時点では slope を `log₂ 3` と同定せず、generic completeness だけを使う。
-/
theorem exists_beattyIndex_mechanicalRoof :
    ∃ σ : ℝ,
      Experimental2.IsLowerMechanicalRoof Critical.beattyIndex σ ∨
        Experimental2.IsUpperMechanicalRoof Critical.beattyIndex σ :=
  beattyIndex_hasUnitCarry.exists_lower_or_upperMechanicalRoof

/-- `beattyIndex 1 = 1` なので正規化 roof は `beattyIndex n - n`。 -/
@[simp] theorem normalizeRoof_beattyIndex_eq
    (n : ℕ) :
    Experimental2.normalizeRoof Critical.beattyIndex n =
      Critical.beattyIndex n - n := by
  simp [Experimental2.normalizeRoof, Critical.beattyIndex_one]

/-- Beatty carry word は `beattyCarry n 1` そのもの。 -/
@[simp] theorem carryWord_beattyIndex_eq
    (n : ℕ) :
    Experimental2.carryWord Critical.beattyIndex n =
      Critical.beattyCarry n 1 := by
  rfl

/-- Beatty の一歩 carry word は generic theorem により balanced。 -/
theorem beattyCarryWord_balanced
    (a b r : ℕ) :
    Experimental2.carryWordWeight Critical.beattyIndex a r ≤
        Experimental2.carryWordWeight Critical.beattyIndex b r + 1 ∧
      Experimental2.carryWordWeight Critical.beattyIndex b r ≤
        Experimental2.carryWordWeight Critical.beattyIndex a r + 1 :=
  beattyIndex_hasUnitCarry.carryWord_balanced a b r

end Bridge
end Collatz3
