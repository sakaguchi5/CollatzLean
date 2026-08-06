import CollatzLean.CollatzSecondLayer3.FutureMinimumSpecialC3
import CollatzLean.CollatzSecondLayer3.DeepLowerReplayExclusion

/-!
# source-preserving Special C3への最終還元

future-minimumから得られる生成履歴付き最終二分岐のうち、
deep lower-replay towerは既に排除されている。

したがって非有界odd-only軌道は、generic obstructionへ情報を忘れる前に、
生成履歴を完全に保持したSpecial C3 towerを生成する。

従来のgeneric二分岐は互換APIとして残し、このファイルの一本化定理を
今後のSpecial C3排除の主入口とする。
-/

namespace CollatzSecondLayer3

open CollatzCore

/--
非有界軌道上のsource-preserving Special C3 towerが存在すること。

`FutureMinimumSpecialC3TowerData`自身が非有界性、future-minimum anchor、
各長さのfirst-deferred normalization、terminal Special C3を保持するため、
ここでは非有界性を重複して外側へ持たせない。
-/
def HasSourcePreservingSpecialC3Tower : Prop :=
  ∃ O : OddOrbit, Nonempty (FutureMinimumSpecialC3TowerData O)

/--
非有界軌道の任意のfuture-minimumは、source-preserving Special C3 towerを生成する。

deep lower-replay側へ分岐した場合は、生成履歴付きtowerの排除定理に反する。
-/
theorem futureMinimum_sourcePreservingSpecialC3Tower
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (FutureMinimumSpecialC3TowerData O) := by
  rcases
      futureMinimum_source_preserving_obstruction_dichotomy
        O hU anchor hmin with
    hSpecial | hDeep
  · exact hSpecial
  · rcases hDeep with ⟨D⟩
    exact False.elim
      (no_futureMinimumDeepLowerReplayTower D)

/--
一つの非有界odd-only軌道から、標準future-minimumを用いて
source-preserving Special C3 towerを直接構成する。
-/
theorem unboundedOrbit_sourcePreservingSpecialC3Tower_direct_on
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (FutureMinimumSpecialC3TowerData O) := by
  let anchor : ℕ := O.tailMinIndex 0
  have hmin : O.FutureMinimumAt anchor := by
    simpa [anchor] using O.futureMinimumAt_tailMinIndex 0
  exact
    futureMinimum_sourcePreservingSpecialC3Tower
      O hU anchor hmin

/--
非有界odd-only軌道の存在を、source-preserving Special C3 towerへ直接還元する。

これが今後の非有界側の主還元であり、deep lower-replay枝やgeneric忘却を経由しない。
-/
theorem unboundedOrbit_sourcePreservingSpecialC3Tower_direct
    (hU : HasUnboundedOddOrbit) :
    HasSourcePreservingSpecialC3Tower := by
  rcases hU with ⟨O, hO⟩
  exact
    ⟨O, unboundedOrbit_sourcePreservingSpecialC3Tower_direct_on O hO⟩

/-- source-preserving Special C3 towerをgeneric Special C3 towerへ忘却する。 -/
theorem hasGenericSpecialC3Tower_of_sourcePreserving
    (hS : HasSourcePreservingSpecialC3Tower) :
    HasGenericSpecialC3Tower := by
  rcases hS with ⟨O, ⟨S⟩⟩
  exact ⟨O, S.unbounded, ⟨S.toGeneric⟩⟩

/--
互換用のgeneric単一対象還元。
主証明ではsource-preserving towerを使い、必要な場合にだけgenericへ忘却する。
-/
theorem unboundedOrbit_genericSpecialC3Tower_direct
    (hU : HasUnboundedOddOrbit) :
    HasGenericSpecialC3Tower :=
  hasGenericSpecialC3Tower_of_sourcePreserving
    (unboundedOrbit_sourcePreservingSpecialC3Tower_direct hU)

/--
source-preserving Special C3 towerを排除すれば、非有界odd-only軌道は存在しない。
-/
theorem no_unbounded_odd_orbit_of_sourcePreservingSpecialC3_exclusion
    (hSpecial : ¬ HasSourcePreservingSpecialC3Tower) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  exact hSpecial
    (unboundedOrbit_sourcePreservingSpecialC3Tower_direct hU)

end CollatzSecondLayer3
