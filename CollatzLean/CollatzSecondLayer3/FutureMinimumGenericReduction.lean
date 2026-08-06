import CollatzLean.CollatzSecondLayer3.SourcePreservingSpecialC3Reduction
import CollatzLean.CollatzSupport.CofinalSelection

/-!
# future-minimumからgeneric obstruction towerへ

このファイルのterminal family APIは、生成履歴を持たない旧generic還元との互換用に残す。

非有界軌道に対する現行の主還元は、
`SourcePreservingSpecialC3Reduction`の

`HasUnboundedOddOrbit → HasSourcePreservingSpecialC3Tower`

である。generic APIが必要な場合に限り、source-preserving Special C3 towerを
`GenericSpecialC3TowerData`へ忘却する。

従来のgeneric二分岐定理も互換用として残すが、deep lower-replay towerの
source-preserving排除により、direct経路では常にSpecial C3側が成立する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore

/-- 一つのfuture-minimumから得られる全正長terminal family。 -/
structure FutureMinimumTerminalFamilyData (O : OddOrbit) where
  start : ℕ → ℕ
  outcome : ∀ j : ℕ,
    Nonempty (GenericDeepLowerReplayAt O (start j) (j + 1)) ∨
      Nonempty (SpecialC3At O (start j) (j + 1))

/-- 非有界軌道のfuture-minimumから標準terminal familyを構成する。 -/
noncomputable def futureMinimumTerminalFamily
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    FutureMinimumTerminalFamilyData O where
  start := fun j =>
    futureMinimumTerminalStart O hU anchor (j + 1) hmin (by omega)
  outcome := fun j => by
    simpa using
      futureMinimum_terminal_dichotomy
        O hU anchor (j + 1) hmin (by omega)

namespace FutureMinimumTerminalFamilyData

/--
任意のterminal familyからgeneric Special C3またはdeep lower-replay towerを抽出する。
この定理はsource情報を持たないfamilyに対する互換APIである。
-/
theorem toGenericTowerDichotomy
    {O : OddOrbit}
    (F : FutureMinimumTerminalFamilyData O) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) := by
  classical
  let IsSpecial : ℕ → Prop :=
    fun j => Nonempty (SpecialC3At O (F.start j) (j + 1))
  by_cases hSpecial : Cofinally IsSpecial
  · let select₁ : ℕ → ℕ := Cofinally.select IsSpecial hSpecial
    have hselect₁Special : ∀ j : ℕ, IsSpecial (select₁ j) := by
      intro j
      exact Cofinally.select_spec IsSpecial hSpecial j
    let Bound : ℕ → ℕ → ℕ → Prop :=
      fun K A j =>
        O.value (F.start (select₁ j) + (select₁ j + 1)) ≤
          K * ((select₁ j + 1) + 1) ^ A
    by_cases hPolynomial :
        ∃ K A : ℕ, Cofinally (Bound K A)
    · obtain ⟨K, A, hBound⟩ := hPolynomial
      let select₂ : ℕ → ℕ :=
        Cofinally.select (Bound K A) hBound
      left
      refine ⟨{
        start := fun j => F.start (select₁ (select₂ j))
        length := fun j => select₁ (select₂ j) + 1
        special := ?_
        lengths_tend_to_infinity := ?_
        growth := .polynomial K A ?_
      }⟩
      · intro j
        exact Classical.choice (hselect₁Special (select₂ j))
      · intro M
        refine ⟨M, ?_⟩
        intro j hj
        have h₂ : j ≤ select₂ j :=
          Cofinally.select_ge (Bound K A) hBound j
        have h₁ : select₂ j ≤ select₁ (select₂ j) :=
          Cofinally.select_ge IsSpecial hSpecial (select₂ j)
        omega
      · intro j
        change Bound K A (select₂ j)
        exact Cofinally.select_spec (Bound K A) hBound j
    · left
      refine ⟨{
        start := fun j => F.start (select₁ j)
        length := fun j => select₁ j + 1
        special := fun j => Classical.choice (hselect₁Special j)
        lengths_tend_to_infinity := ?_
        growth := .superPolynomial ?_
      }⟩
      · intro M
        refine ⟨M, ?_⟩
        intro j hj
        have hs : j ≤ select₁ j :=
          Cofinally.select_ge IsSpecial hSpecial j
        omega
      · intro K A
        have hnot : ¬ Cofinally (Bound K A) := by
          intro h
          exact hPolynomial ⟨K, A, h⟩
        obtain ⟨J, hJ⟩ :=
          Cofinally.eventually_not_of_not (Bound K A) hnot
        refine ⟨J, ?_⟩
        intro j hj
        have hn := hJ j hj
        dsimp [Bound] at hn ⊢
        omega
  · obtain ⟨N, hN⟩ :=
      Cofinally.eventually_not_of_not IsSpecial hSpecial
    right
    refine ⟨{
      start := fun j => F.start (N + j)
      length := fun j => N + j + 1
      deep := ?_
      lengths_tend_to_infinity := ?_
    }⟩
    · intro j
      exact Classical.choice <|
        (F.outcome (N + j)).resolve_right (by
          simpa [IsSpecial] using
            hN (N + j) (by omega))
    · intro M
      refine ⟨M, ?_⟩
      intro j hj
      omega

end FutureMinimumTerminalFamilyData

/--
非有界軌道のfuture-minimumからgeneric Special C3 towerを得る。
source-preserving towerを構成した後、最後にだけgenericへ忘却する。
-/
theorem futureMinimum_genericSpecialC3Tower
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (GenericSpecialC3TowerData O) := by
  rcases
      futureMinimum_sourcePreservingSpecialC3Tower
        O hU anchor hmin with
    ⟨S⟩
  exact ⟨S.toGeneric⟩

/--
従来互換のgeneric二分岐。
source-preserving deep lower-replay towerが排除済みなので、常に左枝を返す。
-/
theorem futureMinimum_generic_obstruction_dichotomy
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) :=
  Or.inl (futureMinimum_genericSpecialC3Tower O hU anchor hmin)

/-- 一つの非有界odd-only軌道からgeneric Special C3 towerを得る。 -/
theorem unboundedOrbit_genericSpecialC3Tower_direct_on
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (GenericSpecialC3TowerData O) := by
  rcases
      unboundedOrbit_sourcePreservingSpecialC3Tower_direct_on
        O hU with
    ⟨S⟩
  exact ⟨S.toGeneric⟩

/--
従来互換の軌道上generic二分岐。
現行のdirect経路では常にSpecial C3側が成立する。
-/
theorem unboundedOrbit_generic_dichotomy_direct_on
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) :=
  Or.inl (unboundedOrbit_genericSpecialC3Tower_direct_on O hU)

/--
従来互換の存在レベルgeneric二分岐。
主還元`unboundedOrbit_sourcePreservingSpecialC3Tower_direct`から忘却して左枝を得る。
-/
theorem unboundedOrbit_generic_dichotomy_direct
    (hU : HasUnboundedOddOrbit) :
    HasGenericSpecialC3Tower ∨ HasGenericDeepLowerReplayTower :=
  Or.inl (unboundedOrbit_genericSpecialC3Tower_direct hU)

end CollatzSecondLayer3
