import CollatzLean.CollatzSecondLayer3.FutureMinimumDeepLowerReplay
import CollatzLean.CollatzSupport.CofinalSelection

/-!
# future-minimumからgeneric obstruction towerへ

長さ`q = j+1`ごとのterminal二分岐を一つのfamilyにまとめる。
Special C3がcofinalなら部分列を選び、endpointがある固定多項式以下でcofinalか否かで
polynomial / superPolynomial profileへ分類する。
Special C3がcofinalでなければ、十分後の全項がdeep lower replayとなる。

最終generic二分岐は、生成履歴付きtowerとcoherent towerを経由して構成する。
従来のterminal family APIも互換用として残す。
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

/-- terminal familyからgeneric Special C3またはdeep lower-replay towerを抽出する。 -/
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
非有界軌道の任意のfuture-minimumはgeneric最終二対象の一方を生成する。
このAPIは生成履歴付き第1層とcoherent第2層を経由してgenericへ忘却する。
-/
theorem futureMinimum_generic_obstruction_dichotomy
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) := by
  exact
    futureMinimum_generic_obstruction_dichotomy_via_history
      O hU anchor hmin

/-- 非有界軌道は外部密度やBaker入力なしでgeneric二対象へ落ちる。 -/
theorem unboundedOrbit_generic_dichotomy_direct_on
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) := by
  let anchor := O.tailMinIndex 0
  have hmin : O.FutureMinimumAt anchor := by
    simpa [anchor] using O.futureMinimumAt_tailMinIndex 0
  exact futureMinimum_generic_obstruction_dichotomy O hU anchor hmin

/-- 非有界odd-only軌道の存在をgeneric二対象へ直接還元する。 -/
theorem unboundedOrbit_generic_dichotomy_direct
    (hU : HasUnboundedOddOrbit) :
    HasGenericSpecialC3Tower ∨ HasGenericDeepLowerReplayTower := by
  rcases hU with ⟨O, hO⟩
  rcases unboundedOrbit_generic_dichotomy_direct_on O hO with hS | hD
  · exact Or.inl ⟨O, hO, hS⟩
  · exact Or.inr ⟨O, hO, hD⟩

end CollatzSecondLayer3
