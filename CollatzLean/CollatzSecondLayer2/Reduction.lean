import CollatzLean.CollatzSecondLayer2.MovingAnchorObstruction

/-!
# 非有界odd-only軌道の無条件三分岐

旧SecondLayerのterminal extractionやCylinder Upgradeを前提にせず、第一層から
再構成したfuture-minimumとfirst-crossingだけで、同一軌道上の三分岐を得る。

* actual one-sided meander
* zero-sync Special C3列
* Special C3へ接続されていないmoving-anchor expanding-block obstruction

第三枝は単なる論理的否定ではなく、future-minimum、first-crossing、
proper-prefix膨張、長さ発散をすべてデータとして保存する。
-/

namespace CollatzSecondLayer2

/--
一つの指定された非有界軌道に対する三分岐。
すべての枝は同じ`O`上のデータである。
-/
theorem unboundedOrbit_trichotomy_on
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (OneSidedMeanderData O) ∨
      HasSpecialC3On O ∨
      HasMovingAnchorExpandingBlockObstructionOn O := by
  classical
  let S : O.FutureMinimumSequence := O.futureMinimumSequence hU
  by_cases hM : ∃ j : ℕ, MeanderAt O (S.index j)
  · rcases hM with ⟨j, hj⟩
    exact Or.inl
      ⟨{
        unbounded := hU
        anchor := S.index j
        futureMinimum := S.futureMinimum j
        meander := hj
      }⟩
  · let F : MovingFirstCrossingData O :=
      movingFirstCrossingData_of_no_meander O hU S hM
    rcases specialC3_or_movingAnchorObstruction F with hC3 | hMoving
    · exact Or.inr (Or.inl ⟨F, hC3⟩)
    · exact Or.inr (Or.inr hMoving)

/--
非有界odd-only軌道の存在は、三つの最終障害のいずれかを与える。
-/
theorem unbounded_odd_orbit_trichotomy :
    HasUnboundedOddOrbit →
      HasOneSidedMeander ∨
      HasSpecialC3 ∨
      HasMovingAnchorExpandingBlockObstruction := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_trichotomy_on O hU with hM | hC3 | hMoving
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hC3⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hMoving⟩)

/-- 三枝をすべて排除できれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_three_exclusions
    (hMeander : ¬ HasOneSidedMeander)
    (hSpecial : ¬ HasSpecialC3)
    (hMoving : ¬ HasMovingAnchorExpandingBlockObstruction) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_trichotomy hU with h | h | h
  · exact hMeander h
  · exact hSpecial h
  · exact hMoving h

/--
同じ軌道上でmeanderとmoving obstructionを排除すれば、その軌道はSpecial C3列を持つ。
-/
theorem specialC3On_of_unbounded_of_no_meander_no_moving
    (O : OddOrbit)
    (hU : O.Unbounded)
    (hMeander : ¬ Nonempty (OneSidedMeanderData O))
    (hMoving : ¬ HasMovingAnchorExpandingBlockObstructionOn O) :
    HasSpecialC3On O := by
  rcases unboundedOrbit_trichotomy_on O hU with h | h | h
  · exact False.elim (hMeander h)
  · exact h
  · exact False.elim (hMoving h)

end CollatzSecondLayer2
