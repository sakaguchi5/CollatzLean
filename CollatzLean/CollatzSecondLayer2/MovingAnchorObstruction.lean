import CollatzLean.CollatzSecondLayer2.FirstCrossing
import CollatzLean.CollatzSecondLayer2.CaptureRefinement

/-!
# moving-anchor expanding-block obstruction

任意に長い全proper-prefix膨張blockがmoving future-minimum anchor上に存在するが、
同じ軌道上にSpecial C3列はまだ存在しない、という残余構造を明示する。
これはone-sided meanderそのものではなく、開始位置が右へ移動し続ける障害である。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- moving first-crossing列がSpecial C3へ接続されていない残余障害。 -/
structure MovingAnchorExpandingBlockObstructionData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  noSpecialC3 : ¬ HasSpecialC3From crossing

namespace MovingAnchorExpandingBlockObstructionData

/-- 各moving anchorはfuture-minimum。 -/
theorem futureMinimum
    {O : OddOrbit}
    (D : MovingAnchorExpandingBlockObstructionData O)
    (j : ℕ) :
    O.FutureMinimumAt (D.crossing.minima.index j) :=
  D.crossing.minima.futureMinimum j

/-- 各blockのすべてのproper prefixは膨張する。 -/
theorem properPrefixesExpanding
    {O : OddOrbit}
    (D : MovingAnchorExpandingBlockObstructionData O)
    (j : ℕ) :
    ProperPrefixesExpanding
      (O.segmentWord
        (D.crossing.minima.index j)
        (D.crossing.crossingLength j)) :=
  (D.crossing.crossing j).properExpanding

/-- 各moving anchor自体はone-sided meanderではない。 -/
theorem not_meander_at_anchor
    {O : OddOrbit}
    (D : MovingAnchorExpandingBlockObstructionData O)
    (j : ℕ) :
    ¬ MeanderAt O (D.crossing.minima.index j) := by
  intro hM
  let p := D.crossing.crossingLength j
  have hp : 0 < p := (D.crossing.crossing j).length_pos
  have hE :
      Expanding (O.segmentWord (D.crossing.minima.index j) p) :=
    hM p hp
  have hC :
      Contracting (O.segmentWord (D.crossing.minima.index j) p) :=
    (D.crossing.crossing j).terminalContracting
  unfold Expanding at hE
  unfold Contracting at hC
  omega

/--
obstruction上の任意のpolynomial prepared refinementではcaptureがpersistentに残る。
そうでなければ`persistentCapture_or_specialC3`がSpecial C3 refinementを生成し、
`noSpecialC3`に反する。
-/
theorem persistentCapture_of_polynomialRefinement
    {O : OddOrbit}
    (D : MovingAnchorExpandingBlockObstructionData O)
    (R : PolynomialPreparedRefinementSequence D.crossing) :
    R.HasPersistentCapture := by
  rcases R.persistentCapture_or_specialC3 with hcap | hspecial
  · exact hcap
  · exact False.elim (D.noSpecialC3 hspecial)

/-- obstructionの膨張block長は任意に大きくなる。 -/
theorem lengths_tend_to_infinity
    {O : OddOrbit}
    (D : MovingAnchorExpandingBlockObstructionData O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < D.crossing.crossingLength j :=
  D.crossing.lengths_tend_to_infinity

end MovingAnchorExpandingBlockObstructionData


/--
任意のmoving first-crossing列は、同じ軌道上のSpecial C3列か、
Special C3が存在しないmoving-anchor obstructionのどちらかへ完全分岐する。
-/
theorem specialC3_or_movingAnchorObstruction
    {O : OddOrbit}
    (F : MovingFirstCrossingData O) :
    HasSpecialC3From F ∨
      Nonempty (MovingAnchorExpandingBlockObstructionData O) := by
  classical
  by_cases hC3 : HasSpecialC3From F
  · exact Or.inl hC3
  · exact Or.inr ⟨⟨F, hC3⟩⟩

/-- 指定軌道上にmoving-anchor expanding-block obstructionが存在する。 -/
def HasMovingAnchorExpandingBlockObstructionOn (O : OddOrbit) : Prop :=
  Nonempty (MovingAnchorExpandingBlockObstructionData O)

/-- 非有界odd-only軌道上にmoving-anchor obstructionが存在する。 -/
def HasMovingAnchorExpandingBlockObstruction : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧ HasMovingAnchorExpandingBlockObstructionOn O

end CollatzSecondLayer2
