import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalFiniteXiIdentity

/-!
# Explicit critical packet -> StrongBoundaryLopezStollMatch

ここまでの object を一本につなぐ。

  CriticalContinuedFractionData
        ↓
  CriticalChristoffelPacket
        ↓
  CriticalSturmianStrongOverlap
        ↓
  CriticalSturmianFiniteXiBridge
        ↓
  CriticalFiniteXiIdentity
        ↓
  StrongBoundaryLopezStollMatch

最後の `CriticalFiniteXiIdentity -> StrongBoundaryLopezStollMatch` は
このファイルで完全に閉じる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace CriticalFiniteXiIdentity

/-- finite Xi identity family から existing strong matching interface を構成する。 -/
theorem toStrongBoundaryLopezStollMatch
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D)
    (I : CriticalFiniteXiIdentity D) :
    StrongBoundaryLopezStollMatch C.toLopezStollInstantiation := by
  refine ⟨?_⟩
  intro j e R hjStart hPrecision hCandidate
  change
    MatchesAtTwoPower e
      (correctedChristoffelP D j)
      (correctedChristoffelQ D j)
      R
  exact I.matches_of_candidate hjStart hPrecision hCandidate

end CriticalFiniteXiIdentity

namespace CriticalSturmianFiniteXiBridge

/-- overlap -> finite Xi bridge まで得られれば strong matching は直ちに完成する。 -/
theorem toStrongBoundaryLopezStollMatch
    {D : CriticalContinuedFractionData}
    (C : CriticalChristoffelPacket D)
    {O : CriticalSturmianStrongOverlap D}
    (B : CriticalSturmianFiniteXiBridge D O) :
    StrongBoundaryLopezStollMatch C.toLopezStollInstantiation :=
  B.finiteIdentity.toStrongBoundaryLopezStollMatch C

end CriticalSturmianFiniteXiBridge

/--
strong matching construction に必要な combinatorial data をまとめた packet。

`overlapToFiniteXi` が唯一の genuine finite-identity bridge で、
それ以降は pure Lean plumbing である。
-/
structure CriticalStrongMatchConstruction
    (D : CriticalContinuedFractionData)
    (C : CriticalChristoffelPacket D) where
  overlap : CriticalSturmianStrongOverlap D
  overlapToFiniteXi :
    CriticalSturmianFiniteXiBridge D overlap

namespace CriticalStrongMatchConstruction

/-- 完成した construction packet から strong Boundary A matching を得る。 -/
theorem toStrongBoundaryLopezStollMatch
    {D : CriticalContinuedFractionData}
    {C : CriticalChristoffelPacket D}
    (X : CriticalStrongMatchConstruction D C) :
    StrongBoundaryLopezStollMatch C.toLopezStollInstantiation :=
  X.overlapToFiniteXi.toStrongBoundaryLopezStollMatch C

/-- strong construction は既存 coarse matching も自動的に含む。 -/
theorem toBoundaryLopezStollMatch
    {D : CriticalContinuedFractionData}
    {C : CriticalChristoffelPacket D}
    (X : CriticalStrongMatchConstruction D C) :
    BoundaryLopezStollMatch C.toLopezStollInstantiation :=
  (X.toStrongBoundaryLopezStollMatch).toBoundaryLopezStollMatch
    C.toPreviousDenominatorStrict

end CriticalStrongMatchConstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
