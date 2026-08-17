import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelPacketClosure
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianFiniteScanIdentity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalStrongMatchConstruction

/-!
# Steps 1--5: end-to-end strong matching proof packet

1. corrected Christoffel packet の elementary fields を orientation から閉じる。
2. continued-fraction parity orientation を明示する。
3. critical-height corridor から strong Sturmian overlap を導く。
4. odd/even finite scan identities から finite Xi bridge を作る。
5. existing pipeline により `StrongBoundaryLopezStollMatch` を完成する。

このファイル以降、A strong matching の未証明数学は

* actual CF から `CriticalBeattyConvergentCorridor` を作ること
* overlap + finite inverse scan から `CriticalSturmianFiniteScanIdentity` を作ること

の二点に局在する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure CriticalStrongMatchProof
    (D : OrientedCriticalContinuedFractionData) where
  corridor : CriticalBeattyConvergentCorridor D.base
  finiteScan :
    CriticalSturmianFiniteScanIdentity
      D.base corridor.toCriticalSturmianStrongOverlap


namespace CriticalStrongMatchProof


/--
Step 1:
向き付けられた critical continued-fraction data から、
corrected López--Stoll packet を明示的に構成する。

この構成は `CriticalStrongMatchProof` の追加証明データには依存せず、
`D` だけから得られる。
-/
theorem christoffelPacket
    (D : OrientedCriticalContinuedFractionData) :
    CriticalChristoffelPacket D.base :=
  D.toCriticalChristoffelPacket


/--
Step 3:
Beatty/convergent height corridor から strong overlap を得る。
-/
theorem strongOverlap
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalStrongMatchProof D) :
    CriticalSturmianStrongOverlap D.base :=
  X.corridor.toCriticalSturmianStrongOverlap


/--
Step 4:
branchwise finite scan identity から、
finite Ξ bridge を得る。
-/
theorem finiteXiBridge
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalStrongMatchProof D) :
    CriticalSturmianFiniteXiBridge D.base X.strongOverlap := by
  exact X.finiteScan.toCriticalSturmianFiniteXiBridge


/--
Steps 1--5 に必要なデータをまとめ、
既存の strong matching construction packet を構成する。
-/
theorem toCriticalStrongMatchConstruction
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalStrongMatchProof D) :
    CriticalStrongMatchConstruction
      D.base (christoffelPacket D) := {
  overlap := X.strongOverlap
  overlapToFiniteXi := X.finiteXiBridge
}


/--
Step 5:
strong construction から、
実際の strong Boundary A matching certificate を得る。
-/
theorem toStrongBoundaryLopezStollMatch
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalStrongMatchProof D) :
    StrongBoundaryLopezStollMatch
      (christoffelPacket D).toLopezStollInstantiation := by
  exact
    X.toCriticalStrongMatchConstruction.toStrongBoundaryLopezStollMatch


/--
strong matching route から、
従来の coarse Boundary matching route も自動的に得られる。
-/
theorem toBoundaryLopezStollMatch
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalStrongMatchProof D) :
    BoundaryLopezStollMatch
      (christoffelPacket D).toLopezStollInstantiation := by
  exact
    X.toCriticalStrongMatchConstruction.toBoundaryLopezStollMatch

end CriticalStrongMatchProof

end ExternalArithmetic
end CSTMicro
end Collatz2
