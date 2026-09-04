import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitEvaluator
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleGapOneAffineCompatibility
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedIntervalFerrersDefectBridge

/-!
# 第3例探索: finite deficit table の soundness 境界

この層は二つを分離する。

1. 既存 exact theorem が actual attached interval の Ferrers deficit を与えること。
2. table row の `deficitModThree` がその actual deficit の `mod 3^42` 像であること。

2 を各 `(r,d,w)` に対して計算可能に埋めれば、最後のファイルでは proof object を捨てて
`native_decide` だけで survivor list を空にできる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open ExternalArithmetic
open MultiCorner

/--
一枝の table row が exact deficit を表していること。
この Prop は proof-side にだけ置き、runtime row 自体には含めない。
-/
def ThirdExampleFiniteDeficitRowRepresents
    (R : ThirdExampleFiniteDeficitRow)
    (deficit : ℕ) : Prop :=
  R.deficitModThree = (deficit : ZMod thirdExampleRightModulus)

/--
D2 packet が exact gap-one data を表し、row が exact Ferrers deficit を表すなら、
affine compatibility checker は必ず true になる。

この theorem が「native verifier が actual candidate を落としてはいけない」方向の核。
-/
theorem thirdExampleFiniteDeficitCompatible_of_exactGapOne
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (R : ThirdExampleFiniteDeficitRow)
    (hR : ThirdExampleFiniteDeficitRowRepresents R deficit) :
    thirdExampleFiniteDeficitCompatible
        (thirdExampleD2FinitePacket
          (gapOneStartValue m : ℤ)
          (gapOneEndpointValue m))
        R.deficitModThree = true := by
  rw [thirdExampleFiniteDeficitCompatible_eq_true_iff]
  have hFull :
      (thirdExampleD2FinitePacket
          (gapOneStartValue m : ℤ)
          (gapOneEndpointValue m)).defectState.fullDefectModThree =
        ((thirdExampleExactCanonicalFullState
            (gapOneStartValue m : ℤ) : ℤ) :
          ZMod thirdExampleRightModulus) := by
    simpa using
      thirdExampleResidueSearchState_right_exact
        CertR (gapOneStartValue m : ℤ)
  have hEndpointVal :=
    thirdExampleD2FinitePacket_endpointModThree_eq_zmod_val
      (gapOneStartValue m : ℤ)
      (gapOneEndpointValue m)
  have hExactState :=
    thirdExampleExactCanonicalFullState_eq_criticalPrefixDefectZ
      (gapOneStartValue m : ℤ)
  have hBeta : thirdExampleTargetBeta = beattyIndex thirdExampleTargetP := by
    unfold thirdExampleTargetBeta
    have h := C.terminalDepth_eq
    omega
  have hCompat :=
    gapOneEndpoint_fullDefect_affineCompatibility_mod
      thirdExampleRightModulus C
  rw [hBeta]
  rw [hR]
  rw [hFull]
  rw [hExactState]
  have hEndpointCast :
      ((thirdExampleD2FinitePacket
          (gapOneStartValue m : ℤ)
          (gapOneEndpointValue m)).endpointModThree :
        ZMod thirdExampleRightModulus) =
      (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
    have hCast := congrArg
      (fun n : ℕ => (n : ZMod thirdExampleRightModulus))
      hEndpointVal
    simpa using hCast
  rw [hEndpointCast]
  exact hCompat

/--
既存の actual attached interval theorem を、finite-deficit 層から直接参照する wrapper。
ここでは新しい deficit formula を捏造せず、既存 theorem をそのまま公開する。
-/
theorem actualAttachedFerrersDeficit_exact
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let P := M.toPureBProfileObstruction hL
    let ww := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    (integerFerrersDeficitInterval ww u n : ℤ) =
      (3 : ℤ) ^ (P.m - (u + n)) *
        straightCheckpointFerrersBracketZ P.h u n := by
  exact AttachedTwoCornerPacket.integerFerrersDeficitInterval_eq_attached_straight_formula
    M hL A hEnd

end ThirdExampleSearch
end CSTMicro
end Collatz2
