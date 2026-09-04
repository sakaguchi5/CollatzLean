import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueSearchState
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCleanDirectEndpointResidue
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCleanActualFerrersDeficitBridge

/-!
# 第3例探索 clean D3 集約

D0/D1 の full critical-prefix defect residue と、actual Ferrers deficit の右剰余を
Case II 非依存の direct endpoint equation で結ぶ。

旧 D3 のように `criticalizationBoundaryDigit` で42桁を一つずつ選ばない。
この層が保持するのは

* D1 の `fullDefectModTwo`
* D1 の `fullDefectModThree`
* Ferrers deficit の `mod 3^42`
* そこから一発で復元した endpoint の `mod 3^42`

だけである。

なお actual Ferrers deficit 自体の「高速 evaluator」は次段で差し替え可能である。
このファイルでは exact semantics を `actualFerrersBands` へ固定し、
高速 evaluator が最終的に一致すべき仕様を明確にする。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/-- clean D3 が hot path へ渡す有限状態。 -/
@[ext]
structure ThirdExampleD3CleanPacket where
  defectState : ThirdExampleResidueSearchState
  deficitModThree : ZMod thirdExampleRightModulus
  endpointModThree : ZMod thirdExampleRightModulus
  deriving DecidableEq

/--
D1 state と deficit residue から clean D3 packet を作る。
証明 object は field に持たない。
-/
def thirdExampleD3CleanPacket
    (start : ℤ)
    (deficitModThree : ZMod thirdExampleRightModulus) :
    ThirdExampleD3CleanPacket :=
  {
    defectState := thirdExampleResidueSearchState start
    deficitModThree := deficitModThree
    endpointModThree :=
      thirdExampleCleanEndpointResidueOfDeficit deficitModThree
  }

@[simp] theorem thirdExampleD3CleanPacket_defectState
    (start : ℤ)
    (d : ZMod thirdExampleRightModulus) :
    (thirdExampleD3CleanPacket start d).defectState =
      thirdExampleResidueSearchState start := rfl

@[simp] theorem thirdExampleD3CleanPacket_deficitModThree
    (start : ℤ)
    (d : ZMod thirdExampleRightModulus) :
    (thirdExampleD3CleanPacket start d).deficitModThree = d := rfl

@[simp] theorem thirdExampleD3CleanPacket_endpointModThree
    (start : ℤ)
    (d : ZMod thirdExampleRightModulus) :
    (thirdExampleD3CleanPacket start d).endpointModThree =
      thirdExampleCleanEndpointResidueOfDeficit d := rfl

/--
actual Ferrers deficit の右剰余像。
これは proof-side の仕様値であり、巨大セル列を hot path で直接評価することを
要求する定義ではない。
-/
def thirdExampleActualFerrersDeficitModThree
    (w : Word) : ZMod thirdExampleRightModulus :=
  (integerFerrersDeficit thirdExampleTargetP (actualFerrersBands w) :
    ZMod thirdExampleRightModulus)

/--
真の第3例 certificate では certificate deficit と actual Ferrers deficit の
右剰余像が一致する。
-/
theorem thirdExampleActualFerrersDeficitModThree_eq_certificate
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    thirdExampleActualFerrersDeficitModThree w =
      (deficit : ZMod thirdExampleRightModulus) := by
  unfold thirdExampleActualFerrersDeficitModThree
  symm
  exact
    cleanExactCriticalGapOne_deficit_mod_eq_actualFerrersDeficitMod
      thirdExampleRightModulus C

/--
certificate deficit を与えた clean D3 packet の soundness。
左右 full defect は D1/D0 の exact state、endpoint は actual gap-one endpoint の
`mod 3^42` 像になる。
-/
theorem thirdExampleD3CleanPacket_exact
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    let D := thirdExampleD3CleanPacket
      (gapOneStartValue m : ℤ)
      (deficit : ZMod thirdExampleRightModulus)
    D.defectState.fullDefectModTwo =
        ((thirdExampleExactCanonicalFullState
          (gapOneStartValue m : ℤ) : ℤ) : ZMod thirdExampleLeftModulus) ∧
    D.defectState.fullDefectModThree =
        ((thirdExampleExactCanonicalFullState
          (gapOneStartValue m : ℤ) : ℤ) : ZMod thirdExampleRightModulus) ∧
    D.endpointModThree =
      (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
  dsimp only
  constructor
  · exact
      thirdExampleResidueSearchState_left_exact
        CertL (gapOneStartValue m : ℤ)
  · constructor
    · exact
        thirdExampleResidueSearchState_right_exact
          CertR (gapOneStartValue m : ℤ)
    · exact thirdExampleCleanEndpointResidueOfDeficit_exact CertR C

/--
actual Ferrers deficit の仕様値を直接入力した版。
次段の compressed deficit evaluator は、この入力値と同じ residue を返すことだけを
証明すれば clean D3 全体へ接続できる。
-/
theorem thirdExampleD3CleanPacket_of_actualFerrersDeficit_exact
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    let D := thirdExampleD3CleanPacket
      (gapOneStartValue m : ℤ)
      (thirdExampleActualFerrersDeficitModThree w)
    D.endpointModThree =
      (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
  dsimp only
  rw [thirdExampleActualFerrersDeficitModThree_eq_certificate C]
  exact thirdExampleCleanEndpointResidueOfDeficit_exact CertR C

end ThirdExampleSearch
end CSTMicro
end Collatz2
