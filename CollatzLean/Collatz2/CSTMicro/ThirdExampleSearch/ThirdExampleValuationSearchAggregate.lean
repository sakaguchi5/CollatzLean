import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleEndpointBound42
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleGapFactors
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDeficitTwoAdicNonvanishing
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFirstDefectOneCell
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.FerrersDeficitValuationPeeling
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleVisibleDefectDecoder68
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDecoderIndependentProfileBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleRightCompressedDeficitMerge

/-!
# 第3例探索 valuation-search 集約

1〜8を一つに束ねる clean aggregate。

依存順は次の通り。

1. range certificate から start/end の有限化。
2. target gap の小因子による `m` 非依存 congruence。
3. `2^68 ∤ deficit`。
4. 最初の defect は一セル、かつ左68 collar 内。
5. residual の exact 2進 valuation から次 visible defect を読む一般補題。
6. 最大68回の executable decoder。
7. decoder entry と `IndependentCriticalDefectProfile` の接続。
8. maximal horizontal bands の右 `3^42` evaluator を clean D3 endpoint へ合流。

Case II / `PureBProfileObstruction` / Last41 は import しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/--
現在の clean pipeline が一つの exact candidate について同時に与える中心事実。
-/
theorem thirdExampleValuationSearch_coreFacts
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    (E : ThirdExampleRightBandEvaluator)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (Cover : MaximalHorizontalBandCover w) :
    gapOneEndpointValue m < thirdExampleRightModulus ∧
      ¬ (2 ^ 68 ∣ deficit) ∧
      (∃ j : ℕ,
        ThirdExampleFirstCriticalDefectAt w j ∧
          Word.criticalDefect w j = 1 ∧ j < 68) ∧
      (gap : ZMod thirdExampleGapFactorModulus) = 0 ∧
      thirdExampleCleanEndpointResidueOfDeficit
          (thirdExampleRightCompressedDeficit E
            (maximalHorizontalBands Cover)) =
        (gapOneEndpointValue m : ZMod thirdExampleRightModulus) ∧
      (thirdExampleCleanEndpointResidueOfDeficit
          (thirdExampleRightCompressedDeficit E
            (maximalHorizontalBands Cover))).val =
        gapOneEndpointValue m := by
  refine ⟨thirdExampleEndpoint_lt_threePow42 R C, ?_⟩
  refine ⟨thirdExampleDeficit_not_dvd_twoPow68 R CertL C, ?_⟩
  refine ⟨thirdExampleFirstDefect_exists_oneCell_and_visible R CertL C, ?_⟩
  refine ⟨thirdExampleCertificate_gap_eq_zero_mod C, ?_⟩
  refine ⟨thirdExampleRightCompressedEndpoint_exact E CertR C Cover, ?_⟩
  exact thirdExampleRightCompressedEndpoint_val_exact R E CertR C Cover

end ThirdExampleSearch
end CSTMicro
end Collatz2
