import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDeficitThreeAdicNonvanishing
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleVisibleDefectDecoder68
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleHensel42ResidueCompleteness

/-!
# 第3例低枝探索 4: 同じ exact candidate 上で左右 collar を同期する

このファイルでは未証明の decoder completeness を捏造しない。
証明するのは、同じ `ExactCriticalGapOneFerrersCertificate C` から同時に

* 低14枝 `(j,a)`,
* exact 2-adic valuation,
* `m mod 2^(a+1)` branch residue,
* 左 `2^68` visible decoder の有限入力,
* `3^42 ∤ deficit`,
* actual endpoint の exact 42桁 Hensel residue,
* deficit から直接復元した右 endpoint residue,

が得られることである。

これにより左探索と右探索が別 candidate を見てしまうことを防ぐ。
なお `thirdExampleVisibleDefectDecoder68` の全 entry が actual profile と一致することは、
この theorem では主張しない。そこは別の completeness theorem が必要である。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch

open DoubleDecomposition
open CertifiedHigh

/--
低枝 exact candidate が同時に持つ左右 collar の有限情報。

右 Hensel residue は endpoint が `3^42` 未満なので actual endpoint 整数そのものになる。
-/
theorem thirdExample_lowBranch_leftRightCollar_bridge
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : Nat}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    ∃ j a : Nat,
      ThirdExampleFirstCriticalDefectAt w j ∧
      (j, a) ∈ thirdExampleLow14FirstDefectPairs ∧
      Word.ExactTwoPowZ a (deficit : Int) ∧
      m % branchModulus a = branchResidue a ∧
      (thirdExampleVisibleDefectDecoder68
          (deficit : ZMod thirdExampleLeftModulus)).length ≤ 68 ∧
      ¬ (3 : Nat) ^ 42 ∣ deficit ∧
      thirdExampleHensel42Residue (gapOneEndpointValue m) =
        gapOneEndpointValue m ∧
      thirdExampleCleanEndpointResidueOfDeficit
          (deficit : ZMod thirdExampleRightModulus) =
        (thirdExampleHensel42Residue (gapOneEndpointValue m) :
          ZMod thirdExampleRightModulus) := by
  obtain ⟨j, F⟩ := thirdExampleFirstCriticalDefect_exists R CertL C
  let a := Word.prefixTwoDepth w j
  have hPair :
      (j, a) ∈ thirdExampleLow14FirstDefectPairs := by
    dsimp [a]
    exact thirdExample_firstDefect_low14_pair R CertL C F
  have hExact : Word.ExactTwoPowZ a (deficit : Int) := by
    dsimp [a]
    exact thirdExampleFirstDefect_exactTwoPow C F
  have hLe : a ≤ 37 := by
    dsimp [a]
    exact thirdExample_firstDefect_height_le_37 R CertL C F
  have hResidue :
      m % branchModulus a = branchResidue a := by
    apply candidate_branch_residue_of_lt_68 CertL C F
    · omega
    · rfl
  have hLeftLength :
      (thirdExampleVisibleDefectDecoder68
          (deficit : ZMod thirdExampleLeftModulus)).length ≤ 68 :=
    thirdExampleVisibleDefectDecoder68_length_le _
  have hThreeNonzero : ¬ (3 : Nat) ^ 42 ∣ deficit :=
    thirdExample_deficit_not_dvd_threePow42 R CertR C
  have hEndpointLt := thirdExampleEndpoint_lt_threePow42 R C
  have hHensel :
      thirdExampleHensel42Residue (gapOneEndpointValue m) =
        gapOneEndpointValue m := by
    rw [thirdExampleHensel42Residue_eq_mod]
    exact Nat.mod_eq_of_lt hEndpointLt
  have hRight :=
    thirdExampleCleanEndpointResidueOfDeficit_exact CertR C
  refine ⟨j, a, F, hPair, hExact, hResidue, hLeftLength,
    hThreeNonzero, hHensel, ?_⟩
  simpa [hHensel] using hRight

end Collatz2.CSTMicro.ThirdExampleSearch
