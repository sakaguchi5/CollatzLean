import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLowBranchCollarBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleRunBridge

/-!
# 第3例低枝探索 5: `familyCheck` を最後の fallback に限定する

低14枝ではまず first-defect / 2-adic / 3-adic collar で候補を削る。
それでも特定 valuation branch が残った場合だけ、既存の高速 `familyCheck` を使えばよい。

このファイルは新しい巨大 `native_decide` を要求しない。
任意の低枝 `a` について、もし

  familyCheck 1000 (rootFamily a) = true

が別途得られたなら、その branch の exact candidate は存在しない、という adapter だけを証明する。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

/--
低14枝の exact candidate に対する汎用 fallback。
first-defect height をそのまま branch index に使うため、手書きの低枝 residue table は不要。
-/
theorem thirdExample_lowBranch_impossible_of_familyCheck
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m j : Nat}
    (C : DoubleDecomposition.ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j)
    (hCheck :
      familyCheck 1000 (rootFamily (Word.prefixTwoDepth w j)) = true) :
    False := by
  let a := Word.prefixTwoDepth w j
  have hLe : a ≤ 37 := by
    dsimp [a]
    exact thirdExample_firstDefect_height_le_37 R CertL C F
  have hResidue :
      m % branchModulus a = branchResidue a := by
    apply candidate_branch_residue_of_lt_68 CertL C F
    · omega
    · rfl
  have hDrops : FamilyDrops (rootFamily a) 1000 := by
    apply familyCheck_sound
    simpa [a] using hCheck
  have hm : m < cutoff := R.multiplier_lt C
  have hw :=
    (DoubleDecomposition.gapOneParadoxical_of_exactCriticalFerrersCertificate C).1
  have hLen : 1000 < w.length := by
    have hp := C.oddSteps_eq
    change w.length = 6586818669 at hp
    omega
  exact checked_family_impossible
    hDrops hm hResidue hw C.minimal.2 hLen

/--
branch37 専用の薄い wrapper。
37を直接 `familyCheck` する必要が生じた場合だけ利用する。
-/
theorem thirdExample_branch37_impossible_of_familyCheck
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m j : Nat}
    (C : DoubleDecomposition.ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j)
    (h37 : Word.prefixTwoDepth w j = 37)
    (hCheck : familyCheck 1000 (rootFamily 37) = true) :
    False := by
  apply thirdExample_lowBranch_impossible_of_familyCheck R CertL C F
  simpa [h37] using hCheck

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
