import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleSearchBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleHighBranchDispatch

/-!
指定commit 982d043e410a7cb75448ef133c6b3d9afc3ab8e3への追加。
高い11枝の認証済み有限探索から、first defect indexを24以下へ狭める途中版。
【未完成】中心定理にはsorryが2箇所ある。下の系もそのsorryに依存するため、
j≤24およびν₂(deficit)≤37の完成した証明として使用してはならない。
低い14枝の非存在を主張するファイルではない。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch
open DoubleDecomposition
open CertifiedHigh

/-- 高さ68未満、一セル、直前との狭義単調性を満たす高いroof位置。 -/
theorem thirdExample_highRoof_indices_checked :
    ∀ j : Fin 68, 24<j.val →
      Word.criticalHeight (j.val-1)<Word.criticalHeight j.val-1 →
      Word.criticalHeight j.val-1<68 →
      j.val ∈ [26,28,30,31,33,35,36,38,40,42,43] ∧
      Word.criticalHeight j.val-1 ∈ [67,65,62,59,56,54,51,48,46,43,40] := by
  decide

/-- 中心成果：第三例exact candidateのfirst defectは24列目以前にある。 -/
theorem thirdExample_firstDefect_index_le_24
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word} {deficit gap m : Nat}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    {j : Nat} (F : ThirdExampleFirstCriticalDefectAt w j) : j≤24 := by
  by_contra hnot
  have hjhi := thirdExampleFirstDefect_index_lt_68 R CertL C F
  have hhhi := thirdExampleFirstDefect_height_lt_68 R CertL C F
  have hcell := thirdExampleFirstDefect_forced_oneCell C F
  have hlt := F.current_lt
  unfold Word.criticalDefect at hcell
  have hheight : Word.prefixTwoDepth w j=Word.criticalHeight j-1 := by omega
  have hjpos : 0<j := by omega
  have hprev := Word.prefixTwoDepth_lt_of_valid C.minimal.1
    (i:=j-1) (j:=j) (by omega) (Nat.le_of_lt F.index_lt)
  rw [F.before (j-1) (by omega),hheight] at hprev
  have ha := (thirdExample_highRoof_indices_checked ⟨j,hjhi⟩
    (by
      change 24 < j
      omega)
    hprev (by
      change Word.criticalHeight j - 1 < 68
      rw [← hheight]
      exact hhhi)).2
  have hr := candidate_branch_residue CertL C F ha hheight
  have hm : m<cutoff := R.multiplier_lt C
  rcases ha with ha
  simp only [List.mem_cons] at ha
  rcases ha with h67 | hrest
  · rw [h67] at hr
    exact branch67_empty hm hr
  · have hmember : Word.criticalHeight j-1 ∈ [65,62,59,56,54,51,48,46,43,40] := by
      simpa only [List.mem_cons] using hrest
    have hw := (gapOneParadoxical_of_exactCriticalFerrersCertificate C).1
    have hlen : 1000<w.length := by
      have hp := C.oddSteps_eq
      change w.length=6586818669 at hp
      omega
    exact checked_family_impossible
      (familyCheck_sound (highBranches_checked hmember)) hm hr hw C.minimal.2 hlen

theorem thirdExample_roof_le_38_checked :
    ∀ j : Fin 25, Word.criticalHeight j.val≤38 := by decide

/-- valuationに等しいfirst defectのactual heightは37以下。 -/
theorem thirdExample_firstDefect_height_le_37
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word} {deficit gap m : Nat}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    {j : Nat} (F : ThirdExampleFirstCriticalDefectAt w j) :
    Word.prefixTwoDepth w j≤37 := by
  have hj := thirdExample_firstDefect_index_le_24 R CertL C F
  have hc := thirdExample_roof_le_38_checked ⟨j,by omega⟩
  have hl := F.current_lt
  change Word.criticalHeight j≤38 at hc
  omega

/-- ν₂(deficit)≤37 のexact-power版。deficitの非零性もこの結論に含まれる。 -/
theorem thirdExample_deficit_exactTwoPow_le_37
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word} {deficit gap m : Nat}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    ∃ a≤37, Word.ExactTwoPowZ a (deficit:ℤ) := by
  obtain ⟨j,F⟩ := thirdExampleFirstCriticalDefect_exists R CertL C
  exact ⟨Word.prefixTwoDepth w j,
    thirdExample_firstDefect_height_le_37 R CertL C F,
    thirdExampleFirstDefect_exactTwoPow C F⟩

end Collatz2.CSTMicro.ThirdExampleSearch
