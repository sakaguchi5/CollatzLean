import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDeficitTwoAdicNonvanishing
import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicCore
import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicActualWord

/-!
# 第3例探索 4: 最初の defect は必ず一セル

actual FirstCrossing profile が critical roof から初めて外れる列を `j` とする。
それ以前は actual height と critical height が一致し、`j` では actual が低い。

critical height の一段増分は高々2、actual height は valid word 上で strict に増加する。
この二事実だけから、最初のずれは

  criticalHeight j - actualHeight j = 1

へ強制される。

さらに full deficit の exact 2進深さはこの actual height である。
前段の `2^68 ∤ deficit` と合わせると、最初の defect index も 68 未満へ入る。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/-- actual profile が critical roof から最初に外れる列。 -/
structure ThirdExampleFirstCriticalDefectAt (w : Word) (j : ℕ) : Prop where
  index_lt : j < Word.oddSteps w
  before : ∀ i : ℕ, i < j →
    Word.prefixTwoDepth w i = Word.criticalHeight i
  current_lt :
    Word.prefixTwoDepth w j < Word.criticalHeight j

/-- critical roof profile の Ferrers code は critical affine budget そのもの。 -/
theorem criticalFerrersCode_criticalHeight_eq_criticalAffineConst
    (p : ℕ) :
    Word.criticalFerrersCode p Word.criticalHeight =
      Word.criticalAffineConst p := by
  rw [Word.criticalFerrersCode_eq_sum]
  unfold Word.criticalAffineConst Word.criticalAffineTerm
  rfl

/--
range certificate と左 certification があれば、真の target candidate は
critical roof と少なくとも一列で異なる。さらに最小の相違列を取れば
`ThirdExampleFirstCriticalDefectAt` が得られる。
-/
theorem thirdExampleFirstCriticalDefect_exists
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    ∃ j : ℕ, ThirdExampleFirstCriticalDefectAt w j := by
  classical
  have hModNe := thirdExampleDeficit_modTwo_ne_zero R CertL C
  have hExists :
      ∃ j : ℕ,
        j < Word.oddSteps w ∧
          Word.prefixTwoDepth w j ≠ Word.criticalHeight j := by
    by_contra hNo
    push Not at hNo
    have hCodeEq :=
      Word.criticalFerrersCode_eq_of_eq_before
        (Word.oddSteps w)
        (fun k => Word.prefixTwoDepth w k)
        Word.criticalHeight
        (fun i hi => hNo i hi)
    rw [Word.criticalFerrersCode_prefixTwoDepth_eq_affineConst] at hCodeEq
    rw [criticalFerrersCode_criticalHeight_eq_criticalAffineConst] at hCodeEq
    rw [C.oddSteps_eq] at hCodeEq
    have hBudget := C.affine_budget
    have hDefZero : deficit = 0 := by
      omega
    apply hModNe
    simp [hDefZero]
  let j := Nat.find hExists
  have hj :
      j < Word.oddSteps w ∧
        Word.prefixTwoDepth w j ≠ Word.criticalHeight j := by
    dsimp [j]
    exact Nat.find_spec hExists
  have hjPos : 0 < j := by
    by_contra hNot
    have hj0 : j = 0 := by
      omega
    have hEq0 :
        Word.prefixTwoDepth w j =
          Word.criticalHeight j := by
      rw [hj0]
      simp [Word.prefixTwoDepth, Word.criticalHeight]
    exact hj.2 hEq0
  refine ⟨j, ?_⟩
  refine {
    index_lt := hj.1
    before := ?_
    current_lt := ?_
  }
  · intro i hi
    by_contra hNe
    have hiCand :
        i < Word.oddSteps w ∧
          Word.prefixTwoDepth w i ≠ Word.criticalHeight i := by
      exact ⟨lt_trans hi hj.1, hNe⟩
    have hMinRaw :
        Nat.find hExists ≤ i :=
      Nat.find_min' hExists hiCand
    have hMin : j ≤ i := by
      dsimp [j]
      exact hMinRaw
    omega
  · have hLe :
        Word.prefixTwoDepth w j ≤
          Word.criticalHeight j :=
      C.minimal.2.prefixTwoDepth_le_criticalHeight
        hjPos hj.1
    omega

/--
最初の defect 列の actual height は full deficit の exact 2進深さになる。
-/
theorem thirdExampleFirstDefect_exactTwoPow
    {w : Word}
    {p H deficit gap m j : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j) :
    Word.ExactTwoPowZ (Word.prefixTwoDepth w j) (deficit : ℤ) := by
  let a := Word.prefixTwoDepth w j
  have hAfter :
      ∀ i : ℕ, j < i → i < Word.oddSteps w →
        a < Word.criticalHeight i ∧
          a < Word.prefixTwoDepth w i := by
    intro i hji hi
    constructor
    · have hCrit :
          Word.criticalHeight j <
            Word.criticalHeight i := by
        have hb := beattyIndex_strictMono hji
        simpa [criticalHeight_eq_beattyIndex] using hb
      have hCurrent :
          a < Word.criticalHeight j := by
        dsimp [a]
        exact F.current_lt
      exact lt_trans hCurrent hCrit
    · dsimp [a]
      exact
        Word.prefixTwoDepth_lt_of_valid
          C.minimal.1 hji (Nat.le_of_lt hi)
  have hExact :=
    Word.firstDifference_twoPow_exact
      (r := Word.oddSteps w)
      (j := j)
      (a := a)
      (h := Word.criticalHeight)
      (h' := fun k => Word.prefixTwoDepth w k)
      F.index_lt
      (fun i hi => (F.before i hi).symm)
      (by
        dsimp [a]
        exact (Nat.ne_of_lt F.current_lt).symm)
      (by
        dsimp [a]
        rw [
          Nat.min_eq_right
            (Nat.le_of_lt F.current_lt)
        ])
      hAfter
  have hBudget :=
    congrArg (fun n : ℕ => (n : ℤ)) C.affine_budget
  push_cast at hBudget
  have hDiff :
      Word.criticalFerrersCodeDiffZ
          (Word.oddSteps w)
          Word.criticalHeight
          (fun k => Word.prefixTwoDepth w k) =
        (deficit : ℤ) := by
    unfold Word.criticalFerrersCodeDiffZ
    rw [
      criticalFerrersCode_criticalHeight_eq_criticalAffineConst
    ]
    rw [
      Word.criticalFerrersCode_prefixTwoDepth_eq_affineConst
    ]
    rw [C.oddSteps_eq]
    rw [← hBudget]
    ring
  rw [hDiff] at hExact
  exact hExact

/--
最初の defect は depth 1、すなわち Ferrers の一セルだけである。
-/
theorem thirdExampleFirstDefect_forced_oneCell
    {w : Word}
    {p H deficit gap m j : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j) :
    Word.criticalDefect w j = 1 := by
  have hCurrentLt :
      Word.prefixTwoDepth w j < Word.criticalHeight j :=
    F.current_lt
  have hjPos : 0 < j := by
    by_contra hnot
    have hj0 : j = 0 := by
      omega
    have hCurrent0 := hCurrentLt
    rw [hj0] at hCurrent0
    simp [Word.prefixTwoDepth, Word.criticalHeight] at hCurrent0
  have hPrevLt : j - 1 < j := by
    omega
  have hPrevEq :
      Word.prefixTwoDepth w (j - 1) =
        Word.criticalHeight (j - 1) :=
    F.before (j - 1) hPrevLt
  have hActualStep :
      Word.prefixTwoDepth w (j - 1) <
        Word.prefixTwoDepth w j :=
    Word.prefixTwoDepth_lt_of_valid
      C.minimal.1
      (i := j - 1)
      (j := j)
      hPrevLt
      (Nat.le_of_lt F.index_lt)
  have hPrevRoofLtActual :
      Word.criticalHeight (j - 1) <
        Word.prefixTwoDepth w j := by
    calc
      Word.criticalHeight (j - 1) =
          Word.prefixTwoDepth w (j - 1) := hPrevEq.symm
      _ < Word.prefixTwoDepth w j := hActualStep
  have hRoofStep :
      Word.criticalHeight j ≤
        Word.criticalHeight (j - 1) + 2 := by
    have h :=
      beattyIndex_add_upper_of_threePow_le_twoPow
        (k := j - 1)
        (r := 1)
        (s := 2)
        (by norm_num)
    have hIdx : j - 1 + 1 = j := by
      omega
    rw [hIdx] at h
    simpa [criticalHeight_eq_beattyIndex] using h
  unfold Word.criticalDefect
  omega

/-- 整数として見た `2^68` も左 modulus では 0。 -/
@[simp] theorem thirdExampleIntTwoPow68_modLeft_eq_zero :
    (((2 : ℤ) ^ 68 : ℤ) : ZMod thirdExampleLeftModulus) = 0 := by
  decide

/--
`2^68 ∤ deficit` と exact valuation を合わせると、
最初の actual height は 68 未満。
-/
theorem thirdExampleFirstDefect_height_lt_68
    (R : ThirdExampleRangeCertificate)
    (CertL :
      ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m j : ℕ}
    (C :
      ExactCriticalGapOneFerrersCertificate
        w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j) :
    Word.prefixTwoDepth w j < 68 := by
  have hExact :=
    thirdExampleFirstDefect_exactTwoPow C F
  have hModNe :=
    thirdExampleDeficit_modTwo_ne_zero R CertL C
  by_contra hnot
  have h68 :
      68 ≤ Word.prefixTwoDepth w j := by
    omega
  have hPowDvd :
      (2 : ℤ) ^ 68 ∣
        (2 : ℤ) ^ Word.prefixTwoDepth w j := by
    refine
      ⟨(2 : ℤ) ^
          (Word.prefixTwoDepth w j - 68), ?_⟩
    have hAdd :
        Word.prefixTwoDepth w j =
          68 + (Word.prefixTwoDepth w j - 68) := by
      omega
    rw [hAdd, pow_add]
    simp
  have hDvdZ :
      (2 : ℤ) ^ 68 ∣ (deficit : ℤ) :=
    hPowDvd.trans hExact.1
  rcases hDvdZ with ⟨t, ht⟩
  have hCast :=
    congrArg
      (fun z : ℤ =>
        (z : ZMod thirdExampleLeftModulus))
      ht
  have hZero :
      (deficit : ZMod thirdExampleLeftModulus) = 0 := by
    change
      (deficit : ZMod thirdExampleLeftModulus) =
        ((((2 : ℤ) ^ 68) * t : ℤ) :
          ZMod thirdExampleLeftModulus) at hCast
    rw [Int.cast_mul] at hCast
    rw [thirdExampleIntTwoPow68_modLeft_eq_zero] at hCast
    simpa using hCast
  exact hModNe hZero

/-- 最初の defect index 自身も 68 未満。 -/
theorem thirdExampleFirstDefect_index_lt_68
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m j : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j) :
    j < 68 := by
  have hHeight := thirdExampleFirstDefect_height_lt_68 R CertL C F
  have hIndexLe : j ≤ Word.prefixTwoDepth w j :=
    Word.index_le_prefixTwoDepth_of_valid C.minimal.1 (Nat.le_of_lt F.index_lt)
  omega

/-- target では「最初の一セル」が左68 collar 内に必ず現れる。 -/
theorem thirdExampleFirstDefect_forced_oneCell_and_visible
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m j : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j) :
    Word.criticalDefect w j = 1 ∧ j < 68 := by
  exact ⟨thirdExampleFirstDefect_forced_oneCell C F,
    thirdExampleFirstDefect_index_lt_68 R CertL C F⟩

/--
真の target candidate には、左68 collar 内に depth 1 の最初の defect が必ず存在する。
外部から first-defect witness を与える必要はない。
-/
theorem thirdExampleFirstDefect_exists_oneCell_and_visible
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    ∃ j : ℕ,
      ThirdExampleFirstCriticalDefectAt w j ∧
        Word.criticalDefect w j = 1 ∧
        j < 68 := by
  rcases thirdExampleFirstCriticalDefect_exists R CertL C with ⟨j, F⟩
  refine ⟨j, F, ?_⟩
  exact thirdExampleFirstDefect_forced_oneCell_and_visible R CertL C F

end ThirdExampleSearch
end CSTMicro
end Collatz2
