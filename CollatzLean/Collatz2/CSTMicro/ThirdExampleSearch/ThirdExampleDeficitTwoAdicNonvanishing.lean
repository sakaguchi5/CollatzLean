import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleEndpointBound42
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleGapFactors
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCanonical42ModularFold
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCleanGapOneAffineCompatibility
set_option linter.style.nativeDecide false
/-!
# 第3例探索 3: target deficit は `2^68` で消えない

左 collar では gap-one deficit を

  D = C - G m  (mod 2^68)

として扱う。`critical Phi mod 2^68` は既存 canonical 42-block fold から取り、
固定 target の切片 `C` と gap `G` を小さい ZMod 値として保持する。

`D = 0 (mod 2^68)` を仮定すると `m` は一意に

  90_240_244_460_680_082_430  (mod 2^68)

へ固定される。この代表元は range certificate の cutoff より大きいため、真の候補では
`2^68 ∤ D` が従う。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open ExternalArithmetic

/-- canonical 42-block fold が返す `critical Phi mod 2^68`。 -/
def thirdExampleCriticalPhiModTwo : ZMod thirdExampleLeftModulus :=
  (thirdExampleCanonical42ModularFold thirdExampleLeftModulus 0).apply 0

/-- 左 CF certification の下で hot-path 値は actual critical `Phi` と一致する。 -/
theorem thirdExampleCriticalPhiModTwo_exact
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus) :
    thirdExampleCriticalPhiModTwo =
      (criticalPrefixPhiZ thirdExampleTargetP : ZMod thirdExampleLeftModulus) := by
  unfold thirdExampleCriticalPhiModTwo
  rw [thirdExampleCanonical42LeftFold_apply_zero CertL 0]
  simp [criticalPrefixDefectZ]

/-- target の deficit affine 式の切片 `C mod 2^68`。 -/
def thirdExampleDeficitInterceptModTwo : ZMod thirdExampleLeftModulus :=
  ((3 : ZMod thirdExampleLeftModulus) ^ thirdExampleTargetP) +
    thirdExampleCriticalPhiModTwo -
    ((2 : ZMod thirdExampleLeftModulus) ^ thirdExampleTargetH)

/-- target coefficient gap `G mod 2^68`。 -/
def thirdExampleGapModTwo : ZMod thirdExampleLeftModulus :=
  ((2 : ZMod thirdExampleLeftModulus) ^ (thirdExampleTargetH + 1)) -
    ((3 : ZMod thirdExampleLeftModulus) ^ (thirdExampleTargetP + 1))

/-- 左 collar の固定数値 checkpoint。 -/
theorem thirdExampleCriticalPhiModTwo_literal :
    thirdExampleCriticalPhiModTwo =
      (46_642_985_394_281_169_823 : ZMod thirdExampleLeftModulus) := by
  native_decide

theorem thirdExampleDeficitInterceptModTwo_literal :
    thirdExampleDeficitInterceptModTwo =
      (196_184_205_680_234_258_930 : ZMod thirdExampleLeftModulus) := by
  native_decide

theorem thirdExampleGapModTwo_literal :
    thirdExampleGapModTwo =
      (141_672_149_500_846_384_391 : ZMod thirdExampleLeftModulus) := by
  native_decide

/-- `G mod 2^68` の固定逆元。 -/
def thirdExampleGapModTwoInverse : ℕ :=
  144_094_860_649_477_224_631

/-- `D = 0 mod 2^68` のときに強制される `m` residue。 -/
def thirdExampleZeroDeficitMResidue : ℕ :=
  90_240_244_460_680_082_430

/-- 固定逆元の kernel/native 検証。 -/
theorem thirdExampleGapModTwoInverse_spec :
    (thirdExampleGapModTwoInverse : ZMod thirdExampleLeftModulus) *
      thirdExampleGapModTwo = 1 := by
  native_decide

/-- zero-deficit residue は実際に `G*m = C` を満たす。 -/
theorem thirdExampleZeroDeficitMResidue_spec :
    thirdExampleGapModTwo *
        (thirdExampleZeroDeficitMResidue : ZMod thirdExampleLeftModulus) =
      thirdExampleDeficitInterceptModTwo := by
  native_decide

/-- zero-deficit residue は range cutoff より strict に大きい。 -/
theorem thirdExampleEndpointMultiplierCutoff_lt_zeroDeficitResidue :
    thirdExampleEndpointMultiplierCutoff < thirdExampleZeroDeficitMResidue := by
  norm_num [thirdExampleEndpointMultiplierCutoff, thirdExampleZeroDeficitMResidue]

/-- zero-deficit residue 自身は canonical `2^68` 代表元の範囲内。 -/
theorem thirdExampleZeroDeficitMResidue_lt_leftModulus :
    thirdExampleZeroDeficitMResidue < thirdExampleLeftModulus := by
  norm_num [thirdExampleZeroDeficitMResidue, thirdExampleLeftModulus]

/-- 真の target certificate では certificate gap の左 residue は固定 `G` に一致する。 -/
theorem thirdExampleCertificate_gap_modTwo
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    (gap : ZMod thirdExampleLeftModulus) = thirdExampleGapModTwo := by
  have h := congrArg
    (fun n : ℕ => (n : ZMod thirdExampleLeftModulus))
    C.next_gap_equation
  push_cast at h
  unfold thirdExampleGapModTwo
  linear_combination h

/--
actual critical affine constant を左 modulus へ送ると、
integer 側の `criticalPrefixPhiZ` の像と一致する。
-/
theorem thirdExampleCriticalAffineConstModTwo_eq_criticalPrefixPhiZ :
    (Word.criticalAffineConst thirdExampleTargetP :
        ZMod thirdExampleLeftModulus) =
      (criticalPrefixPhiZ thirdExampleTargetP :
        ZMod thirdExampleLeftModulus) := by
  have hBridge :=
    congrArg
      (fun z : ℤ => (z : ZMod thirdExampleLeftModulus))
      (cleanCriticalPrefixPhiZ_eq_criticalAffineConst_cast
        thirdExampleTargetP)
  push_cast at hBridge
  exact hBridge.symm

/--
左 CF certification の下では、
actual critical affine constant の左 residue は
canonical 42-block fold の `critical Phi` と一致する。
-/
theorem thirdExampleCriticalAffineConstModTwo_exact
    (CertL :
      ThirdExampleCFPacketCertification
        thirdExampleLeftModulus) :
    (Word.criticalAffineConst thirdExampleTargetP :
        ZMod thirdExampleLeftModulus) =
      thirdExampleCriticalPhiModTwo := by
  calc
    (Word.criticalAffineConst thirdExampleTargetP :
        ZMod thirdExampleLeftModulus) =
        (criticalPrefixPhiZ thirdExampleTargetP :
          ZMod thirdExampleLeftModulus) :=
      thirdExampleCriticalAffineConstModTwo_eq_criticalPrefixPhiZ
    _ = thirdExampleCriticalPhiModTwo :=
      (thirdExampleCriticalPhiModTwo_exact CertL).symm

/--
真の target certificate の deficit equation を
左 modulus へそのまま送った balance equation。

この段階では引き算による rearrangement は行わない。
-/
theorem thirdExampleCertificate_deficit_balance_modTwo
    (CertL :
      ThirdExampleCFPacketCertification
        thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C :
      ExactCriticalGapOneFerrersCertificate
        w
        thirdExampleTargetP
        thirdExampleTargetH
        deficit
        gap
        m) :
    ((3 : ZMod thirdExampleLeftModulus) ^
        thirdExampleTargetP) +
        thirdExampleCriticalPhiModTwo =
      ((2 : ZMod thirdExampleLeftModulus) ^
          thirdExampleTargetH) +
        (deficit : ZMod thirdExampleLeftModulus) +
        (m : ZMod thirdExampleLeftModulus) *
          thirdExampleGapModTwo := by
  have hDef :=
    congrArg
      (fun n : ℕ =>
        (n : ZMod thirdExampleLeftModulus))
      C.deficit_equation
  push_cast at hDef
  rw [thirdExampleCriticalAffineConstModTwo_exact CertL] at hDef
  rw [thirdExampleCertificate_gap_modTwo C] at hDef
  exact hDef

/--
deficit balance equation を、
最終 affine residue に使いやすい順序へ並べ替える。
-/
theorem thirdExampleCertificate_deficit_rearranged_modTwo
    (CertL :
      ThirdExampleCFPacketCertification
        thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C :
      ExactCriticalGapOneFerrersCertificate
        w
        thirdExampleTargetP
        thirdExampleTargetH
        deficit
        gap
        m) :
    (deficit : ZMod thirdExampleLeftModulus) +
        thirdExampleGapModTwo *
          (m : ZMod thirdExampleLeftModulus) +
        ((2 : ZMod thirdExampleLeftModulus) ^
          thirdExampleTargetH) =
      ((3 : ZMod thirdExampleLeftModulus) ^
          thirdExampleTargetP) +
        thirdExampleCriticalPhiModTwo := by
  have hBalance :=
    thirdExampleCertificate_deficit_balance_modTwo
      CertL C
  calc
    (deficit : ZMod thirdExampleLeftModulus) +
          thirdExampleGapModTwo *
            (m : ZMod thirdExampleLeftModulus) +
          ((2 : ZMod thirdExampleLeftModulus) ^
            thirdExampleTargetH) =
        ((2 : ZMod thirdExampleLeftModulus) ^
            thirdExampleTargetH) +
          (deficit : ZMod thirdExampleLeftModulus) +
          (m : ZMod thirdExampleLeftModulus) *
            thirdExampleGapModTwo := by
      rw [
        mul_comm
          thirdExampleGapModTwo
          (m : ZMod thirdExampleLeftModulus)
      ]
      ring
    _ =
        ((3 : ZMod thirdExampleLeftModulus) ^
            thirdExampleTargetP) +
          thirdExampleCriticalPhiModTwo :=
      hBalance.symm

/--
真の target certificate では deficit の左 residue は exact に `C-Gm`。
-/
theorem thirdExampleCertificate_deficit_affine_modTwo
    (CertL :
      ThirdExampleCFPacketCertification
        thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C :
      ExactCriticalGapOneFerrersCertificate
        w
        thirdExampleTargetP
        thirdExampleTargetH
        deficit
        gap
        m) :
    (deficit : ZMod thirdExampleLeftModulus) =
      thirdExampleDeficitInterceptModTwo -
        thirdExampleGapModTwo *
          (m : ZMod thirdExampleLeftModulus) := by
  unfold thirdExampleDeficitInterceptModTwo
  apply (eq_sub_iff_add_eq).2
  apply (eq_sub_iff_add_eq).2
  exact
    thirdExampleCertificate_deficit_rearranged_modTwo
      CertL C

/--
range certificate の下では target deficit の `mod 2^68` 像は非零。
この形を valuation 側の中心命題として使う。
-/
theorem thirdExampleDeficit_modTwo_ne_zero
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    (deficit : ZMod thirdExampleLeftModulus) ≠ 0 := by
  intro hZero
  have hAffine := thirdExampleCertificate_deficit_affine_modTwo CertL C
  rw [hZero] at hAffine
  have hGm :
      thirdExampleGapModTwo * (m : ZMod thirdExampleLeftModulus) =
        thirdExampleDeficitInterceptModTwo := by
    linear_combination hAffine
  have hmCast :
      (m : ZMod thirdExampleLeftModulus) =
        (thirdExampleZeroDeficitMResidue : ZMod thirdExampleLeftModulus) := by
    calc
      (m : ZMod thirdExampleLeftModulus) =
          1 * (m : ZMod thirdExampleLeftModulus) := by ring
      _ = ((thirdExampleGapModTwoInverse : ZMod thirdExampleLeftModulus) *
            thirdExampleGapModTwo) * (m : ZMod thirdExampleLeftModulus) := by
              rw [thirdExampleGapModTwoInverse_spec]
      _ = (thirdExampleGapModTwoInverse : ZMod thirdExampleLeftModulus) *
            (thirdExampleGapModTwo * (m : ZMod thirdExampleLeftModulus)) := by ring
      _ = (thirdExampleGapModTwoInverse : ZMod thirdExampleLeftModulus) *
            thirdExampleDeficitInterceptModTwo := by rw [hGm]
      _ = (thirdExampleGapModTwoInverse : ZMod thirdExampleLeftModulus) *
            (thirdExampleGapModTwo *
              (thirdExampleZeroDeficitMResidue : ZMod thirdExampleLeftModulus)) := by
                rw [thirdExampleZeroDeficitMResidue_spec]
      _ = ((thirdExampleGapModTwoInverse : ZMod thirdExampleLeftModulus) *
            thirdExampleGapModTwo) *
              (thirdExampleZeroDeficitMResidue : ZMod thirdExampleLeftModulus) := by ring
      _ = (thirdExampleZeroDeficitMResidue : ZMod thirdExampleLeftModulus) := by
        rw [thirdExampleGapModTwoInverse_spec]
        simp
  have hmLt : m < thirdExampleLeftModulus :=
    thirdExampleMultiplier_lt_twoPow68 R C
  have hm0Lt := thirdExampleZeroDeficitMResidue_lt_leftModulus
  let : NeZero thirdExampleLeftModulus :=
    ⟨Nat.ne_of_gt thirdExampleLeftModulus_pos⟩
  have hVal := congrArg ZMod.val hmCast
  have hmEqMod :
      m % thirdExampleLeftModulus =
        thirdExampleZeroDeficitMResidue % thirdExampleLeftModulus := by
    simpa using hVal
  rw [Nat.mod_eq_of_lt hmLt, Nat.mod_eq_of_lt hm0Lt] at hmEqMod
  have hmRange := R.multiplier_lt C
  have hTooLarge := thirdExampleEndpointMultiplierCutoff_lt_zeroDeficitResidue
  omega

/-- 左 modulus 自身は `ZMod thirdExampleLeftModulus` で 0。 -/
@[simp] theorem thirdExampleTwoPow68_modLeft_eq_zero :
    ((2 ^ 68 : ℕ) : ZMod thirdExampleLeftModulus) = 0 := by
  decide

/--
従って natural-number deficit 自体も `2^68` の倍数ではない。
-/
theorem thirdExampleDeficit_not_dvd_twoPow68
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    ¬ (2 ^ 68 ∣ deficit) := by
  intro hDvd
  have hZero :
      (deficit : ZMod thirdExampleLeftModulus) = 0 := by
    rcases hDvd with ⟨t, ht⟩
    rw [ht]
    rw [Nat.cast_mul]
    rw [thirdExampleTwoPow68_modLeft_eq_zero]
    simp
  exact thirdExampleDeficit_modTwo_ne_zero R CertL C hZero

end ThirdExampleSearch
end CSTMicro
end Collatz2
