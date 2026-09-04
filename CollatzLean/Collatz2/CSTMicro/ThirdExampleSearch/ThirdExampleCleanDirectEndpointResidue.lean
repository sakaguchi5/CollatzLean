import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCleanGapOneAffineCompatibility
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCanonical42ModularFold
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint
set_option linter.style.nativeDecide false
/-!
# 第3例探索 clean D3-3: deficit から endpoint residue を直接復元

旧 D3 の `criticalizationBoundaryDigit` を使わず、gap-one の affine identity を
`mod 3^42` に落として endpoint residue を直接復元する。

真の gap-one certificate では

  2^(beta+1) * endpoint
    = criticalPrefixPhiZ(p) - deficit + 3^p * start

が整数上で成立する。第3例 target は `p >= 42` なので `mod 3^42` では
最後の `3^p * start` が消える。

従って

  2^(beta+1) * endpoint
    = Phi(p) - deficit          (mod 3^42)

となる。左係数は3進 unit なので、固定逆元を一度だけ kernel で検証して
endpoint residue を一意に復元する。

このファイルは Last41 / attached branch / PureB に依存しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open ExternalArithmetic

/-- target の critical exponent `beta = H-1`。 -/
def thirdExampleCleanTargetBeta : ℕ :=
  thirdExampleTargetH - 1

/--
右 modulus 上の endpoint 係数。
certificate 上では `H = beattyIndex p + 1` なので `2^(beta+1) = 2^H`。
-/
def thirdExampleCleanEndpointCoefficient : ZMod thirdExampleRightModulus :=
  (2 : ZMod thirdExampleRightModulus) ^ thirdExampleTargetH

/--
`thirdExampleCleanEndpointCoefficient` の固定逆元の Nat 代表元。
探索中に Euclid 計算を繰り返さない。
-/
def thirdExampleCleanEndpointCoefficientInverse : ℕ :=
  74922190991541757441

/-- 固定逆元が本当に右 modulus 上の逆元であることを kernel/native で確認する。 -/
theorem thirdExampleCleanEndpointCoefficientInverse_spec :
    (thirdExampleCleanEndpointCoefficientInverse :
        ZMod thirdExampleRightModulus) *
      thirdExampleCleanEndpointCoefficient = 1 := by
  native_decide

/--
hot path で使う critical `Phi(p) mod 3^42`。
canonical 42-block modular fold の `y=0` 値だけを計算する。
-/
def thirdExampleCleanCriticalPhiModThree :
    ZMod thirdExampleRightModulus :=
  (thirdExampleCanonical42ModularFold thirdExampleRightModulus 0).apply 0

/--
右 CF packet certification があれば、上の hot-path 値は
actual `criticalPrefixPhiZ targetP` の剰余像に一致する。
-/
theorem thirdExampleCleanCriticalPhiModThree_exact
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus) :
    thirdExampleCleanCriticalPhiModThree =
      (criticalPrefixPhiZ thirdExampleTargetP :
        ZMod thirdExampleRightModulus) := by
  unfold thirdExampleCleanCriticalPhiModThree
  rw [thirdExampleCanonical42RightFold_apply_zero CertR 0]
  simp [criticalPrefixDefectZ]

/--
deficit residue から endpoint residue を直接復元する hot-path 関数。
-/
def thirdExampleCleanEndpointResidueOfDeficit
    (deficitModThree : ZMod thirdExampleRightModulus) :
    ZMod thirdExampleRightModulus :=
  (thirdExampleCleanEndpointCoefficientInverse :
      ZMod thirdExampleRightModulus) *
    (thirdExampleCleanCriticalPhiModThree - deficitModThree)

/--
真の gap-one certificate から得られる整数 endpoint identity。
Case II の boundary digit は使わない。
-/
theorem cleanExactCriticalGapOne_endpoint_direct_identity
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    (2 : ℤ) ^ (beattyIndex p + 1) *
        (gapOneEndpointValue m : ℤ) =
      criticalPrefixPhiZ p - (deficit : ℤ) +
        (3 : ℤ) ^ p * (gapOneStartValue m : ℤ) := by
  have hBudget := congrArg (fun n : ℕ => (n : ℤ)) C.affine_budget
  push_cast at hBudget
  have hReal := realizes_gapOne_of_criticalFerrersDeficitEquation C.toCritical
  have hRealEq :=
    (Word.realizes_iff w (gapOneStartValue m) (gapOneEndpointValue m)).1 hReal
  rw [C.oddSteps_eq, C.twoSteps_eq, C.terminalDepth_eq] at hRealEq
  have hPhi := cleanCriticalPrefixPhiZ_eq_criticalAffineConst_cast p
  rw [hPhi]
  linarith

/-- target では `p >= 42`。 -/
theorem thirdExampleCleanTargetP_ge_42 : 42 ≤ thirdExampleTargetP := by
  norm_num [thirdExampleTargetP]

/--
第3例 target の exact candidate が満たす右 endpoint congruence。
`3^p * start` は `mod 3^42` で消える。
-/
theorem cleanExactThirdExample_endpoint_direct_mod
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    thirdExampleCleanEndpointCoefficient *
        (gapOneEndpointValue m : ZMod thirdExampleRightModulus) =
      (criticalPrefixPhiZ thirdExampleTargetP :
          ZMod thirdExampleRightModulus) -
        (deficit : ZMod thirdExampleRightModulus) := by
  have h := congrArg
    (fun z : ℤ => (z : ZMod thirdExampleRightModulus))
    (cleanExactCriticalGapOne_endpoint_direct_identity C)
  have hThree :
      ((3 : ZMod thirdExampleRightModulus) ^ thirdExampleTargetP) = 0 := by
    unfold thirdExampleRightModulus
    exact ZMod.natCast_pow_eq_zero_of_le 3 thirdExampleCleanTargetP_ge_42
  push_cast at h
  rw [hThree] at h
  have hDepth :
      thirdExampleTargetH = beattyIndex thirdExampleTargetP + 1 :=
    C.terminalDepth_eq
  simpa [thirdExampleCleanEndpointCoefficient, hDepth] using h

/--
clean D3 の中心 soundness。
certificate deficit の `mod 3^42` を入力すれば、直接復元器は actual endpoint の
`ZMod (3^42)` 像を返す。
-/
theorem thirdExampleCleanEndpointResidueOfDeficit_exact
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    thirdExampleCleanEndpointResidueOfDeficit
        (deficit : ZMod thirdExampleRightModulus) =
      (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
  have hEndpoint := cleanExactThirdExample_endpoint_direct_mod C
  have hPhi := thirdExampleCleanCriticalPhiModThree_exact CertR
  unfold thirdExampleCleanEndpointResidueOfDeficit
  rw [hPhi]
  rw [← hEndpoint]
  calc
    (thirdExampleCleanEndpointCoefficientInverse :
        ZMod thirdExampleRightModulus) *
        (thirdExampleCleanEndpointCoefficient *
          (gapOneEndpointValue m : ZMod thirdExampleRightModulus)) =
      ((thirdExampleCleanEndpointCoefficientInverse :
          ZMod thirdExampleRightModulus) *
        thirdExampleCleanEndpointCoefficient) *
          (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
            ring
    _ = (gapOneEndpointValue m : ZMod thirdExampleRightModulus) := by
      rw [thirdExampleCleanEndpointCoefficientInverse_spec]
      simp

end ThirdExampleSearch
end CSTMicro
end Collatz2
