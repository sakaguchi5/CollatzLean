import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDeficitThreeAdicFilter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitEvaluator
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCanonical42ModularFold
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleGapOneAffineCompatibility

/-!
# 第3例探索 5: deficit から endpoint residue を直接復元

D2 packet を runtime verifier から外す。
Exact gap-one では整数上で

  2^(beta+1) * endpoint
    = criticalPrefixPhiZ(p) - deficit + 3^p * start

が成り立つ。target では p >= 42 なので `mod 3^42` で最後の項が消え、

  2^(beta+1) * endpoint = Phi(p) - deficit

となる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open ExternalArithmetic

/-- target の endpoint 係数。`3^42` と互いに素なので unit。 -/
def thirdExampleEndpointCoefficient : ZMod thirdExampleRightModulus :=
  (2 : ZMod thirdExampleRightModulus) ^ (thirdExampleTargetBeta + 1)

/-- hot path で使う critical `Phi(p) mod 3^42`。42-block modular fold の `y=0` 値。 -/
def thirdExampleCriticalPhiModThree : ZMod thirdExampleRightModulus :=
  (thirdExampleCanonical42ModularFold thirdExampleRightModulus 0).apply 0

/--
ZMod の inverse を使った endpoint residue 復元器。
係数が unit であることの soundness は proof-side theorem で接続する。
-/
def thirdExampleEndpointResidueOfDeficit
    (z : ThirdExampleDeficitResidue) : ZMod thirdExampleRightModulus :=
  (thirdExampleEndpointCoefficient)⁻¹ *
    (thirdExampleCriticalPhiModThree -
      (z.val : ZMod thirdExampleRightModulus))

/-- exact gap-one certificate から、D2 を介さない整数 endpoint identity。 -/
theorem exactCriticalGapOne_endpoint_direct_identity
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
  have hPhi := criticalPrefixPhiZ_eq_criticalAffineConst_cast p
  rw [hPhi]
  linarith

/-- target では `p >= 42`。 -/
theorem thirdExampleTargetP_ge_42 : 42 ≤ thirdExampleTargetP := by
  norm_num [thirdExampleTargetP]

/-- target exact candidate の endpoint congruence。 -/
theorem exactThirdExample_endpoint_direct_mod
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    ((2 : ZMod thirdExampleRightModulus) ^
        (beattyIndex thirdExampleTargetP + 1)) *
        (gapOneEndpointValue m : ZMod thirdExampleRightModulus) =
      (criticalPrefixPhiZ thirdExampleTargetP : ZMod thirdExampleRightModulus) -
        (deficit : ZMod thirdExampleRightModulus) := by
  have h := congrArg
    (fun z : ℤ => (z : ZMod thirdExampleRightModulus))
    (exactCriticalGapOne_endpoint_direct_identity C)
  have hThree :
      ((3 : ZMod thirdExampleRightModulus) ^ thirdExampleTargetP) = 0 := by
    unfold thirdExampleRightModulus
    exact ZMod.natCast_pow_eq_zero_of_le 3 thirdExampleTargetP_ge_42
  push_cast at h
  rw [hThree] at h
  simpa using h

end ThirdExampleSearch
end CSTMicro
end Collatz2
