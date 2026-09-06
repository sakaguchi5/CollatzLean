/-! 第三例の高い11枝。候補数は剰余と上界から再計算する。 -/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

def leftModulus : Nat := 2^68
def cutoff : Nat := 54709494565756179604
def intercept : Nat := 196184205680234258930
def gapResidue : Nat := 141672149500846384391

/-- Newton反復で奇数gapの逆元を求める。入力した逆元を信用しない。 -/
def inverseIter : Nat → Nat
  | 0 => 1
  | k+1 => let x := inverseIter k
           (x * (2 + leftModulus - gapResidue*x % leftModulus)) % leftModulus
def gapInverse : Nat := inverseIter 7

theorem gapInverse_checked : gapResidue * gapInverse % leftModulus = 1 := by
  decide

def branchModulus (a : Nat) : Nat := 2^(a+1)
def branchResidue (a : Nat) : Nat :=
  ((intercept + leftModulus - 2^a) * gapInverse) % branchModulus a
def branchCount (a : Nat) : Nat :=
  if branchResidue a < cutoff then
    (cutoff - 1 - branchResidue a) / branchModulus a + 1
  else 0

/-- 高枝の候補数。11個の小さい結果だけを保持し、候補リストは作らない。 -/
theorem highBranchCounts_checked :
    branchCount 67 = 0 ∧ branchCount 65 = 1 ∧ branchCount 62 = 6 ∧
    branchCount 59 = 47 ∧ branchCount 56 = 379 ∧ branchCount 54 = 1519 ∧
    branchCount 51 = 12148 ∧ branchCount 48 = 97184 ∧
    branchCount 46 = 388735 ∧ branchCount 43 = 3109875 ∧
    branchCount 40 = 24878998 := by
  decide

/-- 計算した各剰余は所定の exact-valuation 合同を満たす。 -/
theorem highBranchResidues_checked :
    ∀ a ∈ [67,65,62,59,56,54,51,48,46,43,40],
      (gapResidue * branchResidue a + 2^a) % branchModulus a =
        intercept % branchModulus a := by
  decide

theorem highBranchInverses_checked :
    ∀ a ∈ [67,65,62,59,56,54,51,48,46,43,40],
      gapInverse * gapResidue % branchModulus a = 1 := by
  decide

theorem highBranchModuli_checked :
    ∀ a ∈ [67,65,62,59,56,54,51,48,46,43,40],
      branchModulus a ∣ leftModulus := by
  decide

theorem branch67_empty {m : Nat}
    (hm : m < cutoff) (hr : m % branchModulus 67 = branchResidue 67) : False := by
  have hq : branchModulus 67 = 295147905179352825856 := by native_decide
  have hres : branchResidue 67 = 237814197050356495358 := by native_decide
  rw [hq, hres] at hr
  unfold cutoff at hm
  have hsmall : m < 295147905179352825856 := by omega
  rw [Nat.mod_eq_of_lt hsmall] at hr
  omega

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
