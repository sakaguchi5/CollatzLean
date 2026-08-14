import CollatzLean.Collatz2.Canonical.PositiveSuffixBudget
import CollatzLean.Collatz2.Global.OddOrbitSurvivalBridge

/-!
# Collatz2 Global: canonical endpoint-floor contracting return

q=0 right branch で本当に必要な finite obstruction を保持する。

以前の `CanonicalAdjacentContractingReturn` は start を global minimum に固定していた。
しかし endpoint floor は一般の FirstCrossing から start を固定したままでは従わない。
正しい最小化では positive / all-suffix-contracting subsegment の start は内部へ移り得る。

そこでこの object は

* actual orbit 上の任意 start index
* canonical start/end
* strict positive return
* FirstCrossing
* 全 proper interior boundary が terminal endpoint より上

だけを保持する。

この条件は次ファイルで right branch から無条件に構成される。
また FirstCrossing から `AllSuffixesContracting` が従うため、
最終 budget

  sigma * 2^H = 3*G*S + K

も FirstCrossing の prefix profile を再利用せず回収できる。
-/

namespace Collatz2
namespace OddOrbit

/--
canonical endpoint-floor contracting return。

`startIndex` から `length` step の actual segment が q=0 canonical FirstCrossing で、
全 proper interior boundary は terminal endpoint より strict に上にある。
-/
structure CanonicalEndpointFloorContractingReturn (O : OddOrbit) where
  unbounded : O.Unbounded

  startIndex : ℕ
  length : ℕ
  length_pos : 0 < length

  firstCrossing :
    Word.FirstCrossing (O.segment startIndex length)

  positive :
    O.value startIndex <
      O.value (startIndex + length)

  endpointFloor :
    ∀ k : ℕ,
      0 < k →
      k < length →
      O.value (startIndex + length) <
        O.value (startIndex + k)

  startCanonical :
    O.value startIndex =
      Word.canonicalStart (O.segment startIndex length)

  endCanonical :
    O.value (startIndex + length) =
      Word.canonicalEnd (O.segment startIndex length)

namespace CanonicalEndpointFloorContractingReturn

/-- obstruction word。 -/
def word
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) : Word :=
  O.segment D.startIndex D.length

/-- terminal index。 -/
def endIndex
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) : ℕ :=
  D.startIndex + D.length

@[simp] theorem word_length
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    D.word.length = D.length := by
  simp [word]

/-- word は nonempty。 -/
theorem word_nonempty
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    D.word ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [D.word_length]
  exact D.length_pos

/-- actual normalized run。 -/
theorem runs
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Runs D.word
      (O.value D.startIndex)
      (O.value D.endIndex) := by
  simpa [word, endIndex] using
    O.runsSegment D.startIndex D.length

/-- word は valid。 -/
theorem word_valid
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.Valid D.word :=
  D.runs.valid

/-- whole transfer は contracting。 -/
theorem contracting
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.Contracting D.word := by
  simpa [word] using D.firstCrossing.terminalContracting

/-- FirstCrossing から全 nonempty suffix contracting を回収する。 -/
theorem allSuffixesContracting
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.AllSuffixesContracting D.word := by
  simpa [word] using D.firstCrossing.allSuffixesContracting

/-- actual run は canonical run そのもの。 -/
theorem runsCanonical
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Runs D.word
      (Word.canonicalStart D.word)
      (Word.canonicalEnd D.word) := by
  have h := D.runs
  rw [D.startCanonical] at h
  simp only [endIndex] at h
  rw [D.endCanonical] at h
  simpa [word] using h

/-- canonical return は strict positive。 -/
theorem canonicalPositive
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.canonicalStart D.word <
      Word.canonicalEnd D.word := by
  calc
    Word.canonicalStart D.word
        = O.value D.startIndex := by
            simpa [word] using D.startCanonical.symm
    _ < O.value D.endIndex := by
          simpa [endIndex] using D.positive
    _ = Word.canonicalEnd D.word := by
          simpa [word, endIndex] using D.endCanonical

/-- endpoint floor の word-boundary 版。 -/
theorem endpointFloor_value
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.word.length) :
    O.value D.endIndex <
      O.value (D.startIndex + k) := by
  have hkLt' : k < D.length := by
    simpa [D.word_length] using hkLt
  simpa [endIndex] using
    D.endpointFloor k hkPos hkLt'

/--
最終 obstruction の half-gap / sigma exact budget。

  canonicalEnd = canonicalStart + 2*n
  p = 6*n + sigma
  sigma * 2^H = 3*G*canonicalStart + K

ここで `K = suffixBudgetExcess > 0`。
-/
theorem exists_halfGap_sigma_budgetIdentity
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    ∃ n sigma : ℕ,
      0 < n ∧
      0 < sigma ∧
      Word.canonicalEnd D.word =
        Word.canonicalStart D.word + 2 * n ∧
      Word.oddSteps D.word = 6 * n + sigma ∧
      sigma * 2 ^ Word.twoSteps D.word =
        3 * (AffineTransfer.ofWord D.word).centerGap *
              Word.canonicalStart D.word +
          Word.suffixBudgetExcess D.word := by
  exact
    D.allSuffixesContracting.exists_canonicalHalfGap_sigma_budgetIdentity
      D.word_valid
      D.word_nonempty
      D.canonicalPositive

/-- suffix budget excess は正。 -/
theorem suffixBudgetExcess_pos
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    0 < Word.suffixBudgetExcess D.word :=
  D.allSuffixesContracting.suffixBudgetExcess_pos D.word_nonempty

/--
suffix budget excess は signed suffix determinant integral の符号反転。
-/
theorem suffixBudgetExcess_int_eq_neg_integral
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    (Word.suffixBudgetExcess D.word : ℤ) =
      -Word.suffixDeterminantIntegral D.word :=
  D.allSuffixesContracting.suffixBudgetExcess_int_eq_neg_integral
      D.word_nonempty

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
