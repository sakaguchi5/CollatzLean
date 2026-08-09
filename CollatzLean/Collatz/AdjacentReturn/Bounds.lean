import CollatzLean.Collatz.AdjacentReturn.Geometry
import CollatzLean.Collatz.Word.SharpAffine

/-!
# adjacent returnのsharp bounds

0a503cで再接続されていたprefix/suffix affine資産を、新State APIへ移す。
-/

namespace Collatz
namespace AdjacentReturn
namespace State

/-- contracting枝では`2^H * Δ < B`。 -/
theorem twoPow_totalExponent_mul_valueGap_lt_affineConstant
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    2 ^ R.totalExponent * R.valueGap < R.affineConstant := by
  have hgap : 0 < R.contractingGap := by
    have hC' := hC
    unfold IsContracting Word.Contracting at hC'
    have hlen : Word.oddSteps R.word = R.length := by
      unfold Word.oddSteps Collatz.AdjacentReturn.State.word
      simp only [OddOrbit.segment_length]
    unfold contractingGap totalExponent
    rw [← hlen]
    omega
  have hx : 0 < R.startValue :=
    O.value_pos R.startIndex
  have hprod : 0 < R.contractingGap * R.startValue :=
    Nat.mul_pos hgap hx
  have hid := R.contractingIdentity hC
  omega

/-- contracting枝では`2^length * Δ < 3^length`。 -/
theorem twoPow_length_mul_valueGap_lt_threePow
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    2 ^ R.length * R.valueGap < 3 ^ R.length := by
  have hdelta := R.twoPow_totalExponent_mul_valueGap_lt_affineConstant hC
  have hbudgetRaw := R.word_valid.twoPow_length_mul_affineConst_le
  have hbudget :
      2 ^ R.length * R.affineConstant ≤
        3 ^ R.length * 2 ^ R.totalExponent := by
    simpa [R.oddSteps_word, affineConstant, totalExponent] using hbudgetRaw
  have hscaled :
      2 ^ R.length * (2 ^ R.totalExponent * R.valueGap) <
        2 ^ R.length * R.affineConstant :=
    (Nat.mul_lt_mul_left (Nat.pow_pos (by omega : 0 < (2 : ℕ)))).2 hdelta
  have hwithH :
      (2 ^ R.length * R.valueGap) * 2 ^ R.totalExponent <
        3 ^ R.length * 2 ^ R.totalExponent := by
    calc
      (2 ^ R.length * R.valueGap) * 2 ^ R.totalExponent
          = 2 ^ R.length * (2 ^ R.totalExponent * R.valueGap) := by ring
      _ < 2 ^ R.length * R.affineConstant := hscaled
      _ ≤ 3 ^ R.length * 2 ^ R.totalExponent := hbudget
  exact (Nat.mul_lt_mul_right (Nat.pow_pos (by omega : 0 < (2 : ℕ)))).mp hwithH

/-- contracting枝のall-suffix sharp affine budget: `3B < r*2^H`。 -/
theorem three_mul_affineConstant_lt_length_mul_twoPow
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    3 * R.affineConstant < R.length * 2 ^ R.totalExponent := by
  have hAll := R.allSuffixesContracting hC
  have h := hAll.three_mul_affineConst_lt R.word_nonempty
  simpa [affineConstant, totalExponent, R.word_length] using h

/-- expanding枝のproper-prefix sharp affine bound。 -/
theorem affineConstant_le_length_mul_threePow_pred
    {O : OddOrbit} (R : State O) (hE : R.IsExpanding) :
    R.affineConstant ≤ R.length * 3 ^ (R.length - 1) := by
  have h := (R.properPrefixesExpanding hE).affineConst_le_sharp
  simpa [affineConstant, R.word_length] using h

/-- expanding枝の長さ2以上tailはall-suffix contracting。 -/
theorem tail_allSuffixesContracting
    {O : OddOrbit} (R : State O) (_hE : R.IsExpanding)
    (hlen : 1 < R.length) :
    (O.segment (R.startIndex + 1) (R.length - 1)).AllSuffixesContracting := by
  apply allSuffixesContracting_segment O
  intro k hk
  have hkWhole : k + 1 < R.length := by omega
  have hs := R.properSuffix_contracting (k := k + 1) (by omega) hkWhole
  have hindex : R.startIndex + (k + 1) = R.startIndex + 1 + k := by omega
  have hlenEq : R.length - (k + 1) = (R.length - 1) - k := by omega
  rw [hindex, hlenEq] at hs
  exact hs

/-- expanding枝のsuffix側sharp affine budget。 -/
theorem three_mul_affineConstant_lt_threePow_add_tail_twoPow
    {O : OddOrbit} (R : State O) (hE : R.IsExpanding)
    (hlen : 1 < R.length) :
    3 * R.affineConstant <
      3 ^ R.length + (R.length - 1) * 2 ^ R.totalExponent := by
  let tail : Collatz.Word := O.segment (R.startIndex + 1) (R.length - 1)
  have htailNe : tail ≠ [] := by
    intro hnil
    have hlen0 := congrArg List.length hnil
    dsimp [tail] at hlen0
    simp at hlen0
    omega
  have htailAll : tail.AllSuffixesContracting := by
    simpa [tail] using R.tail_allSuffixesContracting hE hlen
  have htailBound : 3 * tail.affineConst < tail.length * 2 ^ tail.twoSteps :=
    htailAll.three_mul_affineConst_lt htailNe
  have hword := R.word_eq_startExponent_cons_tail
  have hstartExp := R.startExponent_eq_one
  have hword' : R.word = 1 :: tail := by simpa [tail, hstartExp] using hword
  have htailLength : tail.length = R.length - 1 := by simp [tail]
  have hH : R.totalExponent = tail.twoSteps + 1 := by
    unfold totalExponent
    rw [hword']
    simp [Nat.add_comm]
  have hB : R.affineConstant =
      3 ^ (R.length - 1) + 2 * tail.affineConst := by
    unfold affineConstant
    rw [hword']
    simp [Word.affineConst, htailLength]
  have hscaled :
      3 * (2 * tail.affineConst) <
        (R.length - 1) * 2 ^ R.totalExponent := by
    have hmul := (Nat.mul_lt_mul_left (by omega : 0 < (2 : ℕ))).2 htailBound
    rw [hH, pow_succ]
    simpa [htailLength, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  rw [hB]
  have hpow : 3 * 3 ^ (R.length - 1) = 3 ^ R.length := by
    have hlenOne : 1 ≤ R.length := Nat.le_of_lt hlen
    calc
      3 * 3 ^ (R.length - 1) = 3 ^ (R.length - 1) * 3 := by ring
      _ = 3 ^ ((R.length - 1) + 1) := by rw [pow_succ]
      _ = 3 ^ R.length := by rw [Nat.sub_add_cancel hlenOne]
  omega

/-- expanding枝の全consecutive proper-prefix pairに`7/4` bound。 -/
theorem prefixPair_seven_fourths_bound
    {O : OddOrbit} (R : State O) (hE : R.IsExpanding)
    {j : ℕ} (hj : 0 < j) (hnext : j + 1 < R.length) :
    4 *
        (3 * 2 ^ (O.segment R.startIndex j).twoSteps +
          2 ^ ((O.segment R.startIndex j).twoSteps +
            O.exponent (R.startIndex + j))) <
      7 * 3 ^ (j + 1) := by
  have hproper := R.properPrefixesExpanding hE
  have hjWord : j < R.word.length := by rw [R.word_length]; omega
  have hj1Word : j + 1 < R.word.length := by rw [R.word_length]; exact hnext
  have hE0 := hproper j hj hjWord
  have hE1 := hproper (j + 1) (by omega) hj1Word
  have hjLe : j ≤ R.length := by omega
  have hj1Le : j + 1 ≤ R.length := by omega
  rw [R.word_take_eq_segment hjLe] at hE0
  rw [R.word_take_eq_segment hj1Le] at hE1
  have h0 : 2 ^ (O.segment R.startIndex j).twoSteps < 3 ^ j := by
    simpa [Word.Expanding, Word.oddSteps] using hE0
  have h1raw :
      2 ^ (O.segment R.startIndex (j + 1)).twoSteps < 3 ^ (j + 1) := by
    simpa [Word.Expanding, Word.oddSteps] using hE1
  have hstep :
      (O.segment R.startIndex (j + 1)).twoSteps =
        (O.segment R.startIndex j).twoSteps + O.exponent (R.startIndex + j) := by
    rw [show j + 1 = j + 1 by rfl, O.segment_add R.startIndex j 1]
    simp [Word.twoSteps, Nat.add_comm]
  rw [hstep] at h1raw
  exact Word.prefixPair_seven_fourths_bound
    (O.exponent_pos (R.startIndex + j)) h0 h1raw

end State
end AdjacentReturn
end Collatz
