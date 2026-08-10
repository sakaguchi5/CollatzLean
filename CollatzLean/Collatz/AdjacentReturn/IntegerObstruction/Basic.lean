import CollatzLean.Collatz.AdjacentReturn.Bounds

/-!
# adjacent return の純算術 block

実際の標準 future-minimum 間の一区間から、軌道そのものを忘れて
今後の整数論に必要な有限データだけを取り出す。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/--
標準 adjacent return 一区間の純算術データ。
`startValue + valueGap` が次の future-minimum 値を表す。
-/
structure BlockArithmeticData where
  startValue : ℕ
  valueGap : ℕ
  length : ℕ
  word : Collatz.Word
  totalExponent : ℕ
  affineConstant : ℕ
  tail : Collatz.Word
  startValue_pos : 0 < startValue
  valueGap_pos : 0 < valueGap
  length_pos : 0 < length
  start_odd : Odd startValue
  next_odd : Odd (startValue + valueGap)
  valueGap_four_multiple : ∃ q : ℕ, valueGap = 4 * q
  word_valid : word.Valid
  word_length : word.length = length
  totalExponent_eq : totalExponent = word.twoSteps
  affineConstant_eq : affineConstant = word.affineConst
  word_eq_one_cons_tail : word = 1 :: tail
  tail_length : tail.length = length - 1
  tail_allSuffixesContracting :
    1 < length → tail.AllSuffixesContracting
  scaledEquation :
    2 ^ totalExponent * (startValue + valueGap) =
      3 ^ length * startValue + affineConstant

namespace BlockArithmeticData

/-- 実際の adjacent state から純算術 block を取り出す。 -/
def ofState
    {O : OddOrbit} (R : State O) : BlockArithmeticData := by
  let tail : Collatz.Word :=
    O.segment (R.startIndex + 1) (R.length - 1)
  refine {
    startValue := R.startValue
    valueGap := R.valueGap
    length := R.length
    word := R.word
    totalExponent := R.totalExponent
    affineConstant := R.affineConstant
    tail := tail
    startValue_pos := O.value_pos R.startIndex
    valueGap_pos := R.valueGap_pos
    length_pos := R.length_pos
    start_odd := ?_
    next_odd := ?_
    valueGap_four_multiple := R.valueGap_four_dvd
    word_valid := R.word_valid
    word_length := R.word_length
    totalExponent_eq := rfl
    affineConstant_eq := rfl
    word_eq_one_cons_tail := ?_
    tail_length := ?_
    tail_allSuffixesContracting := ?_
    scaledEquation := ?_
  }
  · unfold State.startValue
    exact O.value_odd _
  · rw [← R.nextValue_eq_startValue_add_valueGap]
    unfold State.nextValue
    exact O.value_odd _
  · have hword := R.word_eq_startExponent_cons_tail
    rw [R.startExponent_eq_one] at hword
    simpa [tail] using hword
  · simp [tail]
  · intro hlen
    simpa [tail] using R.tail_allSuffixesContracting hlen
  · have h := R.scaledEquation
    rw [R.nextValue_eq_startValue_add_valueGap] at h
    exact h

/-- 次値の略記。 -/
def nextValue (B : BlockArithmeticData) : ℕ :=
  B.startValue + B.valueGap

/-- adjacent 値差は少なくとも4。 -/
theorem four_le_valueGap (B : BlockArithmeticData) : 4 ≤ B.valueGap := by
  obtain ⟨q, hq⟩ := B.valueGap_four_multiple
  rw [hq]
  have hgapPos : 0 < B.valueGap := B.valueGap_pos
  have hqPos : 0 < q := by
    rw [hq] at hgapPos
    omega
  omega

/-- 先頭指数は1。 -/
theorem firstExponent_eq_one (B : BlockArithmeticData) :
    B.word.head? = some 1 := by
  rw [B.word_eq_one_cons_tail]
  rfl

end BlockArithmeticData
end IntegerObstruction
end AdjacentReturn
end Collatz
