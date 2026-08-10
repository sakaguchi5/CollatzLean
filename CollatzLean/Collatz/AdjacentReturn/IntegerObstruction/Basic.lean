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

/--
長さ2以上なら標準 adjacent return の tail は非空。
-/
theorem tail_ne_nil_of_length_two_le
    (B : BlockArithmeticData)
    (hlen : 1 < B.length) :
    B.tail ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [B.tail_length]
  omega


/--
長さ2以上なら標準 adjacent return の tail 全体は contracting。
-/
theorem tail_contracting_of_length_two_le
    (B : BlockArithmeticData)
    (hlen : 1 < B.length) :
    B.tail.Contracting := by
  have htailNe : B.tail ≠ [] :=
    tail_ne_nil_of_length_two_le B hlen
  exact
    (B.tail_allSuffixesContracting hlen).whole htailNe


/--
標準 adjacent return の total exponent は
tail の twoSteps に最初の1段を加えたもの。
-/
theorem totalExponent_eq_tail_twoSteps_add_one
    (B : BlockArithmeticData) :
    B.totalExponent = B.tail.twoSteps + 1 := by
  calc
    B.totalExponent = B.word.twoSteps :=
      B.totalExponent_eq
    _ = Word.twoSteps (1 :: B.tail) := by
      rw [B.word_eq_one_cons_tail]
    _ = B.tail.twoSteps + 1 := by
      simp [Word.twoSteps, Nat.add_comm]


/--
長さ2以上なら contracting tail から

`3^(r-1) < 2^(tail.twoSteps)`

を得る。
-/
theorem threePow_pred_lt_tail_twoPow
    (B : BlockArithmeticData)
    (hlen : 1 < B.length) :
    3 ^ (B.length - 1) < 2 ^ B.tail.twoSteps := by
  have htailC :
      B.tail.Contracting :=
    tail_contracting_of_length_two_le B hlen
  unfold Word.Contracting at htailC
  simpa [Word.oddSteps, B.tail_length] using htailC


/--
長さ2以上の標準 adjacent return の純算術 block では、枝に依存せず

`2 * 3^(r-1) < 2^H`。
-/
theorem two_mul_threePow_pred_lt_twoPow
    (B : BlockArithmeticData)
    (hlen : 1 < B.length) :
    2 * 3 ^ (B.length - 1) < 2 ^ B.totalExponent := by
  have htail :
      3 ^ (B.length - 1) < 2 ^ B.tail.twoSteps :=
    threePow_pred_lt_tail_twoPow B hlen
  have hH :
      B.totalExponent = B.tail.twoSteps + 1 :=
    totalExponent_eq_tail_twoSteps_add_one B
  have hscaled :
      2 * 3 ^ (B.length - 1) <
        2 * 2 ^ B.tail.twoSteps := by
    exact
      (Nat.mul_lt_mul_left
        (by omega : 0 < (2 : ℕ))).2 htail
  rw [hH, pow_succ]
  simpa [
    Nat.mul_assoc,
    Nat.mul_comm,
    Nat.mul_left_comm
  ] using hscaled

end BlockArithmeticData
end IntegerObstruction

namespace State

/--
長さ2以上の標準 adjacent return では、Expanding/Contracting の枝に依存せず
`2 * 3^(r-1) < 2^H`。
-/
theorem two_mul_threePow_pred_lt_twoPow
    {O : OddOrbit} (R : State O)
    (hlen : 1 < R.length) :
    2 * 3 ^ (R.length - 1) < 2 ^ R.totalExponent := by
  let B := IntegerObstruction.BlockArithmeticData.ofState R
  have hBlen : 1 < B.length := by
    change 1 < R.length
    exact hlen
  have h := B.two_mul_threePow_pred_lt_twoPow hBlen
  change 2 * 3 ^ (R.length - 1) < 2 ^ R.totalExponent at h
  exact h

end State
end AdjacentReturn
end Collatz
