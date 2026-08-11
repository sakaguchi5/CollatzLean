import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.NaturalZeroReplayArithmetic
import CollatzLean.Collatz.Word.AffineLowerBound
import CollatzLean.Collatz.Word.SuffixExponentBound
import CollatzLean.Collatz.FiniteOrbit.Determinism
import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# natural j=0 packet の bidirectional decoder 準備

natural sign-change packet の tail `v` では

* forward: start `s = 6*(n+d)-1` から actual odd-only step が一意に決まる
* backward: `AllSuffixesContracting v` により全非空 suffix が
  `3^r < 2^K` を満たす

という二方向の拘束が同時に存在する。
このファイルでは meet-in-the-middle contradiction の直前までに必要な
bridge theorem をまとめる。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/-- tail の actual first exponent。 -/
def tailFirstExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  O.exponent (R.startIndex + D.cut)

/-- tail の actual terminal step exponent。 -/
def tailLastExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (_D : NaturalZeroReplaySignChangeData F) : ℕ :=
  O.exponent (R.startIndex + (F.length - 1))

/-- natural tail は canonical start から canonical end への actual run。 -/
theorem tail_runs
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.Runs D.tailWord
      (Word.canonicalStart D.tailWord)
      (Word.canonicalEnd D.tailWord) := by
  have hcutLe : D.cut ≤ F.length := Nat.le_of_lt D.cut_lt
  have hsum : D.cut + (F.length - D.cut) = F.length :=
    Nat.add_sub_of_le hcutLe
  have hrun :=
    O.runsSegment (R.startIndex + D.cut) (F.length - D.cut)
  rw [tailWord, ← D.cutStart_eq, ← D.cutEnd_eq]
  simpa [suffixWord, boundaryValue, FirstCrossingData.endpointValue,
    Nat.add_assoc, hsum] using hrun

/--
canonical start と tail length が同じ actual run は natural tail 自身しかない。
forward actual decoder の決定性。
-/
theorem tailWord_unique_of_runs_length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {w : Collatz.Word} {z : ℕ}
    (hRuns : Word.Runs w (Word.canonicalStart D.tailWord) z)
    (hLength : w.length = D.tailWord.length) :
    w = D.tailWord ∧ z = Word.canonicalEnd D.tailWord := by
  exact hRuns.unique_of_same_start_same_length D.tail_runs hLength

/-- `3*s+1 = 2*(9*(n+d)-1)`。forward decoder の最初の numerator。 -/
theorem firstNumerator_factorization
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    3 * Word.canonicalStart D.tailWord + 1 =
      2 * (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1) := by
  have hs := D.arithmeticData.tailStart_add_one
  have hq : 0 < D.arithmeticData.n + D.arithmeticData.d := by
    omega
  omega

/--
actual first step は `2*(9*(n+d)-1)` の exact 2進分解。
従って first exponent はこの整数の exact 2進指数として一意。
-/
theorem firstExponent_exactFactor
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Collatz.TwoAdic.ExactFactor
      (2 * (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1))
      D.tailFirstExponent
      (O.value (R.startIndex + D.cut + 1)) := by
  have hstep := O.step (R.startIndex + D.cut)
  have hstart :
      O.value (R.startIndex + D.cut) =
        Word.canonicalStart D.tailWord := by
    change boundaryValue F D.cut = Word.canonicalStart D.tailWord
    simpa [tailWord] using D.cutStart_eq
  have hnum := D.firstNumerator_factorization
  constructor
  · calc
      2 * (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1)
          = 3 * Word.canonicalStart D.tailWord + 1 := hnum.symm
      _ = 3 * O.value (R.startIndex + D.cut) + 1 := by rw [hstart]
      _ = 2 ^ D.tailFirstExponent *
            O.value (R.startIndex + D.cut + 1) := by
              simpa [tailFirstExponent, Nat.add_assoc] using hstep.symm
  · exact O.value_odd _

/--
`9*(n+d)-1 = 2^r*u` が exact なら natural tail の first exponent は `r+1`。
-/
theorem tailFirstExponent_eq_succ_of_exactFactor
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r u : ℕ}
    (hFactor :
      Collatz.TwoAdic.ExactFactor
        (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1) r u) :
    D.tailFirstExponent = r + 1 := by
  have hn : 0 < D.arithmeticData.n :=
    D.arithmeticData.n_pos
  have hd : 0 < D.arithmeticData.d :=
    D.arithmeticData.d_pos
  have hq :
      0 < D.arithmeticData.n + D.arithmeticData.d := by
    omega
  have hbasePos :
      0 < 9 * (D.arithmeticData.n + D.arithmeticData.d) - 1 := by
    omega
  have hLift :
      Collatz.TwoAdic.ExactFactor
        (2 * (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1))
        (r + 1) u := by
    constructor
    · rw [hFactor.1, pow_succ]
      ring
    · exact hFactor.2
  exact Collatz.TwoAdic.exponent_unique D.firstExponent_exactFactor hLift

/-- terminal exponent は正。 -/
theorem tailLastExponent_pos
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    0 < D.tailLastExponent := by
  exact O.exponent_pos _

/-- endpoint の `mod 3` は descent half-gap `d` だけで決まる。 -/
theorem endpoint_mod_three_cases
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    (D.arithmeticData.d % 3 = 0 ∧
        Word.canonicalEnd D.tailWord % 3 = 2) ∨
      (D.arithmeticData.d % 3 = 2 ∧
        Word.canonicalEnd D.tailWord % 3 = 1) := by
  have hdNe := D.arithmeticData_d_mod_three_ne_one
  have htNe : Word.canonicalEnd D.tailWord % 3 ≠ 0 := by
    intro hzero
    apply FirstCrossingData.endpoint_mod_three_ne_zero F
    rw [D.cutEnd_eq]
    simpa [tailWord] using hzero
  have hdLt : D.arithmeticData.d % 3 < 3 := Nat.mod_lt _ (by omega)
  have htLt : Word.canonicalEnd D.tailWord % 3 < 3 :=
    Nat.mod_lt _ (by omega)
  have htEq := D.arithmeticData.endpoint_add_one
  omega

/-- terminal actual step equation。 -/
theorem tailLastStep
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    2 ^ D.tailLastExponent * Word.canonicalEnd D.tailWord =
      3 * O.value (R.startIndex + (F.length - 1)) + 1 := by
  have hp : 0 < F.length := F.length_pos
  let k := F.length - 1
  have hk : k + 1 = F.length := by
    dsimp [k]
    omega
  have hstep := O.step (R.startIndex + k)
  have hidx :
      R.startIndex + k + 1 = R.startIndex + F.length := by
    omega
  have hend :
      O.value (R.startIndex + k + 1) =
        Word.canonicalEnd D.tailWord := by
    rw [hidx]
    change F.endpointValue = Word.canonicalEnd D.tailWord
    simpa [tailWord] using D.cutEnd_eq
  dsimp [tailLastExponent]
  rw [hend] at hstep
  simpa [k, Nat.add_assoc] using hstep

/-- `2^(2*k) mod 3 = 1`。 -/
private theorem twoPow_evenShape_mod_three (k : ℕ) :
    2 ^ (k + k) % 3 = 1 := by
  have hpow : 2 ^ (k + k) = (4 : ℕ) ^ k := by
    rw [pow_add]
    have : 2 ^ k * 2 ^ k = (2 * 2) ^ k := by
      rw [mul_pow]
    simpa using this
  rw [hpow, Nat.pow_mod]
  norm_num

/-- `2^(2*k+1) mod 3 = 2`。 -/
private theorem twoPow_oddShape_mod_three (k : ℕ) :
    2 ^ (k + k + 1) % 3 = 2 := by
  rw [pow_succ, Nat.mul_mod]
  rw [twoPow_evenShape_mod_three]

/-- `d = 0 mod 3` なら terminal exponent は奇数。 -/
theorem tailLastExponent_odd_of_d_mod_three_zero
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (hd : D.arithmeticData.d % 3 = 0) :
    Odd D.tailLastExponent := by
  have htmod : Word.canonicalEnd D.tailWord % 3 = 2 := by
    rcases D.endpoint_mod_three_cases with h | h
    · exact h.2
    · omega
  have hstep := D.tailLastStep
  have hmodEq :
      ((2 ^ D.tailLastExponent % 3) *
          (Word.canonicalEnd D.tailWord % 3)) % 3 = 1 := by
    have hstepMod := congrArg (fun z : ℕ => z % 3) hstep
    simpa [Nat.add_mod, Nat.mul_mod] using hstepMod
  obtain ⟨k, heven | hodd⟩ := D.tailLastExponent.even_or_odd'
  · have hpow : 2 ^ D.tailLastExponent % 3 = 1 := by
      rw [heven]
      simpa [two_mul] using (twoPow_evenShape_mod_three k)
    rw [hpow, htmod] at hmodEq
    norm_num at hmodEq
  · exact ⟨k, hodd⟩

/-- `d = 2 mod 3` なら terminal exponent は偶数。 -/
theorem tailLastExponent_even_of_d_mod_three_two
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (hd : D.arithmeticData.d % 3 = 2) :
    Even D.tailLastExponent := by
  have htmod : Word.canonicalEnd D.tailWord % 3 = 1 := by
    rcases D.endpoint_mod_three_cases with h | h
    · omega
    · exact h.2
  have hstep := D.tailLastStep
  have hmodEq :
      ((2 ^ D.tailLastExponent % 3) *
          (Word.canonicalEnd D.tailWord % 3)) % 3 = 1 := by
    have hstepMod := congrArg (fun z : ℕ => z % 3) hstep
    simpa [Nat.add_mod, Nat.mul_mod] using hstepMod
  obtain ⟨k, heven | hodd⟩ := D.tailLastExponent.even_or_odd'
  · exact ⟨k, by simpa [two_mul] using heven⟩
  · have hpow : 2 ^ D.tailLastExponent % 3 = 2 := by
      rw [hodd]
      simpa [two_mul] using (twoPow_oddShape_mod_three k)
    rw [hpow, htmod] at hmodEq
    norm_num at hmodEq

/-- natural tail の任意 decoder residual は universal affine lower bound を満たす。 -/
theorem tail_decoderResidual_lowerBound
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) (k : ℕ) :
    3 ^ Word.oddSteps (D.tailWord.drop k) -
        2 ^ Word.oddSteps (D.tailWord.drop k) ≤
      Word.affineConst (D.tailWord.drop k) := by
  exact D.tail_valid.decoderResidual_lowerBound k

/-- natural tail の全非空 suffix に backward cumulative exponent bound がある。 -/
theorem tail_drop_threePow_lt_twoPow
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hk : k < D.tailWord.length) :
    3 ^ Word.oddSteps (D.tailWord.drop k) <
      2 ^ Word.twoSteps (D.tailWord.drop k) := by
  exact D.tail_allSuffixesContracting.threePow_drop_lt_twoPow_drop hk

end FirstCrossingData.NaturalZeroReplaySignChangeData
end PositiveReturn
end AdjacentReturn
end Collatz
