import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.BidirectionalDecoder
import CollatzLean.Collatz.Word.SuffixGapBudgetLower
import CollatzLean.Collatz.Word.AffineResidualSignature
import CollatzLean.Collatz.Word.ExponentSlope
import CollatzLean.Collatz.FiniteOrbit.PrefixDeterminism
import CollatzLean.Collatz.TwoAdic.FactorizationOrder
import Mathlib.Data.Nat.GCD.Basic

/-!
# bidirectional decoder の自然強化

natural zero-replay sign-change packet から直ちに追加できる拘束を集約する。

* first exponent の mod 8 型分類
* first step の endpoint に対する位置と early collision 排除
* `d + 1 != 3*n`
* suffix gap budget の定量化による `6*n+2 <= m`
* contracting slope `19*m+7 < 12*J`
* terminal exponent の sharp lower bound
* head-weighted affine lower bound
* tail/prepend contracting gap の coprime 性と gcd restriction
* residual 1〜3文字 exact signature への bridge

meet-in-the-middle obstruction の入力 packet。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/-- `q = n+d` の短い名前。 -/
noncomputable def coordinateSum
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  D.arithmeticData.n + D.arithmeticData.d

/-- natural tail の first actual next value。 -/
def tailFirstValue
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  O.value (R.startIndex + D.cut + 1)

/-- total exponent の length 超過分。 -/
def tailExcess
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ :=
  D.tailExponent - D.tailLength

/--
`q=2*k` なら `9*q-1` は奇数なので first exponent は1。
-/
theorem tailFirstExponent_eq_one_of_coordinateSum_eq_two_mul
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hq : D.coordinateSum = k + k) :
    D.tailFirstExponent = 1 := by
  have hn : 0 < D.arithmeticData.n :=
    D.arithmeticData.n_pos
  have hd : 0 < D.arithmeticData.d :=
    D.arithmeticData.d_pos
  have hqpos : 0 < D.coordinateSum := by
    dsimp [coordinateSum]
    omega
  have hkpos : 0 < k := by
    omega
  have hodd :
      Odd (9 * D.coordinateSum - 1) := by
    refine ⟨9 * k - 1, ?_⟩
    rw [hq]
    omega
  have hFactor :
      Collatz.TwoAdic.ExactFactor
        (9 * D.coordinateSum - 1)
        0
        (9 * D.coordinateSum - 1) := by
    exact ⟨by simp, hodd⟩
  have h :=
    D.tailFirstExponent_eq_succ_of_exactFactor
      (by simpa [coordinateSum] using hFactor)
  omega

/--
`q=4*k+3` なら `9*q-1 = 2*(18*k+13)` で odd part は奇数。
従って first exponent は2。
-/
theorem tailFirstExponent_eq_two_of_coordinateSum_eq_four_mul_add_three
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hq : D.coordinateSum = 4 * k + 3) :
    D.tailFirstExponent = 2 := by
  have hodd : Odd (18 * k + 13) := by
    refine ⟨9 * k + 6, ?_⟩
    omega
  have hFactor :
      Collatz.TwoAdic.ExactFactor
        (9 * D.coordinateSum - 1)
        1
        (18 * k + 13) := by
    constructor
    · rw [hq]
      norm_num
      omega
    · exact hodd
  have h :=
    D.tailFirstExponent_eq_succ_of_exactFactor
      (by simpa [coordinateSum] using hFactor)
  omega

/-- `q=8*k+3` なら first exponent は2。 -/
theorem tailFirstExponent_eq_two_of_coordinateSum_eq_eight_mul_add_three
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hq : D.coordinateSum = 8 * k + 3) :
    D.tailFirstExponent = 2 := by
  apply D.tailFirstExponent_eq_two_of_coordinateSum_eq_four_mul_add_three
    (k := 2 * k)
  omega

/-- `q=8*k+7` なら first exponent は2。 -/
theorem tailFirstExponent_eq_two_of_coordinateSum_eq_eight_mul_add_seven
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hq : D.coordinateSum = 8 * k + 7) :
    D.tailFirstExponent = 2 := by
  apply D.tailFirstExponent_eq_two_of_coordinateSum_eq_four_mul_add_three
    (k := 2 * k + 1)
  omega

/-- `q=8*k+5` なら first exponent は3。 -/
theorem tailFirstExponent_eq_three_of_coordinateSum_eq_eight_mul_add_five
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hq : D.coordinateSum = 8 * k + 5) :
    D.tailFirstExponent = 3 := by
  have hodd : Odd (18 * k + 11) := by
    refine ⟨9 * k + 5, ?_⟩
    omega
  have hFactor :
      Collatz.TwoAdic.ExactFactor
        (9 * D.coordinateSum - 1)
        2
        (18 * k + 11) := by
    constructor
    · rw [hq]
      norm_num
      omega
    · exact hodd
  have h :=
    D.tailFirstExponent_eq_succ_of_exactFactor
      (by simpa [coordinateSum] using hFactor)
  omega

/-- `q=8*k+1` なら numerator は少なくとも16を含むので first exponent は4以上。 -/
theorem four_le_tailFirstExponent_of_coordinateSum_eq_eight_mul_add_one
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hq : D.coordinateSum = 8 * k + 1) :
    4 ≤ D.tailFirstExponent := by
  have hpow :
      2 * (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1) =
        2 ^ 4 * (9 * k + 1) := by
    rw [← show D.coordinateSum =
        D.arithmeticData.n + D.arithmeticData.d by rfl, hq]
    norm_num
    omega
  exact
    D.firstExponent_exactFactor.exponent_ge_of_eq_twoPow_mul hpow

/--
first exponent が1なら最初の next value は endpoint より上。
-/
theorem endpoint_lt_tailFirstValue_of_firstExponent_eq_one
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (he : D.tailFirstExponent = 1) :
    Word.canonicalEnd D.tailWord < D.tailFirstValue := by
  have hfac := D.firstExponent_exactFactor.1
  rw [he] at hfac
  norm_num at hfac
  have ht := D.arithmeticData.endpoint_add_one
  have hn := D.arithmeticData.n_pos
  have hd := D.arithmeticData.d_pos
  dsimp [tailFirstValue, coordinateSum] at *
  omega

/--
first exponent が2なら first next value と endpoint の差は
`2*y + 3*n = 2*t + d + 1` で exact に記録される。
-/
theorem firstValue_balance_of_firstExponent_eq_two
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (he : D.tailFirstExponent = 2) :
    2 * D.tailFirstValue + 3 * D.arithmeticData.n =
      2 * Word.canonicalEnd D.tailWord + D.arithmeticData.d + 1 := by
  have hfac := D.firstExponent_exactFactor.1
  rw [he] at hfac
  norm_num at hfac
  have ht := D.arithmeticData.endpoint_add_one
  dsimp [tailFirstValue, coordinateSum] at *
  omega

/--
first exponent が3以上なら最初の next value は endpoint より下。
-/
theorem tailFirstValue_lt_endpoint_of_three_le_firstExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (he : 3 ≤ D.tailFirstExponent) :
    D.tailFirstValue < Word.canonicalEnd D.tailWord := by
  have hfac := D.firstExponent_exactFactor.1
  have hp :
      8 ≤ 2 ^ D.tailFirstExponent := by
    have h :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) he
    norm_num at h
    exact h
  have hscaled :
      8 * D.tailFirstValue ≤
        2 ^ D.tailFirstExponent * D.tailFirstValue := by
    exact Nat.mul_le_mul_right D.tailFirstValue hp
  have hscaled' :
      8 * D.tailFirstValue ≤
        2 * (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1) := by
    rw [hfac]
    exact hscaled
  have ht := D.arithmeticData.endpoint_add_one
  have hn := D.arithmeticData.n_pos
  have hd := D.arithmeticData.d_pos
  have hnumLt :
      2 * (9 * (D.arithmeticData.n + D.arithmeticData.d) - 1) <
        8 * Word.canonicalEnd D.tailWord := by
    omega
  have h8 :
      8 * D.tailFirstValue <
        8 * Word.canonicalEnd D.tailWord :=
    lt_of_le_of_lt hscaled' hnumLt
  omega

/--
natural tail の途中では endpoint を早期再訪しない。
`k < tailLength` なら cut から `k` step 後の actual value は最終 endpoint と異なる。
-/
theorem tail_value_ne_endpoint_of_lt_length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hk : k < D.tailLength) :
    O.value (R.startIndex + D.cut + k) ≠
      Word.canonicalEnd D.tailWord := by
  intro heq
  have hlenEq :
      D.tailLength = F.length - D.cut := by
    simp [tailLength, tailWord, suffixWord, Word.oddSteps]
  have hcutk : D.cut + k < F.length := by
    rw [hlenEq] at hk
    omega
  have hend :
      Word.canonicalEnd D.tailWord = F.endpointValue := by
    simpa [tailWord] using D.cutEnd_eq.symm
  have hactual :
      O.value (R.startIndex + D.cut + k) =
        O.value (R.startIndex + F.length) := by
    rw [hend] at heq
    simpa [FirstCrossingData.endpointValue, Nat.add_assoc] using heq
  have hindex :=
    (O.value_injective_of_unbounded R.unbounded) hactual
  omega

/--
tail の first actual value は、tail endpoint を早期再訪しない。
-/
theorem tailFirstValue_ne_endpoint
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.tailFirstValue ≠ Word.canonicalEnd D.tailWord := by
  have hlen := D.six_mul_n_le_tailLength
  have hn := D.arithmeticData.n_pos
  have hk : 1 < D.tailLength := by
    omega
  change
    O.value (R.startIndex + D.cut + 1) ≠
      Word.canonicalEnd D.tailWord
  exact D.tail_value_ne_endpoint_of_lt_length hk

/--
`d+1=3*n` なら first exponent は2になり、step 1 で endpoint を再訪してしまう。
従ってこれは不可能。
-/
theorem arithmeticData_d_add_one_ne_three_mul_n
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.arithmeticData.d + 1 ≠ 3 * D.arithmeticData.n := by
  intro hd
  have hn := D.arithmeticData.n_pos
  have hq :
      D.coordinateSum =
        4 * (D.arithmeticData.n - 1) + 3 := by
    dsimp [coordinateSum]
    omega
  have he :=
    D.tailFirstExponent_eq_two_of_coordinateSum_eq_four_mul_add_three hq
  have hbal := D.firstValue_balance_of_firstExponent_eq_two he
  have heq :
      D.tailFirstValue = Word.canonicalEnd D.tailWord := by
    omega
  exact D.tailFirstValue_ne_endpoint heq

/-- subtraction 形の corollary: `d != 3*n-1`。 -/
theorem arithmeticData_d_ne_three_mul_n_sub_one
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.arithmeticData.d ≠ 3 * D.arithmeticData.n - 1 := by
  intro hd
  apply D.arithmeticData_d_add_one_ne_three_mul_n
  have hn := D.arithmeticData.n_pos
  omega

/--
prepend-one contracting から `19*m+7 < 12*J`。
-/
theorem nineteen_mul_tailLength_add_seven_lt_twelve_mul_tailExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    19 * D.tailLength + 7 < 12 * D.tailExponent := by
  have hC0 :
      3 ^ (D.tailLength + 1) <
        2 ^ (1 + D.tailExponent) := by
    simpa [tailLength, tailExponent, Word.Contracting] using
      D.prepend_contracting
  have hC :
      3 ^ (D.tailLength + 1) <
        2 ^ (D.tailExponent + 1) := by
    rw [Nat.add_comm D.tailExponent 1]
    exact hC0
  have hslope :=
    Word.nineteen_mul_lt_twelve_mul_of_threePow_lt_twoPow
      (m := D.tailLength + 1)
      (J := D.tailExponent + 1)
      (by omega)
      hC
  omega

/-- tail exponent は length 以上。 -/
theorem tailLength_le_tailExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.tailLength ≤ D.tailExponent := by
  simpa [tailLength, tailExponent] using
    Word.oddSteps_le_twoSteps D.tail_valid

/--
slope bound を excess exponent `J-m` で書いた形。
-/
theorem seven_mul_tailLength_add_one_lt_twelve_mul_tailExcess
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    7 * (D.tailLength + 1) < 12 * D.tailExcess := by
  have hslope :=
    D.nineteen_mul_tailLength_add_seven_lt_twelve_mul_tailExponent
  have hle := D.tailLength_le_tailExponent
  have hsplit :
      D.tailLength + D.tailExcess = D.tailExponent := by
    dsimp [tailExcess]
    exact Nat.add_sub_of_le hle
  omega

/--
natural tail は既に長さ6以上なので最後4 suffix の定量 budget を使える。
その結果 `6*n+1 <= m`。
-/
theorem six_mul_n_add_one_le_tailLength
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    6 * D.arithmeticData.n + 1 ≤ D.tailLength := by
  have hOld := D.six_mul_n_le_tailLength
  have hn := D.arithmeticData.n_pos
  have hlen4 : 4 ≤ D.tailLength := by omega
  have hBudget :
      2 ^ D.tailExponent <
        Word.suffixGapBudget D.tailWord := by
    simpa [tailLength, tailExponent] using
      D.tail_allSuffixesContracting.twoPow_lt_suffixGapBudget_of_four_le_length
        (by simpa [tailLength, Word.oddSteps] using hlen4)
  have hEq := D.exact_suffixGapBudget
  have hApos : 0 < 2 ^ D.tailExponent :=
    Nat.pow_pos (by omega)
  have hGpos : 0 < D.prependGap := D.prependGap_pos
  have hspos : 0 < Word.canonicalStart D.tailWord := by
    unfold tailWord
    rw [← D.cutStart_eq]
    unfold boundaryValue
    exact O.value_pos _
  have hGspos :
      0 < D.prependGap * Word.canonicalStart D.tailWord :=
    Nat.mul_pos hGpos hspos
  have hlt :
      (6 * D.arithmeticData.n + 1) * 2 ^ D.tailExponent <
        (D.tailLength + 1) * 2 ^ D.tailExponent := by
    calc
      (6 * D.arithmeticData.n + 1) * 2 ^ D.tailExponent
          =
        6 * D.arithmeticData.n * 2 ^ D.tailExponent +
          2 ^ D.tailExponent := by ring
      _ <
        6 * D.arithmeticData.n * 2 ^ D.tailExponent +
          Word.suffixGapBudget D.tailWord :=
            Nat.add_lt_add_left hBudget _
      _ <
        D.prependGap * Word.canonicalStart D.tailWord +
          6 * D.arithmeticData.n * 2 ^ D.tailExponent +
          Word.suffixGapBudget D.tailWord := by
            omega
      _ =
        (D.tailLength + 1) * 2 ^ D.tailExponent := hEq.symm
  have hcoef :
      6 * D.arithmeticData.n + 1 < D.tailLength + 1 := by
    exact (Nat.mul_lt_mul_right hApos).mp (by
      simpa [Nat.mul_assoc] using hlt)
  omega

/--
長さが7以上になった後は最後7 suffix の budget が `2*A` を越える。
従って最終的に `6*n+2 <= m`。
-/
theorem six_mul_n_add_two_le_tailLength
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    6 * D.arithmeticData.n + 2 ≤ D.tailLength := by
  have hOne := D.six_mul_n_add_one_le_tailLength
  have hn := D.arithmeticData.n_pos
  have hlen7 : 7 ≤ D.tailLength := by omega
  have hBudget :
      2 * 2 ^ D.tailExponent <
        Word.suffixGapBudget D.tailWord := by
    simpa [tailLength, tailExponent] using
      D.tail_allSuffixesContracting.two_mul_twoPow_lt_suffixGapBudget_of_seven_le_length
        (by simpa [tailLength, Word.oddSteps] using hlen7)
  have hEq := D.exact_suffixGapBudget
  have hApos : 0 < 2 ^ D.tailExponent :=
    Nat.pow_pos (by omega)
  have hGpos : 0 < D.prependGap := D.prependGap_pos
  have hspos : 0 < Word.canonicalStart D.tailWord := by
    unfold tailWord
    rw [← D.cutStart_eq]
    unfold boundaryValue
    exact O.value_pos _
  have hGspos :
      0 < D.prependGap * Word.canonicalStart D.tailWord :=
    Nat.mul_pos hGpos hspos
  have hlt :
      (6 * D.arithmeticData.n + 2) * 2 ^ D.tailExponent <
        (D.tailLength + 1) * 2 ^ D.tailExponent := by
    calc
      (6 * D.arithmeticData.n + 2) * 2 ^ D.tailExponent
          =
        6 * D.arithmeticData.n * 2 ^ D.tailExponent +
          2 * 2 ^ D.tailExponent := by ring
      _ <
        6 * D.arithmeticData.n * 2 ^ D.tailExponent +
          Word.suffixGapBudget D.tailWord :=
            Nat.add_lt_add_left hBudget _
      _ <
        D.prependGap * Word.canonicalStart D.tailWord +
          6 * D.arithmeticData.n * 2 ^ D.tailExponent +
          Word.suffixGapBudget D.tailWord := by
            omega
      _ =
        (D.tailLength + 1) * 2 ^ D.tailExponent := hEq.symm
  have hcoef :
      6 * D.arithmeticData.n + 2 < D.tailLength + 1 := by
    exact (Nat.mul_lt_mul_right hApos).mp (by
      simpa [Nat.mul_assoc] using hlt)
  omega

/-- 強化された length bound と slope を合わせた excess lower bound。 -/
theorem fortyTwo_mul_n_add_twentyOne_lt_twelve_mul_tailExcess
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    42 * D.arithmeticData.n + 21 < 12 * D.tailExcess := by
  have hlen := D.six_mul_n_add_two_le_tailLength
  have hex := D.seven_mul_tailLength_add_one_lt_twelve_mul_tailExcess
  omega

/--
terminal one-letter suffix は contracting。
-/
theorem tailLastExponent_singleton_contracting
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.Contracting ([D.tailLastExponent] : Collatz.Word) := by
  have hp : 0 < F.length := F.length_pos
  let k := F.length - 1
  have hk : k < F.length := by
    dsimp [k]
    omega
  have hword := suffixWord_eq_cons F hk
  have hnext : suffixWord F (k + 1) = [] := by
    have hEq : k + 1 = F.length := by
      dsimp [k]
      omega
    rw [hEq]
    simp [suffixWord]
  rw [hnext] at hword
  have hAll :=
    FirstCrossingData.suffixWord_allSuffixesContracting
      F (Nat.le_of_lt hk)
  have hC :=
    Word.AllSuffixesContracting.whole
      (w := suffixWord F k)
      (by rw [hword]; simp)
      hAll
  dsimp [tailLastExponent]
  simpa [k] using (by
    rw [hword] at hC
    exact hC)

/-- terminal singleton の contracting 性から、terminal exponent は少なくとも2。 -/
theorem two_le_tailLastExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    2 ≤ D.tailLastExponent := by
  have hC := D.tailLastExponent_singleton_contracting
  have hpow : 3 < 2 ^ D.tailLastExponent := by
    simpa [Word.Contracting, Word.oddSteps, Word.twoSteps] using hC
  by_contra hnot
  have hle : D.tailLastExponent ≤ 1 := by omega
  interval_cases D.tailLastExponent <;> norm_num at hpow

/-- `d=0 mod3` branch では terminal exponent は奇数かつ2以上なので3以上。 -/
theorem three_le_tailLastExponent_of_d_mod_three_zero
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (hd : D.arithmeticData.d % 3 = 0) :
    3 ≤ D.tailLastExponent := by
  have hodd := D.tailLastExponent_odd_of_d_mod_three_zero hd
  have htwo := D.two_le_tailLastExponent
  rcases hodd with ⟨k, hk⟩
  omega

/--
natural tail の actual first exponent を使った affine lower bound。
-/
theorem tailAffine_firstExponent_lowerBound
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    3 ^ (D.tailLength - 1) +
        2 ^ D.tailFirstExponent *
          (3 ^ (D.tailLength - 1) - 2 ^ (D.tailLength - 1)) ≤
      D.tailAffine := by
  have hword :=
    suffixWord_eq_cons F D.cut_lt
  have hvalid := D.tail_valid
  rw [tailWord, hword] at hvalid
  have hbound :=
    hvalid.affineConst_cons_ge_headWeightedMinimum
  have hlen :
      Word.oddSteps (suffixWord F (D.cut + 1)) =
        D.tailLength - 1 := by
    have htail :
        D.tailLength =
          Word.oddSteps (suffixWord F (D.cut + 1)) + 1 := by
      rw [tailLength, tailWord, hword]
      simp
    omega
  rw [hlen] at hbound
  simpa [
    tailAffine,
    tailFirstExponent,
    tailWord,
    hword
  ] using hbound

/--
tail gap と prepend gap の補助 exact relation: `G + 3^m = 2*g`。
-/
theorem prependGap_add_threePow_eq_two_mul_tailGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.prependGap + 3 ^ D.tailLength = 2 * D.tailGap := by
  have htail :
      3 ^ D.tailLength + D.tailGap =
        2 ^ D.tailExponent := by
    unfold tailGap
    exact Nat.add_sub_of_le (Nat.le_of_lt (by
      simpa [tailExponent, tailLength, Word.Contracting] using
        D.tail_contracting))
  have hpre :
      3 ^ Word.oddSteps (1 :: D.tailWord) + D.prependGap =
        2 ^ Word.twoSteps (1 :: D.tailWord) := by
    unfold prependGap
    exact Nat.add_sub_of_le (Nat.le_of_lt (by
      simpa [Word.Contracting] using D.prepend_contracting))
  have hpre0 :
      3 ^ D.tailLength * 3 + D.prependGap =
        2 * 2 ^ D.tailExponent := by
    simpa only [
      tailLength,
      tailExponent,
      Word.oddSteps_cons,
      Word.twoSteps_cons,
      pow_add,
      pow_one
    ] using hpre
  have hpre' :
      3 * 3 ^ D.tailLength + D.prependGap =
        2 * 2 ^ D.tailExponent := by
    calc
      3 * 3 ^ D.tailLength + D.prependGap
          = 3 ^ D.tailLength * 3 + D.prependGap := by
              rw [Nat.mul_comm 3 (3 ^ D.tailLength)]
      _ = 2 * 2 ^ D.tailExponent := hpre0
  nlinarith


/-- prepend gap の定義を加法形にした exact equation。 -/
theorem three_mul_threePow_add_prependGap_eq_two_mul_twoPow
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    3 * 3 ^ D.tailLength + D.prependGap =
      2 * 2 ^ D.tailExponent := by
  have hpre :
      3 ^ Word.oddSteps (1 :: D.tailWord) + D.prependGap =
        2 ^ Word.twoSteps (1 :: D.tailWord) := by
    unfold prependGap
    exact Nat.add_sub_of_le (Nat.le_of_lt (by
      simpa [Word.Contracting] using D.prepend_contracting))
  have hpre0 :
      3 ^ D.tailLength * 3 + D.prependGap =
        2 ^ (1 + D.tailExponent) := by
    simpa [
      tailLength,
      tailExponent,
      Word.oddSteps_cons,
      Word.twoSteps_cons,
      pow_succ
    ] using hpre
  calc
    3 * 3 ^ D.tailLength + D.prependGap
        = 3 ^ D.tailLength * 3 + D.prependGap := by
            rw [Nat.mul_comm 3 (3 ^ D.tailLength)]
    _ = 2 ^ (1 + D.tailExponent) := hpre0
    _ = 2 * 2 ^ D.tailExponent := by
      rw [pow_add]
      norm_num

private theorem coprime_two_of_odd
    {x : ℕ} (hx : Odd x) :
    Nat.Coprime x 2 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd x 2
  have hgx : g ∣ x := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ 2 := Nat.gcd_dvd_right _ _
  have hgle : g ≤ 2 := Nat.le_of_dvd (by omega) hg2
  have hgpos : 0 < g :=
    Nat.gcd_pos_of_pos_right x (by omega)
  have hg_ne_two : g ≠ 2 := by
    intro h
    have h2x : 2 ∣ x := by
      rw [← h]
      exact hgx
    rcases hx with ⟨k, hk⟩
    rcases h2x with ⟨q, hq⟩
    omega
  omega

private theorem coprime_three_of_not_dvd
    {x : ℕ} (hx : ¬ 3 ∣ x) :
    Nat.Coprime x 3 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd x 3
  have hgx : g ∣ x := Nat.gcd_dvd_left _ _
  have hg3 : g ∣ 3 := Nat.gcd_dvd_right _ _
  have hgle : g ≤ 3 := Nat.le_of_dvd (by omega) hg3
  have hgpos : 0 < g :=
    Nat.gcd_pos_of_pos_right x (by omega)
  have hg_ne_three : g ≠ 3 := by
    intro h
    apply hx
    rw [← h]
    exact hgx
  have hg_ne_two : g ≠ 2 := by
    intro h
    have h2three : 2 ∣ 3 := by
      rw [← h]
      exact hg3
    norm_num at h2three
  omega

/-- prepend gap は奇数。 -/
theorem prependGap_odd
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Odd D.prependGap := by
  have hGC := D.prependGap_add_threePow_eq_two_mul_tailGap
  have hCodd : Odd (3 ^ D.tailLength) :=
    (show Odd (3 : ℕ) by decide).pow
  obtain ⟨k, heven | hodd⟩ := D.prependGap.even_or_odd'
  · rcases hCodd with ⟨c, hc⟩
    omega
  · exact ⟨k, hodd⟩

/-- prepend gap は2と互いに素。 -/
theorem prependGap_coprime_two
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Nat.Coprime D.prependGap 2 :=
  coprime_two_of_odd D.prependGap_odd

/-- prepend gap は3で割れない。 -/
theorem three_not_dvd_prependGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ¬ 3 ∣ D.prependGap := by
  intro h3G
  have hEq := D.three_mul_threePow_add_prependGap_eq_two_mul_twoPow
  have h3left :
      3 ∣ 3 * 3 ^ D.tailLength + D.prependGap :=
    Nat.dvd_add
      (Nat.dvd_mul_right 3 (3 ^ D.tailLength))
      h3G
  rw [hEq] at h3left
  have hcop32 : Nat.Coprime 3 2 := by decide
  have h3A : 3 ∣ 2 ^ D.tailExponent := by
    exact hcop32.dvd_mul_left.mp h3left
  have hcopA :
      Nat.Coprime 3 (2 ^ D.tailExponent) := by
    simpa using
      (show Nat.Coprime (3 ^ 1) (2 ^ D.tailExponent) from
        (by decide : Nat.Coprime 3 2).pow 1 D.tailExponent)
  have hthreeEqOne :=
    Nat.eq_one_of_dvd_coprimes
      hcopA (Nat.dvd_refl 3) h3A
  norm_num at hthreeEqOne

/-- prepend gap は3と互いに素。 -/
theorem prependGap_coprime_three
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Nat.Coprime D.prependGap 3 :=
  coprime_three_of_not_dvd D.three_not_dvd_prependGap

/-- prepend gap は6と互いに素。 -/
theorem prependGap_coprime_six
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Nat.Coprime D.prependGap 6 := by
  have h :=
    Nat.coprime_mul_iff_right.mpr
      ⟨D.prependGap_coprime_two, D.prependGap_coprime_three⟩
  simpa using h

/--
`g = 2^J-3^m` と `G = 2^(J+1)-3^(m+1)` は互いに素。
-/
theorem tailGap_coprime_prependGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Nat.Coprime D.tailGap D.prependGap := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let k := Nat.gcd D.tailGap D.prependGap
  have hkG : k ∣ D.tailGap :=
    Nat.gcd_dvd_left _ _
  have hkP : k ∣ D.prependGap :=
    Nat.gcd_dvd_right _ _
  have hAG :
      2 ^ D.tailExponent + D.prependGap =
        3 * D.tailGap := by
    simpa [Nat.add_comm] using
      D.three_mul_tailGap_eq_twoPow_add_prependGap.symm
  have hGC :
      D.prependGap + 3 ^ D.tailLength =
        2 * D.tailGap :=
    D.prependGap_add_threePow_eq_two_mul_tailGap
  have hkAG :
      k ∣ 2 ^ D.tailExponent + D.prependGap := by
    rw [hAG]
    exact Nat.dvd_mul_left_of_dvd hkG 3
  have hkA : k ∣ 2 ^ D.tailExponent :=
    (Nat.dvd_add_iff_left hkP).mpr hkAG
  have hkGC :
      k ∣ D.prependGap + 3 ^ D.tailLength := by
    rw [hGC]
    exact Nat.dvd_mul_left_of_dvd hkG 2
  have hkC : k ∣ 3 ^ D.tailLength :=
    (Nat.dvd_add_iff_right hkP).mpr hkGC
  have hAC :
      Nat.Coprime (2 ^ D.tailExponent) (3 ^ D.tailLength) :=
    (by decide : Nat.Coprime 2 3).pow
      D.tailExponent D.tailLength
  exact Nat.eq_one_of_dvd_coprimes hAC hkA hkC

/--
`gcd(g,B)=gcd(g,d)`。
first exact affine identity と `gcd(g,G)=1` から得る。
-/
theorem gcd_tailGap_tailAffine_eq_gcd_tailGap_d
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Nat.gcd D.tailGap D.tailAffine =
      Nat.gcd D.tailGap D.arithmeticData.d := by
  have hE :=
    D.tailAffine_add_tailGap_eq_six_n_gap_add_two_d_prependGap
  have hJpos : 0 < D.tailExponent := by
    simpa [tailExponent] using
      Word.twoSteps_pos_of_valid_nonempty D.tail_valid D.tail_nonempty
  have htailC :
      3 ^ D.tailLength + D.tailGap =
        2 ^ D.tailExponent := by
    unfold tailGap
    exact Nat.add_sub_of_le (Nat.le_of_lt (by
      simpa [tailExponent, tailLength, Word.Contracting] using
        D.tail_contracting))
  have hAC :
      Nat.Coprime (2 ^ D.tailExponent) (3 ^ D.tailLength) :=
    (by decide : Nat.Coprime 2 3).pow
      D.tailExponent D.tailLength
  have hgC : Nat.Coprime D.tailGap (3 ^ D.tailLength) := by
    unfold tailGap
    exact (Nat.coprime_sub_self_left
      (Nat.le_of_lt (by
        simpa [tailExponent, tailLength, Word.Contracting] using
          D.tail_contracting))).2 hAC
  have hgA : Nat.Coprime D.tailGap (2 ^ D.tailExponent) := by
    rw [← htailC]
    simpa using hgC
  have htwoDvd : 2 ∣ 2 ^ D.tailExponent := by
    obtain ⟨r, hr⟩ : ∃ r : ℕ, D.tailExponent = r + 1 :=
      ⟨D.tailExponent - 1, by omega⟩
    refine ⟨2 ^ r, ?_⟩
    rw [hr, pow_succ]
    ring
  have hg2 : Nat.Coprime D.tailGap 2 :=
    Nat.Coprime.of_dvd_right htwoDvd hgA
  have hgP := D.tailGap_coprime_prependGap
  have hg2P :
      Nat.Coprime D.tailGap (2 * D.prependGap) :=
    Nat.coprime_mul_iff_right.mpr ⟨hg2, hgP⟩
  calc
    Nat.gcd D.tailGap D.tailAffine
        = Nat.gcd D.tailGap (D.tailAffine + D.tailGap) := by
            symm
            exact Nat.gcd_add_self_right _ _
    _ =
        Nat.gcd D.tailGap
          (6 * D.arithmeticData.n * D.tailGap +
            2 * D.arithmeticData.d * D.prependGap) := by
              rw [hE]
    _ =
        Nat.gcd D.tailGap
          (2 * D.arithmeticData.d * D.prependGap) := by
              simpa [Nat.mul_assoc] using
                Nat.gcd_mul_right_add_right
                  D.tailGap
                  (2 * D.arithmeticData.d * D.prependGap)
                  (6 * D.arithmeticData.n)
    _ =
        Nat.gcd D.tailGap
          (D.arithmeticData.d * (2 * D.prependGap)) := by
              congr 1
              ring
    _ = Nat.gcd D.tailGap D.arithmeticData.d := by
      exact hg2P.symm.gcd_mul_right_cancel_right D.arithmeticData.d


/--
`gcd(G,B+g)=gcd(G,n)`。
prepend gap は `6*g` と互いに素なので second exact affine identity の共通因子を消せる。
-/
theorem gcd_prependGap_tailAffine_add_tailGap_eq_gcd_prependGap_n
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Nat.gcd D.prependGap (D.tailAffine + D.tailGap) =
      Nat.gcd D.prependGap D.arithmeticData.n := by
  have hE :=
    D.tailAffine_add_tailGap_eq_six_n_gap_add_two_d_prependGap
  have hGg : Nat.Coprime D.prependGap D.tailGap :=
    D.tailGap_coprime_prependGap.symm
  have hG6g :
      Nat.Coprime D.prependGap (6 * D.tailGap) :=
    Nat.coprime_mul_iff_right.mpr
      ⟨D.prependGap_coprime_six, hGg⟩
  calc
    Nat.gcd D.prependGap (D.tailAffine + D.tailGap)
        =
      Nat.gcd D.prependGap
        (6 * D.arithmeticData.n * D.tailGap +
          2 * D.arithmeticData.d * D.prependGap) := by
            rw [hE]
    _ =
      Nat.gcd D.prependGap
        (6 * D.arithmeticData.n * D.tailGap) := by
          have h :=
            Nat.gcd_add_mul_left_right
              D.prependGap
              (6 * D.arithmeticData.n * D.tailGap)
              (2 * D.arithmeticData.d)
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    _ =
      Nat.gcd D.prependGap
        (D.arithmeticData.n * (6 * D.tailGap)) := by
          congr 1
          ring
    _ = Nat.gcd D.prependGap D.arithmeticData.n := by
      exact hG6g.symm.gcd_mul_right_cancel_right D.arithmeticData.n

/--
natural tail の残り1文字 residual は affine constant 1。
-/
theorem tail_drop_affine_eq_one_of_remaining_one
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hlen : (D.tailWord.drop k).length = 1) :
    Word.affineConst (D.tailWord.drop k) = 1 := by
  exact
    (D.tail_valid.drop k).affine_signature_of_length_one hlen

/--
natural tail の残り2文字 residual では `B-3` が正の純2冪。
-/
theorem tail_drop_exists_affine_sub_three_eq_twoPow_of_remaining_two
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hlen : (D.tailWord.drop k).length = 2) :
    ∃ e : ℕ,
      0 < e ∧
      Word.affineConst (D.tailWord.drop k) - 3 = 2 ^ e := by
  exact
    (D.tail_valid.drop k).exists_affine_sub_three_eq_twoPow_of_length_two hlen

/-- natural tail の残り3文字 residual の exact nested affine signature。 -/
theorem tail_drop_exists_affine_signature_of_remaining_three
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hlen : (D.tailWord.drop k).length = 3) :
    ∃ e f : ℕ,
      0 < e ∧
      0 < f ∧
      Word.affineConst (D.tailWord.drop k) =
        9 + 2 ^ e * (3 + 2 ^ f) := by
  exact
    (D.tail_valid.drop k).exists_affine_signature_of_length_three hlen

end FirstCrossingData.NaturalZeroReplaySignChangeData
end PositiveReturn
end AdjacentReturn
end Collatz
