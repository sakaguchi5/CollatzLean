import CollatzLean.Collatz2.Canonical.EndpointFloorCyclicGeometry
import CollatzLean.Collatz2.Geometry.RankPath
import Mathlib.Tactic.LinearCombination

/-!
# Collatz2 Canonical: endpoint-floor cyclic separation の rank 形式

Stage 5。

current A の proper cut `k` に対し、prefix rank

  d_k = H*k - p*h_k

は complementary suffix の chord determinant

  p*H_suffix - H*p_suffix

と exact に一致する。

また既存の全 cut cyclic translation identity を
prefix odd length `k` を明示した rank-ready 形式へ持ち上げる。

FutureMinimum endpoint は使わない。
-/

namespace Collatz2
namespace Word

/--
cut suffix が whole rational chord に対して持つ signed rank。

  p*H_suffix - H*p_suffix.
-/
def suffixChordRankInt (w : Word) (k : ℕ) : ℤ :=
  (oddSteps w : ℤ) * (twoSteps (w.drop k) : ℤ) -
    (twoSteps w : ℤ) * (oddSteps (w.drop k) : ℤ)

/--
prefix chord rank と complementary suffix chord rank は exact に同じ。
-/
theorem chordRankInt_eq_suffixChordRankInt
    {w : Word}
    {k : ℕ}
    (hk : k ≤ oddSteps w) :
    chordRankInt w k = suffixChordRankInt w k := by
  have hkLen : k ≤ w.length := by
    simpa [oddSteps] using hk
  have hOddRaw := congrArg oddSteps (List.take_append_drop k w)
  have hTwoRaw := congrArg twoSteps (List.take_append_drop k w)
  have hTakeOdd : oddSteps (w.take k) = k := by
    unfold oddSteps
    exact List.length_take_of_le hkLen
  have hOdd :
      k + oddSteps (w.drop k) = oddSteps w := by
    rw [oddSteps_append] at hOddRaw
    rw [hTakeOdd] at hOddRaw
    exact hOddRaw
  have hTwo :
      prefixTwoDepth w k + twoSteps (w.drop k) = twoSteps w := by
    rw [twoSteps_append] at hTwoRaw
    simpa [prefixTwoDepth] using hTwoRaw
  have hOddZ :
      (k : ℤ) + (oddSteps (w.drop k) : ℤ) = (oddSteps w : ℤ) := by
    exact_mod_cast hOdd
  have hTwoZ :
      (prefixTwoDepth w k : ℤ) + (twoSteps (w.drop k) : ℤ) =
        (twoSteps w : ℤ) := by
    exact_mod_cast hTwo
  unfold chordRankInt suffixChordRankInt
  linear_combination
    (twoSteps w : ℤ) * hOddZ - (oddSteps w : ℤ) * hTwoZ

/--
whole が contracting で cut prefix が expanding なら、その cut rank は正。
`FirstCrossing` 全体を仮定しない局所版。
-/
theorem prefixSlope_cross_of_expanding_contracting
    {w : Word}
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < w.length)
    (hPrefix : Expanding (w.take k))
    (hWhole : Contracting w) :
    oddSteps w * prefixTwoDepth w k < twoSteps w * k := by
  have hkLe : k ≤ w.length := Nat.le_of_lt hkLt
  have hTakeLen : (w.take k).length = k :=
    List.length_take_of_le hkLe
  have hPrefixPowRaw :=
    (expanding_iff_twoPow_lt_threePow).1 hPrefix
  have hPrefixPow :
      2 ^ prefixTwoDepth w k < 3 ^ k := by
    simpa [prefixTwoDepth, oddSteps, hTakeLen] using hPrefixPowRaw
  have hWholePow :=
    (contracting_iff_threePow_lt_twoPow).1 hWhole
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    omega
  have hPrefixPowRaisedRaw :=
    Nat.pow_lt_pow_left hPrefixPow (Nat.ne_of_gt hpPos)
  have hPrefixPowRaised :
      2 ^ (prefixTwoDepth w k * oddSteps w) <
        3 ^ (k * oddSteps w) := by
    calc
      2 ^ (prefixTwoDepth w k * oddSteps w)
          = (2 ^ prefixTwoDepth w k) ^ oddSteps w := by
              rw [pow_mul]
      _ < (3 ^ k) ^ oddSteps w := hPrefixPowRaisedRaw
      _ = 3 ^ (k * oddSteps w) := by
              rw [pow_mul]
  have hWholePowRaisedRaw :=
    Nat.pow_lt_pow_left hWholePow (Nat.ne_of_gt hkPos)
  have hWholePowRaised :
      3 ^ (oddSteps w * k) < 2 ^ (twoSteps w * k) := by
    calc
      3 ^ (oddSteps w * k)
          = (3 ^ oddSteps w) ^ k := by
              rw [pow_mul]
      _ < (2 ^ twoSteps w) ^ k := hWholePowRaisedRaw
      _ = 2 ^ (twoSteps w * k) := by
              rw [pow_mul]
  by_contra hnot
  have hle : twoSteps w * k ≤ oddSteps w * prefixTwoDepth w k := by
    omega
  have htwo :
      2 ^ (twoSteps w * k) ≤
        2 ^ (oddSteps w * prefixTwoDepth w k) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle
  have hleft :
      2 ^ (oddSteps w * prefixTwoDepth w k) <
        3 ^ (oddSteps w * k) := by
    simpa [Nat.mul_comm] using hPrefixPowRaised
  have hcontra :
      2 ^ (twoSteps w * k) < 2 ^ (twoSteps w * k) :=
    lt_of_le_of_lt htwo (lt_trans hleft hWholePowRaised)
  exact (Nat.lt_irrefl _ hcontra)

/-- expanding prefix / contracting whole の signed chord rank 版。 -/
theorem chordRankInt_pos_of_expanding_contracting
    {w : Word}
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < w.length)
    (hPrefix : Expanding (w.take k))
    (hWhole : Contracting w) :
    0 < chordRankInt w k := by
  have hSlope :=
    prefixSlope_cross_of_expanding_contracting
      hkPos hkLt hPrefix hWhole
  have hSlopeZ :
      (oddSteps w : ℤ) * (prefixTwoDepth w k : ℤ) <
        (twoSteps w : ℤ) * (k : ℤ) := by
    exact_mod_cast hSlope
  unfold chordRankInt
  linarith

end Word

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- current A の cut rank を complementary suffix rank として読む。 -/
theorem cutRank_eq_suffixChordRankInt
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hk : k ≤ D.length) :
    Word.chordRankInt D.word k =
      (Word.oddSteps D.word : ℤ) *
          (Word.twoSteps (D.cutSuffix k) : ℤ) -
        (Word.twoSteps D.word : ℤ) *
          (Word.oddSteps (D.cutSuffix k) : ℤ) := by
  have hkWord : k ≤ Word.oddSteps D.word := by
    simpa [Word.oddSteps, D.word_length] using hk
  have h :=
    Word.chordRankInt_eq_suffixChordRankInt
      (w := D.word) hkWord
  simpa [Word.suffixChordRankInt, cutSuffix] using h

/-- current A proper cut の signed rank は strict positive。 -/
theorem cutChordRankInt_pos
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.length) :
    0 < Word.chordRankInt D.word k := by
  have hF : Word.FirstCrossing D.word := by
    simpa [word] using D.firstCrossing
  have hkLtWord : k < Word.oddSteps D.word := by
    simpa [Word.oddSteps, D.word_length] using hkLt
  have hEq := hF.chordRankInt_eq_natCast hkPos hkLtWord
  rw [hEq]
  exact_mod_cast D.cutChordRank_pos hkPos hkLt

/--
全 cut cyclic translation identity の rank-ready 版。

prefix length を `k` に固定し、同時に同じ cut rank が suffix chord determinant に
一致することを保持する。
-/
theorem cutRotation_translate_sub_exact_rank
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D)
    {k : ℕ}
    (hkLt : k < D.length) :
    (((Word.affineConst (D.cutRotation k) : ℕ) : ℤ) -
        ((Word.affineConst D.word : ℕ) : ℤ) =
      (2 * L.n : ℤ) * ((3 : ℤ) ^ k) *
          (((2 : ℤ) ^ Word.twoSteps (D.cutSuffix k)) -
            ((3 : ℤ) ^ Word.oddSteps (D.cutSuffix k))) +
        (((2 : ℤ) ^ Word.twoSteps D.word) -
            ((3 : ℤ) ^ Word.oddSteps D.word)) *
          ((O.value (D.startIndex + k) : ℤ) -
            (O.value D.endIndex : ℤ))) ∧
    Word.chordRankInt D.word k =
      (Word.oddSteps D.word : ℤ) *
          (Word.twoSteps (D.cutSuffix k) : ℤ) -
        (Word.twoSteps D.word : ℤ) *
          (Word.oddSteps (D.cutSuffix k) : ℤ) := by
  have hkLe : k ≤ D.length := Nat.le_of_lt hkLt
  constructor
  · have h := cutRotation_translate_sub_exact L hkLt
    rw [D.cutPrefix_oddSteps_eq hkLe] at h
    exact h
  · exact D.cutRank_eq_suffixChordRankInt hkLe

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
