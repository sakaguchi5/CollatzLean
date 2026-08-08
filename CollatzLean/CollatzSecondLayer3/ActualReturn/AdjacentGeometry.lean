import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentExpandingReturn
import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentContractingReturn

/-!
# adjacent return の両側 geometry

標準 future-minimum の隣接区間では、任意の真の内部位置から次の
future-minimum までが contracting である。この suffix 情報を正本 state 上へ
引き上げる。

さらに whole word が expanding の場合、proper prefix が一つでも contracting なら
その prefix と後続 contracting suffix の積も contracting となり whole expanding に
矛盾する。従って Adjacent Expanding Return は全 proper prefix が expanding である。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord

/-- contracting 語どうしの連結も contracting。 -/
theorem contracting_append_adjacent
    {u v : ExpWord}
    (hu : Contracting u)
    (hv : Contracting v) :
    Contracting (u ++ v) := by
  unfold Contracting at hu hv ⊢
  rw [oddSteps_append, twoSteps_append, pow_add, pow_add]
  have hv3 : 0 < 3 ^ oddSteps v := Nat.pow_pos (by omega)
  have hu2 : 0 < 2 ^ twoSteps u := Nat.pow_pos (by omega)
  have h₁ :
      3 ^ oddSteps u * 3 ^ oddSteps v <
        2 ^ twoSteps u * 3 ^ oddSteps v :=
    (Nat.mul_lt_mul_right hv3).2 hu
  have h₂ :
      2 ^ twoSteps u * 3 ^ oddSteps v <
        2 ^ twoSteps u * 2 ^ twoSteps v :=
    (Nat.mul_lt_mul_left hu2).2 hv
  exact lt_trans h₁ h₂

end ExpWord

namespace AdjacentFutureMinimumReturnData

/-- 隣接 word の先頭 `k` 個は actual prefix segment。 -/
theorem word_take_eq_segmentWord
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O)
    {k : ℕ}
    (hk : k ≤ R.length) :
    R.word.take k = O.segmentWord R.startIndex k := by
  change
    k ≤ consecutiveFutureMinimumIndexGap O R.index
    at hk
  change
    (O.segmentWord
      (O.futureMinIndex R.index)
      (consecutiveFutureMinimumIndexGap O R.index)).take k =
      O.segmentWord (O.futureMinIndex R.index) k
  exact O.segmentWord_take_of_le hk

/-- 隣接 word を位置 `k` で actual prefix/suffix に分解する。 -/
theorem word_eq_prefix_append_suffix
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O)
    {k : ℕ}
    (hk : k ≤ R.length) :
    R.word =
      O.segmentWord R.startIndex k ++
      O.segmentWord (R.startIndex + k) (R.length - k) := by
  have hlen :
      R.length = k + (R.length - k) := by
    omega
  change
    O.segmentWord R.startIndex R.length =
      O.segmentWord R.startIndex k ++
      O.segmentWord (R.startIndex + k) (R.length - k)
  calc
    O.segmentWord R.startIndex R.length =
        O.segmentWord R.startIndex (k + (R.length - k)) := by
      rw [hlen]
      simp
    _ =
        O.segmentWord R.startIndex k ++
          O.segmentWord (R.startIndex + k) (R.length - k) :=
      O.segmentWord_add R.startIndex k (R.length - k)

/--
任意の真の proper suffix は次 future-minimum へ真に下がるため contracting。
-/
theorem properSuffix_contracting
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < R.length) :
    Contracting
      (O.segmentWord (R.startIndex + k) (R.length - k)) := by
  have hleft :
      O.futureMinIndex R.index < R.startIndex + k := by
    unfold startIndex
    omega
  have hright' :
      R.startIndex + k < R.nextIndex := by
    rw [R.nextIndex_eq_startIndex_add_length]
    omega
  have hright :
      R.startIndex + k <
        O.futureMinIndex (R.index + 1) := by
    simpa [nextIndex] using hright'
  have hs :=
    suffix_to_nextFutureMinimum_contracting
      O R.unbounded R.index (R.startIndex + k) hleft hright
  have hlen :
      O.futureMinIndex (R.index + 1) - (R.startIndex + k) =
        R.length - k := by
    change
      O.futureMinIndex (R.index + 1) -
          (O.futureMinIndex R.index + k) =
        (O.futureMinIndex (R.index + 1) -
          O.futureMinIndex R.index) - k
    omega
  rw [hlen] at hs
  exact hs

/--
正長隣接 word を先頭 exponent と残りの actual tail に分解する。
-/
theorem word_eq_startExponent_cons_tail
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    R.word =
      O.exponent R.startIndex ::
        O.segmentWord (R.startIndex + 1) (R.length - 1) := by
  have hpos := R.length_pos
  obtain ⟨q, hq⟩ : ∃ q : ℕ, R.length = q + 1 :=
    ⟨R.length - 1, by omega⟩
  change
    O.segmentWord R.startIndex R.length =
      O.exponent R.startIndex ::
        O.segmentWord (R.startIndex + 1) (R.length - 1)
  rw [hq]
  simp only [O.segmentWord_succ]
  rw [show q + 1 - 1 = q by omega]

end AdjacentFutureMinimumReturnData

namespace AdjacentExpandingReturnData

/--
Adjacent Expanding Return では全 proper prefix が expanding。

proper prefix が contracting なら、その終点から next future-minimum までの
proper suffix も contracting なので whole word も contracting となり矛盾する。
-/
theorem properPrefixesExpanding
    {O : OddOrbit}
    (D : AdjacentExpandingReturnData O) :
    ProperPrefixesExpanding D.state.word := by
  intro k hkPos hkLtWord
  have hkLt : k < D.state.length := by
    simpa using hkLtWord
  have hkLe : k ≤ D.state.length := Nat.le_of_lt hkLt
  have htake := D.state.word_take_eq_segmentWord hkLe
  have hvalid : Valid (O.segmentWord D.state.startIndex k) :=
    (O.runs_segment D.state.startIndex k).valid
  have hne : O.segmentWord D.state.startIndex k ≠ [] :=
    segmentWord_nonempty_of_length_pos hkPos
  rcases expanding_or_contracting_of_valid_nonempty hvalid hne with hExp | hCon
  · rw [htake]
    exact hExp
  · have hSuffix := D.state.properSuffix_contracting hkPos hkLt
    have hWholeCon : Contracting D.state.word := by
      rw [D.state.word_eq_prefix_append_suffix hkLe]
      exact ExpWord.contracting_append_adjacent hCon hSuffix
    have hWholeExp : Expanding D.state.word := by
      simpa [
        AdjacentExpandingReturnAt,
        AdjacentFutureMinimumReturnData.word
      ] using D.expanding
    unfold Expanding at hWholeExp
    unfold Contracting at hWholeCon
    omega

end AdjacentExpandingReturnData

end CollatzSecondLayer3
