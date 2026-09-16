import CollatzLean.Collatz3.CSTConditional.IntegerReduction.AdmissibleBlock
import Mathlib.Tactic.NormNum

/-!
# Collatz3 CSTConditional IntegerReduction: 許容ブロックの有限分類

`IsAdmissibleBlock` の B1/B2 から、前方 prefix 条件・先頭指数 `1`・
許される block length の最終 `+2` jump をすべて導く。

primitive definition は増やさず、長さだけを扱う薄い predicate
`IsAdmissibleLength` だけを後段の counting 用に置く。
-/

namespace Collatz3
namespace IntegerReduction

open Critical

namespace IsAdmissibleBlock

/--
B1+B2 から任意の proper positive prefix は Beatty roof 以下になる。

後方 suffix 条件だけを primitive にしても、前方臨界条件は自動的に復元される。
-/
theorem prefixTwoDepth_le_beattyIndex
    {w : Word}
    (h : IsAdmissibleBlock w)
    {t : ℕ}
    (htPos : 0 < t)
    (htLt : t < w.length) :
    Word.prefixTwoDepth w t ≤ Critical.beattyIndex t := by
  let q : ℕ := w.length - t
  have hqPos : 0 < q := by
    dsimp [q]
    omega
  have hqLt : q < w.length := by
    dsimp [q]
    omega
  have hSuffix := h.suffixTwoDepth_lower hqPos hqLt
  have hDrop : w.length - q = t := by
    dsimp [q]
    omega
  rw [suffixTwoDepth, hDrop] at hSuffix
  have hSplit := twoSteps_eq_prefixTwoDepth_add_drop w t
  have hTotal := h.totalTwoDepth_eq_beattyIndex
  have hAdd := Critical.beattyIndex_add_upper t q
  have hTQ : t + q = w.length := by
    dsimp [q]
    omega
  rw [hTQ] at hAdd
  omega

/-- proper positive prefix は power-form でも strict に臨界線の下。 -/
theorem twoPow_prefixTwoDepth_lt_threePow
    {w : Word}
    (h : IsAdmissibleBlock w)
    {t : ℕ}
    (htPos : 0 < t)
    (htLt : t < w.length) :
    2 ^ Word.prefixTwoDepth w t < 3 ^ t := by
  have hDepth := h.prefixTwoDepth_le_beattyIndex htPos htLt
  have hPow :
      2 ^ Word.prefixTwoDepth w t ≤
        2 ^ Critical.beattyIndex t :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
  exact lt_of_le_of_lt hPow (Critical.beattyIndex_lower_strict htPos)

/-- 許容ブロックの先頭指数は必ず `1`。 -/
theorem head_eq_one
    {e : ℕ}
    {tail : Word}
    (h : IsAdmissibleBlock (e :: tail)) :
    e = 1 := by
  have hePos : 0 < e := h.valid e (by simp)
  by_cases hTail : tail = []
  · subst tail
    have hTotal := h.totalTwoDepth_eq_beattyIndex
    simp [Word.twoSteps, beattyIndex_one] at hTotal
    omega
  · have hLen : 1 < (e :: tail).length := by
      cases tail with
      | nil => contradiction
      | cons a t => simp
    have hPrefix :=
      h.prefixTwoDepth_le_beattyIndex
        (t := 1) (by omega) hLen
    simp [Word.prefixTwoDepth, Word.twoSteps, beattyIndex_one] at hPrefix
    omega

/--
非自明な許容ブロックでは、その長さ `r` の最後の Beatty jump は exactly `+2`。
-/
theorem terminalBeattyJump_eq_two
    {w : Word}
    (h : IsAdmissibleBlock w)
    (hLen : 1 < w.length) :
    Critical.beattyIndex w.length =
      Critical.beattyIndex (w.length - 1) + 2 := by
  cases w with
  | nil => simp at hLen
  | cons e tail =>
      have he : e = 1 := h.head_eq_one
      have hqPos : 0 < (e :: tail).length - 1 := by omega
      have hqLt : (e :: tail).length - 1 < (e :: tail).length := by omega
      have hSuffix := h.suffixTwoDepth_lower hqPos hqLt
      have hDrop :
          (e :: tail).length - ((e :: tail).length - 1) = 1 := by
        omega
      rw [suffixTwoDepth, hDrop] at hSuffix
      have hSplit := twoSteps_eq_prefixTwoDepth_add_drop (e :: tail) 1
      have hTotal := h.totalTwoDepth_eq_beattyIndex
      have hPrefixOne :
          Word.prefixTwoDepth (e :: tail) 1 = 1 := by
        simp [Word.prefixTwoDepth, Word.twoSteps, he]
      have hStep :=
        beattyIndex_step_eq_add_one_or_two ((e :: tail).length - 1)
      have hSucc :
          ((e :: tail).length - 1) + 1 = (e :: tail).length := by
        omega
      rw [hSucc] at hStep
      omega

end IsAdmissibleBlock

/--
許容ブロック長の純整数 characterization。

`r=1`、または `r>1` で最後の Beatty jump が `+2`。
-/
def IsAdmissibleLength
    (r : ℕ) : Prop :=
  0 < r ∧
    (r = 1 ∨
      Critical.beattyIndex r =
        Critical.beattyIndex (r - 1) + 2)

/-- 許容ブロックの長さは `IsAdmissibleLength`。 -/
theorem IsAdmissibleBlock.isAdmissibleLength
    {w : Word}
    (h : IsAdmissibleBlock w) :
    IsAdmissibleLength w.length := by
  refine ⟨h.length_pos, ?_⟩
  by_cases hOne : w.length = 1
  · exact Or.inl hOne
  · right
    apply h.terminalBeattyJump_eq_two
    have hPos : 0 < w.length := h.length_pos
    omega

private def terminalHeavyWord
    (r : ℕ) : Word :=
  List.replicate (r - 1) 1 ++
    [Critical.beattyIndex r - (r - 1)]

private theorem terminalHeavyWord_length
    {r : ℕ}
    (hr : 0 < r) :
    (terminalHeavyWord r).length = r := by
  simp [terminalHeavyWord]
  omega

private theorem terminalHeavyWord_valid
    {r : ℕ}
    (hr : 0 < r) :
    Word.Valid (terminalHeavyWord r) := by
  intro e he
  unfold terminalHeavyWord at he
  rw [List.mem_append] at he
  rcases he with he | he
  · simp at he
    omega
  · simp at he
    subst e
    have hb := nat_le_beattyIndex r
    omega

private theorem terminalHeavyWord_total
    {r : ℕ}
    (hr : 0 < r) :
    Word.twoSteps (terminalHeavyWord r) =
      Critical.beattyIndex r := by
  have hb := nat_le_beattyIndex r
  simp [terminalHeavyWord, Word.twoSteps]
  omega

private theorem terminalHeavyWord_suffix_lower
    {r q : ℕ}
    (hr : 1 < r)
    (hJump :
      Critical.beattyIndex r =
        Critical.beattyIndex (r - 1) + 2)
    (hqPos : 0 < q)
    (hqLt : q < r) :
    Critical.beattyIndex q + 1 ≤
      suffixTwoDepth (terminalHeavyWord r) q := by
  let d : ℕ := r - 1 - q
  have hQD : q + d = r - 1 := by
    dsimp [d]
    omega
  have hDistance := beattyIndex_add_distance_lower q d
  rw [hQD] at hDistance
  have hMain :
      Critical.beattyIndex q + (r - q) + 1 ≤
        Critical.beattyIndex r := by
    dsimp [d] at hDistance
    rw [hJump]
    omega
  have hLen : (terminalHeavyWord r).length = r :=
    terminalHeavyWord_length (by omega)
  have hDropLe :
      r - q ≤ (List.replicate (r - 1) 1).length := by
    simp
    omega
  unfold suffixTwoDepth
  rw [hLen]
  unfold terminalHeavyWord
  rw [List.drop_append_of_le_length hDropLe]
  simp [Word.twoSteps]
  omega

/--
`IsAdmissibleLength r` なら実際に長さ `r` の許容ブロックが存在する。

証人は先頭側をすべて `1` に寄せた terminal-heavy word。
-/
theorem exists_admissibleBlock_of_isAdmissibleLength
    {r : ℕ}
    (h : IsAdmissibleLength r) :
    ∃ w : Word,
      IsAdmissibleBlock w ∧
        w.length = r := by
  rcases h with ⟨hrPos, hrOne | hJump⟩
  · subst r
    refine ⟨[1], ?_, by simp⟩
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro e he
      simp at he
      omega
    · simp [Word.twoSteps, beattyIndex_one]
    · intro q hqPos hqLt
      simp at hqLt
      omega
  · have hrGt : 1 < r := by
      by_contra hNot
      have hrEq : r = 1 := by omega
      subst r
      simp [beattyIndex_one] at hJump
    let w := terminalHeavyWord r
    have hLenW : w.length = r := by
      simpa [w] using terminalHeavyWord_length hrPos
    refine ⟨w, ?_, hLenW⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hLenW]
      exact hrPos
    · exact terminalHeavyWord_valid hrPos
    · rw [terminalHeavyWord_length hrPos]
      exact terminalHeavyWord_total hrPos
    · intro q hqPos hqLt
      have hLen : w.length = r := by
        simpa [w] using terminalHeavyWord_length hrPos
      rw [hLen] at hqLt
      simpa [w] using
        terminalHeavyWord_suffix_lower hrGt hJump hqPos hqLt

/--
長さ `r` の許容ブロックが存在することと `IsAdmissibleLength r` は同値。
-/
theorem exists_admissibleBlock_iff_isAdmissibleLength
    (r : ℕ) :
    (∃ w : Word,
      IsAdmissibleBlock w ∧ w.length = r) ↔
      IsAdmissibleLength r := by
  constructor
  · rintro ⟨w, hw, hLen⟩
    subst r
    exact hw.isAdmissibleLength
  · exact exists_admissibleBlock_of_isAdmissibleLength

end IntegerReduction
end Collatz3
