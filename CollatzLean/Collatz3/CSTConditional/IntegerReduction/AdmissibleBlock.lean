import CollatzLean.Collatz3.CSTConditional.IntegerReduction.PowerIndex
import CollatzLean.Collatz3.Core.Word

/-!
# Collatz3 CSTConditional IntegerReduction: 許容ブロックの薄い定義

Work 側で得た純整数 block 条件 B1/B2 だけを primitive にする。
actual orbit、future minimum、A/C symbol はこのファイルには入れない。

* word は非空かつ正指数語
* total two-depth は `beattyIndex(length)` に exact
* 任意の proper positive suffix は、その幅の Beatty roof を 1 以上上回る

それ以外は derived theorem として後続ファイルで導く。
-/

namespace Collatz3
namespace IntegerReduction

open Critical

/--
word の末尾 `q` 文字が持つ 2-depth。
`q > length` の場合は自然数減算により word 全体を取る。
-/
def suffixTwoDepth
    (w : Word)
    (q : ℕ) : ℕ :=
  Word.twoSteps (w.drop (w.length - q))

/--
純整数側の許容ブロック。

B1: total depth = Beatty roof。
B2: 任意の proper positive suffix は `beattyIndex q + 1` 以上。
-/
def IsAdmissibleBlock
    (w : Word) : Prop :=
  0 < w.length ∧
    Word.Valid w ∧
    Word.twoSteps w = Critical.beattyIndex w.length ∧
    ∀ q : ℕ,
      0 < q →
      q < w.length →
        Critical.beattyIndex q + 1 ≤ suffixTwoDepth w q

namespace IsAdmissibleBlock

/-- 許容ブロックは非空。 -/
theorem length_pos
    {w : Word}
    (h : IsAdmissibleBlock w) :
    0 < w.length :=
  h.1

/-- 許容ブロックの全指数は正。 -/
theorem valid
    {w : Word}
    (h : IsAdmissibleBlock w) :
    Word.Valid w :=
  h.2.1

/-- 許容ブロックの total depth は Beatty roof に exact。 -/
theorem totalTwoDepth_eq_beattyIndex
    {w : Word}
    (h : IsAdmissibleBlock w) :
    Word.twoSteps w = Critical.beattyIndex w.length :=
  h.2.2.1

/-- proper positive suffix の defining lower bound。 -/
theorem suffixTwoDepth_lower
    {w : Word}
    (h : IsAdmissibleBlock w)
    {q : ℕ}
    (hqPos : 0 < q)
    (hqLt : q < w.length) :
    Critical.beattyIndex q + 1 ≤ suffixTwoDepth w q :=
  h.2.2.2 q hqPos hqLt

end IsAdmissibleBlock

/--
全 two-depth は prefix と残り suffix の和に exact に分解する。
定義ではなく `List.take_append_drop` からの derived view。
-/
theorem twoSteps_eq_prefixTwoDepth_add_drop
    (w : Word)
    (t : ℕ) :
    Word.twoSteps w =
      Word.prefixTwoDepth w t + Word.twoSteps (w.drop t) := by
  calc
    Word.twoSteps w =
        Word.twoSteps (w.take t ++ w.drop t) := by
          rw [List.take_append_drop]
    _ =
        Word.twoSteps (w.take t) + Word.twoSteps (w.drop t) := by
          rw [Word.twoSteps_append]
    _ =
        Word.prefixTwoDepth w t + Word.twoSteps (w.drop t) := by
          rfl

/-- full suffix は word 全体の depth。 -/
@[simp] theorem suffixTwoDepth_length
    (w : Word) :
    suffixTwoDepth w w.length = Word.twoSteps w := by
  simp [suffixTwoDepth]

end IntegerReduction
end Collatz3
