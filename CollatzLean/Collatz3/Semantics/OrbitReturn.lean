import CollatzLean.Collatz3.Semantics.Runs


/-!
# Collatz3: actual odd-only 軌道の return

文字列の反復とは分離し、actual `Runs` が同じ整数へ戻ることだけを扱う。
`PrimitiveReturn` は真の非空初期部分ではまだ開始点へ戻らない最小 return。

任意の return から最初の return prefix を primitive return として正規化でき、
同じ基点の primitive return word は finite run の決定性により一意になる。
-/

namespace Collatz3

/-- 非空 word の actual run が開始点へ戻る。 -/
def ReturnsTo (w : Word) (x : ℕ) : Prop :=
  w ≠ [] ∧ Runs w x x

/--
開始点 `x` への primitive return。
非空の真の初期部分では `x` に戻らない。
-/
def PrimitiveReturn (w : Word) (x : ℕ) : Prop :=
  ReturnsTo w x ∧
    ∀ frontWord backWord : Word,
      w = frontWord ++ backWord →
      frontWord ≠ [] →
      backWord ≠ [] →
      ¬ Runs frontWord x x

namespace ReturnsTo

/-- return word は非空。 -/
theorem word_nonempty
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    w ≠ [] :=
  h.1

/-- return は actual run。 -/
theorem run
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    Runs w x x :=
  h.2

/-- return の開始点は奇数。 -/
theorem start_odd
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    Odd x :=
  h.run.start_odd_of_nonempty h.word_nonempty

/--
任意の非空 return には primitive return が存在する。

最初の一段の終点がすぐ基点なら一段 return が primitive。
そうでなければ残りの finite run から基点への first-hit prefix を有限に取り出す。
classical choice や無限探索は使わない。
-/
theorem exists_primitiveReturn
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    ∃ v : Word, PrimitiveReturn v x := by
  cases w with
  | nil =>
      exact False.elim (h.word_nonempty rfl)
  | cons e u =>
      rcases Runs.exists_intermediate_of_cons h.run with
        ⟨m, hstep, htail⟩
      by_cases hmx : m = x
      · subst m
        refine
          ⟨[e],
            ⟨by simp, Runs.cons hstep (Runs.nil x)⟩,
            ?_⟩
        intro front back hEq hFrontNonempty hBackNonempty hFrontRun
        have hFrontPos : 0 < Word.oddSteps front := by
          cases front with
          | nil => contradiction
          | cons a as => simp
        have hBackPos : 0 < Word.oddSteps back := by
          cases back with
          | nil => contradiction
          | cons a as => simp
        have hSteps := congrArg Word.oddSteps hEq
        simp [Word.oddSteps_append] at hSteps
        omega
      · rcases Runs.exists_firstHitPrefix htail hmx with
          ⟨v, _tail, _hSplit, hvRun, _hvNonempty, hvFirst⟩
        refine
          ⟨e :: v,
            ⟨by simp, Runs.cons hstep hvRun⟩,
            ?_⟩
        intro front back hEq hFrontNonempty hBackNonempty hFrontRun
        cases front with
        | nil => contradiction
        | cons f fs =>
            rcases Runs.exists_intermediate_of_cons hFrontRun with
              ⟨n, hstep', htail'⟩
            simp only [List.cons_append] at hEq
            injection hEq with hef hRest
            subst f
            have hmn : m = n :=
              (OddStep.deterministic hstep hstep').2
            subst n
            exact hvFirst fs back hRest hBackNonempty htail'


end ReturnsTo

namespace PrimitiveReturn

/-- primitive return は特に return。 -/
theorem returnsTo
    {w : Word} {x : ℕ}
    (h : PrimitiveReturn w x) :
    ReturnsTo w x :=
  h.1

/--
同じ基点の primitive return word は一意。
片方が他方の真の prefix なら、長い方の primitive 性に反する。
-/
theorem word_unique
    {u v : Word}
    {x : ℕ}
    (hu : PrimitiveReturn u x)
    (hv : PrimitiveReturn v x) :
    u = v := by
  rcases Runs.prefixComparable_of_common_start
      hu.returnsTo.run hv.returnsTo.run with
      ⟨t, hEq, hRun⟩ | ⟨t, hEq, hRun⟩
  · by_cases ht : t = []
    · subst t
      simpa using hEq.symm
    · exact False.elim
        (hv.2 u t hEq hu.returnsTo.word_nonempty ht hu.returnsTo.run)
  · by_cases ht : t = []
    · subst t
      simpa using hEq
    · exact False.elim
        (hu.2 v t hEq hv.returnsTo.word_nonempty ht hv.returnsTo.run)

end PrimitiveReturn

end Collatz3
