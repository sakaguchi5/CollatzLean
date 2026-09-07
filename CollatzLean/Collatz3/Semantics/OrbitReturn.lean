import CollatzLean.Collatz3.Semantics.Runs

/-!
# Collatz3: actual odd-only 軌道の return

文字列の反復とは分離し、actual `Runs` が同じ整数へ戻ることだけを扱う。
`PrimitiveReturn` は真の非空初期部分ではまだ開始点へ戻らない最小 return。
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

end ReturnsTo

namespace PrimitiveReturn

/-- primitive return は特に return。 -/
theorem returnsTo
    {w : Word} {x : ℕ}
    (h : PrimitiveReturn w x) :
    ReturnsTo w x :=
  h.1

end PrimitiveReturn
end Collatz3
