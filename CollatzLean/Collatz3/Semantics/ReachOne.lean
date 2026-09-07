import CollatzLean.Collatz3.Semantics.Runs

/-!
# Collatz3: 1 への有限到達

`EndsAtOne` は「この finite run の終点が 1」という薄い語彙だけを表す。
`FirstHitsOne` はさらに、開始点が 1 ではなく、どの真の初期部分でもまだ 1 に
到達していないことを要求する。

ここでは canonical residue や affine consequence を導入しない。
-/

namespace Collatz3

/-- word `w` を actual に実行すると終点が `1`。 -/
def EndsAtOne (w : Word) (x : ℕ) : Prop :=
  Runs w x 1

/--
word の最後で初めて `1` に到達する。
`frontWord ++ backWord = w` かつ `backWord` 非空なら、`frontWord` は真の初期部分。
-/
def FirstHitsOne (w : Word) (x : ℕ) : Prop :=
  EndsAtOne w x ∧
    x ≠ 1 ∧
    ∀ frontWord backWord : Word,
      w = frontWord ++ backWord →
      backWord ≠ [] →
      ¬ Runs frontWord x 1

namespace FirstHitsOne

/-- first hit は特に終点 1 の run。 -/
theorem endsAtOne
    {w : Word} {x : ℕ}
    (h : FirstHitsOne w x) :
    EndsAtOne w x :=
  h.1

/-- first hit の開始点は 1 ではない。 -/
theorem start_ne_one
    {w : Word} {x : ℕ}
    (h : FirstHitsOne w x) :
    x ≠ 1 :=
  h.2.1

/-- first hit の word は非空。 -/
theorem word_nonempty
    {w : Word} {x : ℕ}
    (h : FirstHitsOne w x) :
    w ≠ [] := by
  intro hw
  subst w
  have hRun : Runs ([] : Word) x 1 := h.endsAtOne
  cases hRun
  exact h.start_ne_one rfl

end FirstHitsOne
end Collatz3
