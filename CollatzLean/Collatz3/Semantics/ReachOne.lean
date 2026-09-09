import CollatzLean.Collatz3.Semantics.Reachability


/-!
# Collatz3: 1 への有限到達

`ReachesOne x` は、指数語を忘れた意味で `x` が有限時間後に `1` へ到達することだけを表す。
これは軌道の最終挙動を分類するときの第1の基礎述語である。

`EndsAtOne w x` は、その到達を特定の有限指数語 `w` が実現するという有限証明書である。
したがって `ReachesOne` と `EndsAtOne` を同一視せず、前者を軌道側、後者を有限区間側に置く。

`FirstHitsOne` はさらに、開始点が `1` ではなく、どの真の初期部分でもまだ `1` に
到達していないことを要求する。これは第1分類の正規な有限証明書として使う。

ここでは canonical residue や affine consequence を導入しない。
-/

namespace Collatz3

/-- 正の長さを仮定せず、有限時間後に `1` へ到達することだけを表す。 -/
def ReachesOne (x : ℕ) : Prop :=
  Reaches x 1

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

namespace EndsAtOne

/-- 終点 `1` の有限 run は、軌道として `1` へ到達することの証明になる。 -/
theorem reachesOne
    {w : Word} {x : ℕ}
    (h : EndsAtOne w x) :
    ReachesOne x := by
  change Reaches x 1
  exact ⟨w, h⟩

end EndsAtOne

namespace ReachesOne

/-- `1` への有限到達には、それを実現する有限指数語が存在する。 -/
theorem exists_endsAtOne
    {x : ℕ}
    (h : ReachesOne x) :
    ∃ w : Word, EndsAtOne w x := by
  change Reaches x 1 at h
  exact h

/--
開始点が `1` でないなら、与えられた finite run を左から有限に調べ、
`1` へ初めて到達する prefix を取り出す。

`Runs.exists_firstHitPrefix` を使うため、classical choice や無限探索は不要。
-/
theorem exists_firstHitsOne_of_ne_one
    {x : ℕ}
    (hx : x ≠ 1)
    (h : ReachesOne x) :
    ∃ w : Word, FirstHitsOne w x := by
  rcases h.exists_endsAtOne with ⟨w, hw⟩
  rcases Runs.exists_firstHitPrefix hw hx with
    ⟨v, _tail, _hSplit, hvRun, _hvNonempty, hvFirst⟩
  exact ⟨v, hvRun, hx, hvFirst⟩

end ReachesOne

/-- `ReachesOne` は `EndsAtOne` 証明書が存在することと正確に同値。 -/
theorem reachesOne_iff_exists_endsAtOne
    (x : ℕ) :
    ReachesOne x ↔ ∃ w : Word, EndsAtOne w x := by
  constructor
  · exact ReachesOne.exists_endsAtOne
  · rintro ⟨w, hw⟩
    exact EndsAtOne.reachesOne hw

/--
第1分類の正規化。
`x = 1` なら空 run で既に終局点にあり、そうでなければ `FirstHitsOne` 証明書を持つ。
-/
theorem reachesOne_iff_eq_one_or_exists_firstHitsOne
    (x : ℕ) :
    ReachesOne x ↔
      x = 1 ∨ ∃ w : Word, FirstHitsOne w x := by
  constructor
  · intro h
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (ReachesOne.exists_firstHitsOne_of_ne_one hx h)
  · intro h
    rcases h with rfl | ⟨w, hw⟩
    · exact Reaches.refl 1
    · exact EndsAtOne.reachesOne hw.1

namespace FirstHitsOne

/-- first hit は特に終点 1 の run。 -/
theorem endsAtOne
    {w : Word} {x : ℕ}
    (h : FirstHitsOne w x) :
    EndsAtOne w x :=
  h.1

/-- first hit は特に軌道として `1` へ到達する。 -/
theorem reachesOne
    {w : Word} {x : ℕ}
    (h : FirstHitsOne w x) :
    ReachesOne x :=
  EndsAtOne.reachesOne h.endsAtOne

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

/--
同じ開始値から `1` に初めて到達する word は一意。
finite run の prefix 決定性により、片方が他方の真の prefix なら長い方の first-hit 性に反する。
-/
theorem word_unique
    {u v : Word}
    {x : ℕ}
    (hu : FirstHitsOne u x)
    (hv : FirstHitsOne v x) :
    u = v := by
  rcases Runs.prefixComparable_of_common_start
      hu.endsAtOne hv.endsAtOne with
      ⟨t, hEq, hRun⟩ | ⟨t, hEq, hRun⟩
  · by_cases ht : t = []
    · subst t
      simpa using hEq.symm
    · exact False.elim
        (hv.2.2 u t hEq ht hu.endsAtOne)
  · by_cases ht : t = []
    · subst t
      simpa using hEq
    · exact False.elim
        (hu.2.2 v t hEq ht hv.endsAtOne)

end FirstHitsOne

/--
`x ≠ 1` かつ `ReachesOne x` なら first-hit word は存在し、しかも一意。
-/
theorem existsUnique_firstHitsOne
    {x : ℕ}
    (hx : x ≠ 1)
    (h : ReachesOne x) :
    ∃! w : Word, FirstHitsOne w x := by
  rcases ReachesOne.exists_firstHitsOne_of_ne_one hx h with ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  intro v hv
  exact FirstHitsOne.word_unique hv hw

end Collatz3
