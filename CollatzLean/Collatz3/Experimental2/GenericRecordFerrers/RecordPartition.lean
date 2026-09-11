import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.ChordRank
import Mathlib.Data.List.Sort

/-!
# Collatz3 Experimental2: 一般屋根の canonical record partition

`GenericRecordFerrers.ChordRank` の弦順位から、strict running minimum を有限計算で抽出し、
その切断点列を隣接差の block length 列へ変換する。

このファイルの正本は任意の `anchor` を受け取る

* `recordCutsAfter`,
* `recordLengthsAfter`

である。

将来の一般 RecordFerrers で使う標準 anchor `1` は薄い特殊化として

* `canonicalRecordCuts`,
* `canonicalRecordLengths`

にだけ現れる。

ここではまだ

* `HasUnitCarry β`,
* `IsAdmissibleRoofPath β m height`,
* roof cut であること,
* carry compatibility,
* `NoRecordLevelTie`

を要求しない。record partition の有限順序論だけを分離する。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
`anchor` より後の cut `k` が、それ以前の全弦順位より strict に低い。

比較集合には `anchor` 自身を含める。
-/
def IsRecordCutAfter
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor k : ℕ) : Prop :=
  anchor < k ∧
    k < m ∧
    ∀ j : Fin k,
      anchor ≤ j.1 →
        chordRank β m height k < chordRank β m height j.1

/-- `IsRecordCutAfter` は有限比較だけなので計算可能に判定できる。 -/
instance instDecidableIsRecordCutAfter
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor k : ℕ) :
    Decidable (IsRecordCutAfter β m height anchor k) := by
  unfold IsRecordCutAfter
  infer_instance

/-- `Fin k` 版の定義を通常の自然数区間で読む仕様定理。 -/
theorem isRecordCutAfter_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor k : ℕ} :
    IsRecordCutAfter β m height anchor k ↔
      anchor < k ∧
      k < m ∧
      ∀ j : ℕ,
        anchor ≤ j →
        j < k →
          chordRank β m height k < chordRank β m height j := by
  constructor
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj hjk
    exact H.2.2 ⟨j, hjk⟩ haj
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj
    exact H.2.2 j.1 haj j.2

/-- 指定 anchor より後の deterministic strict record cut 列。 -/
def recordCutsAfter
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor : ℕ) : List ℕ :=
  (List.range m).filter
    (fun k => IsRecordCutAfter β m height anchor k)

/-- `recordCutsAfter` の membership specification。 -/
theorem mem_recordCutsAfter_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor k : ℕ} :
    k ∈ recordCutsAfter β m height anchor ↔
      k < m ∧ IsRecordCutAfter β m height anchor k := by
  simp [recordCutsAfter]

/-- record cut は必ず指定 anchor より後ろにある。 -/
theorem recordCut_gt_anchor
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor k : ℕ}
    (hk : k ∈ recordCutsAfter β m height anchor) :
    anchor < k := by
  have hSpec :=
    (mem_recordCutsAfter_iff
      (β := β) (m := m) (height := height) (anchor := anchor) (k := k)).1 hk
  exact hSpec.2.1

/-- `recordCutsAfter` は index 順に strict に増加する。 -/
theorem recordCutsAfter_pairwise_lt
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor : ℕ) :
    (recordCutsAfter β m height anchor).Pairwise (fun x y => x < y) := by
  unfold recordCutsAfter
  have hRange :
      (List.range m).Pairwise (fun x y => x < y) :=
    List.pairwise_lt_range
  exact hRange.filter _

/--
`a` から `terminal` までの間にある cut 列が、
現在位置から終端へ向かって strict に増加していること。

rank や屋根算術を含まない純粋な list-order predicate。
-/
def StrictCutChainFrom (terminal : ℕ) : ℕ → List ℕ → Prop
  | a, [] => a < terminal
  | a, k :: ks =>
      a < k ∧
      k < terminal ∧
      StrictCutChainFrom terminal k ks

/-- strict cut chain 内の任意の cut は current start より後ろにある。 -/
theorem lt_of_mem_of_strictCutChainFrom
    {terminal a : ℕ}
    {cuts : List ℕ}
    (C : StrictCutChainFrom terminal a cuts)
    {k : ℕ}
    (hk : k ∈ cuts) :
    a < k := by
  induction cuts generalizing a with
  | nil =>
      simp at hk
  | cons q qs ih =>
      simp only [StrictCutChainFrom] at C
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact C.1
      · exact lt_trans C.1 (ih C.2.2 hk)

/--
pairwise increasing で、全 cut が `(a, terminal)` 内なら strict cut chain になる。
-/
theorem strictCutChainFrom_of_pairwise_bounds
    {terminal a : ℕ}
    {cuts : List ℕ}
    (haTerminal : a < terminal)
    (hBounds :
      ∀ k ∈ cuts,
        a < k ∧ k < terminal)
    (hPair : cuts.Pairwise (fun x y => x < y)) :
    StrictCutChainFrom terminal a cuts := by
  induction cuts generalizing a with
  | nil =>
      simpa [StrictCutChainFrom] using haTerminal
  | cons k ks ih =>
      simp only [List.pairwise_cons] at hPair
      have hkBounds := hBounds k (by simp)
      have hTailBounds :
          ∀ q ∈ ks,
            k < q ∧ q < terminal := by
        intro q hq
        refine ⟨hPair.1 q hq, ?_⟩
        exact (hBounds q (by simp [hq])).2
      exact
        ⟨hkBounds.1,
          hkBounds.2,
          ih hkBounds.2 hTailBounds hPair.2⟩

/-- `recordCutsAfter` は anchor から終端 `m` までの strict cut chain。 -/
theorem recordCutsAfter_strictCutChain
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor : ℕ}
    (hAnchor : anchor < m) :
    StrictCutChainFrom m anchor (recordCutsAfter β m height anchor) := by
  apply strictCutChainFrom_of_pairwise_bounds
  · exact hAnchor
  · intro k hk
    have hSpec :=
      (mem_recordCutsAfter_iff
        (β := β) (m := m) (height := height) (anchor := anchor) (k := k)).1 hk
    exact ⟨hSpec.2.1, hSpec.1⟩
  · exact recordCutsAfter_pairwise_lt β m height anchor

/--
strict cut 列から隣接差を取り、最後に terminal までの差を付ける。

`[k₁, k₂, ..., kₛ]` から
`[k₁-a, k₂-k₁, ..., terminal-kₛ]` を作る。
-/
def blockLengthsFromCuts (terminal : ℕ) : ℕ → List ℕ → List ℕ
  | a, [] => [terminal - a]
  | a, k :: ks =>
      (k - a) :: blockLengthsFromCuts terminal k ks

/-- `blockLengthsFromCuts` は常に非空。 -/
theorem blockLengthsFromCuts_ne_nil
    (terminal a : ℕ)
    (cuts : List ℕ) :
    blockLengthsFromCuts terminal a cuts ≠ [] := by
  cases cuts <;> simp [blockLengthsFromCuts]

/-- strict cut chain から作った全 block length は正。 -/
theorem blockLengthsFromCuts_pos
    {terminal a : ℕ}
    {cuts : List ℕ}
    (C : StrictCutChainFrom terminal a cuts) :
    ∀ r ∈ blockLengthsFromCuts terminal a cuts, 0 < r := by
  induction cuts generalizing a with
  | nil =>
      simp only [StrictCutChainFrom] at C
      intro r hr
      simp only [blockLengthsFromCuts, List.mem_singleton] at hr
      subst r
      exact Nat.sub_pos_of_lt C
  | cons k ks ih =>
      simp only [StrictCutChainFrom] at C
      intro r hr
      simp only [blockLengthsFromCuts, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Nat.sub_pos_of_lt C.1
      · exact ih C.2.2 r hr

/-- strict cut chain から作った block length の総和は start から terminal までの距離。 -/
theorem blockLengthsFromCuts_sum
    {terminal a : ℕ}
    {cuts : List ℕ}
    (C : StrictCutChainFrom terminal a cuts) :
    (blockLengthsFromCuts terminal a cuts).sum = terminal - a := by
  induction cuts generalizing a with
  | nil =>
      simp [blockLengthsFromCuts]
  | cons k ks ih =>
      simp only [StrictCutChainFrom] at C
      simp only [blockLengthsFromCuts, List.sum_cons]
      rw [ih C.2.2]
      omega

/--
任意 anchor に対する record block length 列。
cut 列は `recordCutsAfter` から決定的に計算される。
-/
def recordLengthsAfter
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor : ℕ) : List ℕ :=
  blockLengthsFromCuts m anchor (recordCutsAfter β m height anchor)

/-- 任意 anchor の record block length 列は常に非空。 -/
theorem recordLengthsAfter_ne_nil
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor : ℕ) :
    recordLengthsAfter β m height anchor ≠ [] := by
  unfold recordLengthsAfter
  exact blockLengthsFromCuts_ne_nil m anchor (recordCutsAfter β m height anchor)

/-- `anchor < m` なら全 record block length は正。 -/
theorem recordLengthsAfter_pos
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor : ℕ}
    (hAnchor : anchor < m) :
    ∀ r ∈ recordLengthsAfter β m height anchor, 0 < r := by
  unfold recordLengthsAfter
  exact blockLengthsFromCuts_pos
    (recordCutsAfter_strictCutChain
      (β := β) (height := height) hAnchor)

/-- `anchor < m` なら record block length の総和は exact に `m-anchor`。 -/
theorem recordLengthsAfter_sum
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor : ℕ}
    (hAnchor : anchor < m) :
    (recordLengthsAfter β m height anchor).sum = m - anchor := by
  unfold recordLengthsAfter
  exact blockLengthsFromCuts_sum
    (recordCutsAfter_strictCutChain
      (β := β) (height := height) hAnchor)

/-- 一般 RecordFerrers 実験で使う標準の正の anchor。 -/
def canonicalAnchor : ℕ := 1

/-- 標準 anchor `1` より後の deterministic strict record cut 列。 -/
def canonicalRecordCuts
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : List ℕ :=
  recordCutsAfter β m height canonicalAnchor

/--
標準 anchor `1` に対する canonical record block length 列。

この段階では `β 1 = 1` や admissibility は要求せず、単に record partition の標準座標を固定する。
-/
def canonicalRecordLengths
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : List ℕ :=
  recordLengthsAfter β m height canonicalAnchor

/-- canonical record block length 列は常に非空。 -/
theorem canonicalRecordLengths_ne_nil
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) :
    canonicalRecordLengths β m height ≠ [] := by
  unfold canonicalRecordLengths
  exact recordLengthsAfter_ne_nil β m height canonicalAnchor

/-- `1 < m` なら canonical block length はすべて正。 -/
theorem canonicalRecordLengths_pos
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (hm : 1 < m) :
    ∀ r ∈ canonicalRecordLengths β m height, 0 < r := by
  unfold canonicalRecordLengths
  exact recordLengthsAfter_pos
    (β := β) (height := height)
    (by simpa [canonicalAnchor] using hm)

/-- `1 < m` なら canonical block length の総和は exact に `m-1`。 -/
theorem canonicalRecordLengths_sum
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (hm : 1 < m) :
    (canonicalRecordLengths β m height).sum = m - 1 := by
  unfold canonicalRecordLengths
  simpa [canonicalAnchor] using
    (recordLengthsAfter_sum
      (β := β) (height := height)
      (anchor := canonicalAnchor)
      (by simpa [canonicalAnchor] using hm))

end GenericRecordFerrers
end Experimental2
end Collatz3
