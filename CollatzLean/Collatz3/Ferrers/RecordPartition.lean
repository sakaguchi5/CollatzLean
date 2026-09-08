import CollatzLean.Collatz3.Ferrers.RecordView
import Mathlib.Data.List.Sort

/-!
# Collatz3: deterministic canonical record partition

`RecordView` が有限計算で与える `initialRecordCuts` から、
隣接差として canonical block length 列を作る純粋な有限層。

このファイルには

* `NoRecordLevelTie`
* carry
* critical local geometry
* `CriticalRecordSkeleton`

を入れない。

従って依存方向は

`RecordView → RecordPartition → RecordCanonical`

となり、`RecordCanonical` が canonical length 列を直接利用しても
import 循環は起こらない。
-/

namespace Collatz3
namespace Ferrers

open Critical

/--
`a` から `terminal` までの間にある cut 列が、
現在位置から terminal へ向かって strict に増加していること。

単なる list-order の薄い仕様であり、rank や Collatz 固有算術は含まない。
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
strict cut 列から隣接差を取り、最後に terminal までの差を付ける。

`[k₁, k₂, ..., kₛ]` から
`[k₁-a, k₂-k₁, ..., terminal-kₛ]` を作る有限計算。
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

/-- canonical block lengths の総和は start から terminal までの距離。 -/
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

/-- pairwise increasing で全 cut が `(a,terminal)` 内なら strict cut chain になる。 -/
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

/-- `initialRecordCuts` は index 順に strict に増加する。 -/
theorem initialRecordCuts_pairwise_lt
    {m : ℕ}
    (h : Profile m) :
    (initialRecordCuts h).Pairwise (fun x y => x < y) := by
  unfold initialRecordCuts recordCutsAfter
  have hRange :
      (List.range m).Pairwise (fun x y => x < y) :=
    List.pairwise_lt_range
  exact hRange.filter _

/-- canonical strict record cut list は anchor `1` から terminal まで strict chain。 -/
theorem initialRecordCuts_strictCutChain
    {m : ℕ}
    {h : Profile m}
    (hm : 1 < m) :
    StrictCutChainFrom m initialRoofAnchor (initialRecordCuts h) := by
  apply strictCutChainFrom_of_pairwise_bounds
  · simpa [initialRoofAnchor] using hm
  · intro k hk
    refine ⟨initialRecordCut_gt_anchor hk, ?_⟩
    change k ∈ recordCutsAfter h initialRoofAnchor at hk
    have hSpec := (mem_recordCutsAfter_iff).1 hk
    exact hSpec.1
  · exact initialRecordCuts_pairwise_lt h

/-- profile が計算的に決める canonical record block length 列。 -/
def canonicalRecordLengths
    {m : ℕ}
    (h : Profile m) : List ℕ :=
  blockLengthsFromCuts m initialRoofAnchor (initialRecordCuts h)

/-- canonical block lengths はすべて正。 -/
theorem canonicalRecordLengths_pos
    {m : ℕ}
    {h : Profile m}
    (hm : 1 < m) :
    ∀ r ∈ canonicalRecordLengths h, 0 < r := by
  exact
    blockLengthsFromCuts_pos
      (initialRecordCuts_strictCutChain (h := h) hm)

/-- canonical block lengths の総和は exact に `m-1`。 -/
theorem canonicalRecordLengths_sum
    {m : ℕ}
    {h : Profile m}
    (hm : 1 < m) :
    (canonicalRecordLengths h).sum = m - 1 := by
  simpa [canonicalRecordLengths, initialRoofAnchor] using
    blockLengthsFromCuts_sum
      (initialRecordCuts_strictCutChain (h := h) hm)

end Ferrers
end Collatz3
