import CollatzLean.Collatz3.Ferrers.RecordCanonical
import CollatzLean.Collatz3.Critical.RecordCarryExact
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

/-!
# Collatz3: canonical strict cuts と exact carry law

真の `RecordFerrers` を再導入する直前の 6A--6C をこのファイルで閉じる。

* 6A: deterministic な `initialRecordCuts` から block length 列を有限計算する。
* 6B: 隣接 strict record cut の間は、追加仮定なしで weak record excursion になる。
* 6C: exact carry compatibility が proper-prefix bound を与え、weak excursion を
  genuine strict record excursion へ昇格させる。

ここではまだ `RecordFerrers` 自体は定義しない。
`IsPrimitiveWidth` / `IsBestUpperWidth` も使わない。
-/

namespace Collatz3

namespace Ferrers

open Critical

/-! ## 6A: strict cut list から canonical block lengths -/

/--
`a` から `terminal` までの間にある strict cut 列が、
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
  exact blockLengthsFromCuts_pos (initialRecordCuts_strictCutChain (h := h) hm)

/-- canonical block lengths の総和は exact に `m-1`。 -/
theorem canonicalRecordLengths_sum
    {m : ℕ}
    {h : Profile m}
    (hm : 1 < m) :
    (canonicalRecordLengths h).sum = m - 1 := by
  simpa [canonicalRecordLengths, initialRoofAnchor] using
    blockLengthsFromCuts_sum
      (initialRecordCuts_strictCutChain (h := h) hm)

/-! ## 6B: canonical strict cuts の間は weak excursion -/

/--
record block の weak 版。

* 長さは正、
* interior は start rank 以上、
* endpoint では start rank より strict に下がる。

record-level tie をまだ禁止しない。
-/
def IsWeakRecordBlock
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : Prop :=
  0 < r ∧
    (∀ j : ℕ,
      0 < j →
      j < r →
        profileChordRank h a ≤ profileChordRank h (a + j)) ∧
    profileChordRank h (a + r) < profileChordRank h a

namespace IsWeakRecordBlock

theorem length_pos
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsWeakRecordBlock h a r) :
    0 < r :=
  B.1

theorem interior
    {m : ℕ}
    {h : Profile m}
    {a r j : ℕ}
    (B : IsWeakRecordBlock h a r)
    (hjPos : 0 < j)
    (hjLt : j < r) :
    profileChordRank h a ≤ profileChordRank h (a + j) :=
  B.2.1 j hjPos hjLt

theorem end_drop
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsWeakRecordBlock h a r) :
    profileChordRank h (a + r) < profileChordRank h a :=
  B.2.2

end IsWeakRecordBlock

/--
strict cut list が切り出す各区間を weak record block として読む canonical view。
最後の区間は terminal `m` まで。
-/
def CanonicalWeakBlocksFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | a, [] =>
      IsWeakRecordBlock h a (m - a)
  | a, k :: ks =>
      IsWeakRecordBlock h a (k - a) ∧
        IsRoofCut h k ∧
        CanonicalWeakBlocksFrom h k ks

/--
relative strict record start `a` より後で最初に start rank を strict に下回る cut は、
元 anchor から見ても strict record cut になる。
-/
private theorem firstLower_isRecordCutAfter
    {m : ℕ}
    {h : Profile m}
    {anchor a k : ℕ}
    (haRecord : IsRelativeRecordStart h anchor a)
    (hak : a < k)
    (hkm : k < m)
    (hLower :
      profileChordRank h k < profileChordRank h a)
    (hFirst :
      ∀ j : ℕ,
        a < j →
        j < k →
          profileChordRank h a ≤ profileChordRank h j) :
    IsRecordCutAfter h anchor k := by
  apply (isRecordCutAfter_iff).2
  refine ⟨lt_of_le_of_lt haRecord.1 hak, hkm, ?_⟩
  intro j haj hjk
  by_cases hja : j < a
  · have hPrev := haRecord.2.2 j haj hja
    exact lt_trans hLower hPrev
  by_cases hEq : j = a
  · subst j
    exact hLower
  · have hajStrict : a < j := by omega
    exact lt_of_lt_of_le hLower (hFirst j hajStrict hjk)

/--
current start `a` より前に未列挙の strict lower cut が無いなら、
次の canonical cut までの rank は start rank 以上。
-/
private theorem rank_le_before_next_recordCut
    {m : ℕ}
    {h : Profile m}
    {anchor a endIndex : ℕ}
    {cuts : List ℕ}
    (haRecord : IsRelativeRecordStart h anchor a)
    (hComplete :
      ∀ q : ℕ,
        IsRecordCutAfter h anchor q →
        a < q →
        q ∈ cuts)
    (hNoCutBefore :
      ∀ q ∈ cuts,
        ¬ (a < q ∧ q < endIndex))
    {j : ℕ}
    (haj : a < j)
    (hjEnd : j < endIndex)
    (hEndLeM : endIndex ≤ m) :
    profileChordRank h a ≤ profileChordRank h j := by
  by_contra hNot
  have hjLower :
      profileChordRank h j < profileChordRank h a :=
    lt_of_not_ge hNot
  have hExists :
      ∃ q : ℕ,
        a < q ∧
        q < endIndex ∧
        profileChordRank h q < profileChordRank h a :=
    ⟨j, haj, hjEnd, hjLower⟩
  let q : ℕ := Nat.find hExists
  have hq := Nat.find_spec hExists
  have hqFirst :
      ∀ t : ℕ,
        a < t →
        t < q →
          profileChordRank h a ≤ profileChordRank h t := by
    intro t hat htq
    by_contra hNotLe
    have htLower :
        profileChordRank h t < profileChordRank h a :=
      lt_of_not_ge hNotLe
    have htCandidate :
        a < t ∧
        t < endIndex ∧
        profileChordRank h t < profileChordRank h a :=
      ⟨hat, lt_trans htq hq.2.1, htLower⟩
    have hqLe : q ≤ t := by
      dsimp [q]
      exact Nat.find_min' hExists htCandidate
    omega
  have hqm : q < m := lt_of_lt_of_le hq.2.1 hEndLeM
  have hRecordQ : IsRecordCutAfter h anchor q :=
    firstLower_isRecordCutAfter
      haRecord hq.1 hqm hq.2.2 hqFirst
  have hMem := hComplete q hRecordQ hq.1
  exact hNoCutBefore q hMem ⟨hq.1, hq.2.1⟩

private theorem canonicalWeakBlocksFrom_of_cuts
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    (recordCut_isRoof :
      ∀ {k : ℕ},
        IsRecordCutAfter h anchor k →
        IsRoofCut h k) :
    ∀ (a : ℕ) (cuts : List ℕ),
      IsRoofCut h a →
      IsRelativeRecordStart h anchor a →
      StrictCutChainFrom m a cuts →
      (∀ k ∈ cuts, IsRecordCutAfter h anchor k) →
      (∀ k : ℕ,
        IsRecordCutAfter h anchor k →
        a < k →
        k ∈ cuts) →
      CanonicalWeakBlocksFrom h a cuts
  | a, [], hRoof, hRelative, hChain, _hRecords, hComplete => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom]
      refine ⟨Nat.sub_pos_of_lt hChain, ?_, ?_⟩
      · intro j hjPos hjLt
        have haj : a < a + j := by
          omega
        have hjm : a + j < m := by
          omega
        exact rank_le_before_next_recordCut
          hRelative
          hComplete
          (by simp)
          haj
          hjm
          (Nat.le_refl m)
      · have hIndex :
            a + (m - a) = m :=
          Nat.add_sub_of_le
            (Nat.le_of_lt hChain)
        rw [hIndex, profileChordRank_terminal_eq_zero]
        exact profileChordRank_pos_of_roofCut hRoof
  | a, k :: ks, hRoof, hRelative, hChain,
      hRecords, hComplete => by
      simp only [StrictCutChainFrom] at hChain
      have hak : a < k :=
        hChain.1
      have hkm : k < m :=
        hChain.2.1
      have hTailChain :=
        hChain.2.2
      have hRecordK :
          IsRecordCutAfter h anchor k :=
        hRecords k (by simp)
      have hNoCutBefore :
          ∀ q ∈ k :: ks,
            ¬ (a < q ∧ q < k) := by
        intro q hq hBetween
        simp only [List.mem_cons] at hq
        rcases hq with hEq | hTail
        · subst q
          omega
        · have hkq :=
            lt_of_mem_of_strictCutChainFrom
              hTailChain hTail
          omega
      have hWeakInterior :
          ∀ j : ℕ,
            0 < j →
            j < k - a →
              profileChordRank h a ≤
                profileChordRank h (a + j) := by
        intro j hjPos hjLt
        have haj : a < a + j := by
          omega
        have hjk : a + j < k := by
          omega
        exact rank_le_before_next_recordCut
          hRelative
          hComplete
          hNoCutBefore
          haj
          hjk
          (Nat.le_of_lt hkm)
      have hRK :=
        (isRecordCutAfter_iff).1 hRecordK
      have hEndDrop :
          profileChordRank h k <
            profileChordRank h a :=
        hRK.2.2 a hRelative.1 hak
      have hIndex :
          a + (k - a) = k :=
        Nat.add_sub_of_le
          (Nat.le_of_lt hak)
      have hWeakBlock :
          IsWeakRecordBlock h a (k - a) := by
        refine
          ⟨Nat.sub_pos_of_lt hak,
            hWeakInterior,
            ?_⟩
        simpa [hIndex] using hEndDrop
      have hRoofK : IsRoofCut h k :=
        recordCut_isRoof hRecordK
      have hRelativeK :
          IsRelativeRecordStart h anchor k :=
        isRelativeRecordStart_of_recordCut hRecordK
      have hTailRecords :
          ∀ q ∈ ks,
            IsRecordCutAfter h anchor q := by
        intro q hq
        exact hRecords q (by simp [hq])
      have hTailComplete :
          ∀ q : ℕ,
            IsRecordCutAfter h anchor q →
            k < q →
            q ∈ ks := by
        intro q hqRecord hkq
        have hMem :=
          hComplete q hqRecord
            (lt_trans hak hkq)
        simp only [List.mem_cons] at hMem
        rcases hMem with hEq | hTail
        · subst q
          omega
        · exact hTail
      refine ⟨hWeakBlock, hRoofK, ?_⟩
      exact canonicalWeakBlocksFrom_of_cuts
        recordCut_isRoof
        k ks
        hRoofK
        hRelativeK
        hTailChain
        hTailRecords
        hTailComplete

/--
任意の admissible profile について、deterministic strict record cuts が切り出す区間は
自動的に weak record excursions になる。
`NoRecordLevelTie` は仮定しない。
-/
theorem canonicalWeakBlocksFrom_initialRecordCuts
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m) :
    CanonicalWeakBlocksFrom h initialRoofAnchor (initialRecordCuts h) := by
  have hRoof := initialRoofAnchor_isRoofCut A hm
  have hRelative :
      IsRelativeRecordStart h initialRoofAnchor initialRoofAnchor :=
    isRelativeRecordStart_anchor hRoof.lt_width
  have hChain := initialRecordCuts_strictCutChain (h := h) hm
  have hRecords :
      ∀ k ∈ initialRecordCuts h,
        IsRecordCutAfter h initialRoofAnchor k := by
    intro k hk
    change k ∈ recordCutsAfter h initialRoofAnchor at hk
    have hSpec := (mem_recordCutsAfter_iff).1 hk
    exact hSpec.2
  have hComplete :
      ∀ k : ℕ,
        IsRecordCutAfter h initialRoofAnchor k →
        initialRoofAnchor < k →
        k ∈ initialRecordCuts h := by
    intro k hRecord _hkAfter
    change k ∈ recordCutsAfter h initialRoofAnchor
    exact (mem_recordCutsAfter_iff).2 ⟨hRecord.2.1, hRecord⟩
  exact canonicalWeakBlocksFrom_of_cuts
    (isRoofCut_of_isRecordCutAfter A)
    initialRoofAnchor
    (initialRecordCuts h)
    hRoof hRelative hChain hRecords hComplete

/-! ## 6C: exact carry law が weak excursion を strict にする -/

/--
canonical strict-cut partition に沿った exact carry compatibility。

最後だけ terminal carry `0` を要求し、それ以前の各区間では
premature carry-1 roof return だけを禁止する。
-/
def CanonicalCarryCompatibleFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | a, [] =>
      NoPrematureCarryOneRoofReturn h a (m - a) ∧
        beattyCarry a (m - a) = 0
  | a, k :: ks =>
      NoPrematureCarryOneRoofReturn h a (k - a) ∧
        CanonicalCarryCompatibleFrom h k ks

/-- carry law で weak interior の equality case を排除した strict canonical blocks。 -/
def CanonicalStrictBlocksFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | a, [] =>
      Combinatorics.IsRecordBlock
        (profileChordRank h) a (m - a)
  | a, k :: ks =>
      Combinatorics.IsRecordBlock
          (profileChordRank h) a (k - a) ∧
        IsRoofCut h k ∧
        CanonicalStrictBlocksFrom h k ks

/--
local proper-prefix Beatty bound は chord rank の strict interior inequality を与える。
これが carry compatibility から record-level tie を消す算術 bridge。
-/
theorem profileChordRank_lt_add_of_localDepth_le_beatty
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a j : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hjPos : 0 < j)
    (hEndLt : a + j < m)
    (hDepth : localDepth h a j ≤ beattyIndex j) :
    profileChordRank h a < profileChordRank h (a + j) := by
  have hm : 0 < m := lt_trans hStartRoof.pos hStartRoof.lt_width
  have hChord :=
    beattyIndex_below_criticalChord
      (m := m) (r := j) hm hjPos
  have hScaled :
      m * localDepth h a j < criticalTwoDepth m * j :=
    lt_of_le_of_lt
      (Nat.mul_le_mul_left m hDepth)
      hChord
  have hScaledZ :
      (m : ℤ) * (localDepth h a j : ℤ) <
        (criticalTwoDepth m : ℤ) * (j : ℤ) := by
    exact_mod_cast hScaled
  have hDiff :=
    profileChordRank_add_sub A (Nat.le_of_lt hEndLt)
  have hPos :
      0 < profileChordRank h (a + j) - profileChordRank h a := by
    rw [hDiff]
    linarith
  exact sub_pos.mp hPos

/--
一つの weak record block は、premature carry-1 roof return が無ければ strict record block。
-/
theorem isRecordBlock_of_weak_of_noPrematureCarryOneRoofReturn
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hEnd : a + r ≤ m)
    (W : IsWeakRecordBlock h a r)
    (C : NoPrematureCarryOneRoofReturn h a r) :
    Combinatorics.IsRecordBlock (profileChordRank h) a r := by
  have hPrefix :=
    (localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
      A hStartRoof hEnd).2 C
  refine ⟨W.length_pos, ?_, W.end_drop⟩
  intro j hjPos hjLt
  have hEndLt : a + j < m := by omega
  exact profileChordRank_lt_add_of_localDepth_le_beatty
    A hStartRoof hjPos hEndLt (hPrefix j hjPos hjLt)

/--
6B の weak canonical blocks は exact carry compatibility により strict canonical blocks へ昇格する。
-/
theorem canonicalStrictBlocksFrom_of_weak_of_carry
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ∀ (a : ℕ) (cuts : List ℕ),
      IsRoofCut h a →
      StrictCutChainFrom m a cuts →
      CanonicalWeakBlocksFrom h a cuts →
      CanonicalCarryCompatibleFrom h a cuts →
      CanonicalStrictBlocksFrom h a cuts
  | a, [], hRoof, hChain, hWeak, hCarry => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom] at hWeak
      simp only [CanonicalCarryCompatibleFrom] at hCarry
      simp only [CanonicalStrictBlocksFrom]
      have hEnd : a + (m - a) ≤ m := by omega
      exact isRecordBlock_of_weak_of_noPrematureCarryOneRoofReturn
        A hRoof hEnd hWeak hCarry.1
  | a, k :: ks, hRoof, hChain, hWeak, hCarry => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom] at hWeak
      simp only [CanonicalCarryCompatibleFrom] at hCarry
      simp only [CanonicalStrictBlocksFrom]
      have hIndex : a + (k - a) = k := by omega
      have hEnd : a + (k - a) ≤ m := by omega
      have hStrict :
          Combinatorics.IsRecordBlock
            (profileChordRank h) a (k - a) :=
        isRecordBlock_of_weak_of_noPrematureCarryOneRoofReturn
          A hRoof hEnd hWeak.1 hCarry.1
      refine ⟨hStrict, hWeak.2.1, ?_⟩
      exact canonicalStrictBlocksFrom_of_weak_of_carry
        A k ks hWeak.2.1 hChain.2.2 hWeak.2.2 hCarry.2

/--
canonical exact carry law だけで、deterministic record partition の全区間が
strict record excursions になる。

これが 6C の中心結論であり、`NoRecordLevelTie` を独立仮定にしない。
-/
theorem canonicalStrictBlocksFrom_of_carry
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m)
    (C : CanonicalCarryCompatibleFrom
      h initialRoofAnchor (initialRecordCuts h)) :
    CanonicalStrictBlocksFrom
      h initialRoofAnchor (initialRecordCuts h) := by
  exact canonicalStrictBlocksFrom_of_weak_of_carry
    A initialRoofAnchor (initialRecordCuts h)
    (initialRoofAnchor_isRoofCut A hm)
    (initialRecordCuts_strictCutChain (h := h) hm)
    (canonicalWeakBlocksFrom_initialRecordCuts A hm)
    C

end Ferrers
end Collatz3
