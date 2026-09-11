import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordPartitionInverse
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordRoofBridge
import CollatzLean.Collatz3.Experimental2.RecordCarryLaw
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: canonical record partition から roof block chain へ

第1--4段階で得た deterministic record geometry を、既存 `Experimental2.RecordCarryLaw` が
受け取れる有限 block chain へ接続する。

このファイルでは三つを閉じる。

1. strict record cut 列が切り出す各区間の weak record geometry、
2. canonical record cut が genuine roof cut であることとの合成、
3. `canonicalRecordLengths` が `RoofBlockChainFrom` を成すこと。

これにより次段階では、canonical partition に対して既存の
`FullCarryCompatibleFrom` / `ContextualCarryCompatibleFrom` /
`LocalRoofCriticalBlocksFrom` を直接適用できる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
proper roof cut の弦順位は正。

roof 上では `height a = β a` なので、一般の strict critical chord
`m * β a < criticalDepth β m * a` をそのまま順位の正値性として読める。
-/
theorem chordRank_pos_of_properRoofCut
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a : ℕ}
    (R : IsProperRoofCut β m height a) :
    0 < chordRank β m height a := by
  have hChord :
      m * β a < criticalDepth β m * a :=
    U.below_criticalChord R.1
  have hChordZ :
      (m : ℤ) * (β a : ℤ) <
        (criticalDepth β m : ℤ) * (a : ℤ) := by
    exact_mod_cast hChord
  have hRoof : height a = β a := R.2.2
  rw [chordRank_of_lt (β := β) (height := height) R.2.1]
  rw [hRoof]
  linarith

/-- anchor から見て start `a` が relative strict record である。 -/
def IsRelativeRecordStart
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor a : ℕ) : Prop :=
  anchor ≤ a ∧
    a < m ∧
    ∀ j : ℕ,
      anchor ≤ j →
      j < a →
        chordRank β m height a < chordRank β m height j

/-- anchor 自身は relative record start。 -/
theorem isRelativeRecordStart_anchor
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor : ℕ}
    (ha : anchor < m) :
    IsRelativeRecordStart β m height anchor anchor := by
  refine ⟨le_rfl, ha, ?_⟩
  intro j haj hja
  omega

/-- strict record cut は relative record start でもある。 -/
theorem isRelativeRecordStart_of_recordCut
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor k : ℕ}
    (R : IsRecordCutAfter β m height anchor k) :
    IsRelativeRecordStart β m height anchor k := by
  have hR :=
    (isRecordCutAfter_iff
      (β := β) (m := m) (height := height)
      (anchor := anchor) (k := k)).1 R
  exact ⟨Nat.le_of_lt hR.1, hR.2.1, hR.2.2⟩

/--
一つの canonical record block の weak 版。

* 長さは正、
* interior では start rank 以上、
* endpoint では start rank より strict に下がる。

`NoRecordLevelTie` はまだ要求しない。
-/
def IsWeakRecordBlock
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a r : ℕ) : Prop :=
  0 < r ∧
    (∀ j : ℕ,
      0 < j →
      j < r →
        chordRank β m height a ≤ chordRank β m height (a + j)) ∧
    chordRank β m height (a + r) < chordRank β m height a

namespace IsWeakRecordBlock

/-- weak record block の長さは正。 -/
theorem length_pos
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {a r : ℕ}
    (B : IsWeakRecordBlock β m height a r) :
    0 < r :=
  B.1

/-- weak record block の proper interior では start rank 以上。 -/
theorem interior
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {a r j : ℕ}
    (B : IsWeakRecordBlock β m height a r)
    (hjPos : 0 < j)
    (hjLt : j < r) :
    chordRank β m height a ≤ chordRank β m height (a + j) :=
  B.2.1 j hjPos hjLt

/-- weak record block の endpoint では rank が strict に下がる。 -/
theorem end_drop
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {a r : ℕ}
    (B : IsWeakRecordBlock β m height a r) :
    chordRank β m height (a + r) < chordRank β m height a :=
  B.2.2

end IsWeakRecordBlock

/--
strict cut list が切り出す各区間を weak record block として読む canonical view。
最後の区間だけは terminal `m` まで読む。
-/
def CanonicalWeakBlocksFrom
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | a, [] =>
      IsWeakRecordBlock β m height a (m - a)
  | a, k :: ks =>
      IsWeakRecordBlock β m height a (k - a) ∧
        IsProperRoofCut β m height k ∧
        CanonicalWeakBlocksFrom β m height k ks

/--
relative strict record start `a` より後で最初に start rank を strict に下回る cut は、
元 anchor から見ても strict record cut になる。
-/
private theorem firstLower_isRecordCutAfter
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor a k : ℕ}
    (haRecord : IsRelativeRecordStart β m height anchor a)
    (hak : a < k)
    (hkm : k < m)
    (hLower :
      chordRank β m height k < chordRank β m height a)
    (hFirst :
      ∀ j : ℕ,
        a < j →
        j < k →
          chordRank β m height a ≤ chordRank β m height j) :
    IsRecordCutAfter β m height anchor k := by
  apply
    (isRecordCutAfter_iff
      (β := β) (m := m) (height := height)
      (anchor := anchor) (k := k)).2
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
current start `a` より前に未列挙の strict lower cut が無ければ、
次の canonical cut までの rank は start rank 以上。

`Nat.find` は theorem 内の有限存在証明にだけ使い、canonical data の定義には入れない。
-/
private theorem rank_le_before_next_recordCut
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor a endIndex : ℕ}
    {cuts : List ℕ}
    (haRecord : IsRelativeRecordStart β m height anchor a)
    (hComplete :
      ∀ q : ℕ,
        IsRecordCutAfter β m height anchor q →
        a < q →
        q ∈ cuts)
    (hNoCutBefore :
      ∀ q ∈ cuts,
        ¬ (a < q ∧ q < endIndex))
    {j : ℕ}
    (haj : a < j)
    (hjEnd : j < endIndex)
    (hEndLeM : endIndex ≤ m) :
    chordRank β m height a ≤ chordRank β m height j := by
  by_contra hNot
  have hjLower :
      chordRank β m height j < chordRank β m height a :=
    lt_of_not_ge hNot
  have hExists :
      ∃ q : ℕ,
        a < q ∧
        q < endIndex ∧
        chordRank β m height q < chordRank β m height a :=
    ⟨j, haj, hjEnd, hjLower⟩
  let q : ℕ := Nat.find hExists
  have hq := Nat.find_spec hExists
  have hqFirst :
      ∀ t : ℕ,
        a < t →
        t < q →
          chordRank β m height a ≤ chordRank β m height t := by
    intro t hat htq
    by_contra hNotLe
    have htLower :
        chordRank β m height t < chordRank β m height a :=
      lt_of_not_ge hNotLe
    have htCandidate :
        a < t ∧
        t < endIndex ∧
        chordRank β m height t < chordRank β m height a :=
      ⟨hat, lt_trans htq hq.2.1, htLower⟩
    have hqLe : q ≤ t := by
      dsimp [q]
      exact Nat.find_min' hExists htCandidate
    omega
  have hqm : q < m :=
    lt_of_lt_of_le hq.2.1 hEndLeM
  have hRecordQ :
      IsRecordCutAfter β m height anchor q :=
    firstLower_isRecordCutAfter
      haRecord hq.1 hqm hq.2.2 hqFirst
  have hMem := hComplete q hRecordQ hq.1
  exact hNoCutBefore q hMem ⟨hq.1, hq.2.1⟩

private theorem canonicalWeakBlocksFrom_of_cuts
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor : ℕ}
    (U : HasUnitCarry β)
    (recordCut_isRoof :
      ∀ {k : ℕ},
        IsRecordCutAfter β m height anchor k →
          IsProperRoofCut β m height k) :
    ∀ (a : ℕ) (cuts : List ℕ),
      IsProperRoofCut β m height a →
      IsRelativeRecordStart β m height anchor a →
      StrictCutChainFrom m a cuts →
      (∀ k ∈ cuts, IsRecordCutAfter β m height anchor k) →
      (∀ k : ℕ,
        IsRecordCutAfter β m height anchor k →
        a < k →
        k ∈ cuts) →
      CanonicalWeakBlocksFrom β m height a cuts
  | a, [], hRoof, hRelative, hChain, _hRecords, hComplete => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom]
      refine ⟨Nat.sub_pos_of_lt hChain, ?_, ?_⟩
      · intro j hjPos hjLt
        have haj : a < a + j := by omega
        have hjm : a + j < m := by omega
        exact rank_le_before_next_recordCut
          hRelative
          hComplete
          (by simp)
          haj
          hjm
          (Nat.le_refl m)
      · have hIndex : a + (m - a) = m :=
          Nat.add_sub_of_le (Nat.le_of_lt hChain)
        rw [hIndex, chordRank_terminal_eq_zero]
        exact chordRank_pos_of_properRoofCut U hRoof
  | a, k :: ks, hRoof, hRelative, hChain,
      hRecords, hComplete => by
      simp only [StrictCutChainFrom] at hChain
      have hak : a < k := hChain.1
      have hkm : k < m := hChain.2.1
      have hTailChain := hChain.2.2
      have hRecordK :
          IsRecordCutAfter β m height anchor k :=
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
              chordRank β m height a ≤
                chordRank β m height (a + j) := by
        intro j hjPos hjLt
        have haj : a < a + j := by omega
        have hjk : a + j < k := by omega
        exact rank_le_before_next_recordCut
          hRelative
          hComplete
          hNoCutBefore
          haj
          hjk
          (Nat.le_of_lt hkm)
      have hRK :=
        (isRecordCutAfter_iff
          (β := β) (m := m) (height := height)
          (anchor := anchor) (k := k)).1 hRecordK
      have hEndDrop :
          chordRank β m height k < chordRank β m height a :=
        hRK.2.2 a hRelative.1 hak
      have hIndex : a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hak)
      have hWeakBlock :
          IsWeakRecordBlock β m height a (k - a) := by
        refine ⟨Nat.sub_pos_of_lt hak, hWeakInterior, ?_⟩
        simpa [hIndex] using hEndDrop
      have hRoofK : IsProperRoofCut β m height k :=
        recordCut_isRoof hRecordK
      have hRelativeK :
          IsRelativeRecordStart β m height anchor k :=
        isRelativeRecordStart_of_recordCut hRecordK
      have hTailRecords :
          ∀ q ∈ ks,
            IsRecordCutAfter β m height anchor q := by
        intro q hq
        exact hRecords q (by simp [hq])
      have hTailComplete :
          ∀ q : ℕ,
            IsRecordCutAfter β m height anchor q →
            k < q →
            q ∈ ks := by
        intro q hqRecord hkq
        have hMem :=
          hComplete q hqRecord (lt_trans hak hkq)
        simp only [List.mem_cons] at hMem
        rcases hMem with hEq | hTail
        · subst q
          omega
        · exact hTail
      refine ⟨hWeakBlock, hRoofK, ?_⟩
      exact canonicalWeakBlocksFrom_of_cuts
        U recordCut_isRoof
        k ks
        hRoofK
        hRelativeK
        hTailChain
        hTailRecords
        hTailComplete

/--
一般 admissible roof path について、deterministic canonical record cuts が切り出す区間は
自動的に weak record excursions になる。

`NoRecordLevelTie` や primitive 性は仮定しない。
-/
theorem canonicalWeakBlocksFrom_canonicalRecordCuts
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    CanonicalWeakBlocksFrom
      β m height canonicalAnchor (canonicalRecordCuts β m height) := by
  have hRoof : IsProperRoofCut β m height canonicalAnchor :=
    canonicalAnchor_isProperRoofCut U A hβ1 hm
  have hRelative :
      IsRelativeRecordStart β m height canonicalAnchor canonicalAnchor :=
    isRelativeRecordStart_anchor hRoof.2.1
  have hChain :
      StrictCutChainFrom m canonicalAnchor
        (canonicalRecordCuts β m height) := by
    unfold canonicalRecordCuts
    exact
      recordCutsAfter_strictCutChain
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor)
        hRoof.2.1
  have hRecords :
      ∀ k ∈ canonicalRecordCuts β m height,
        IsRecordCutAfter β m height canonicalAnchor k := by
    intro k hk
    unfold canonicalRecordCuts at hk
    exact
      ((mem_recordCutsAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor) (k := k)).1 hk).2
  have hComplete :
      ∀ k : ℕ,
        IsRecordCutAfter β m height canonicalAnchor k →
        canonicalAnchor < k →
        k ∈ canonicalRecordCuts β m height := by
    intro k hRecord _hkAfter
    unfold canonicalRecordCuts
    exact
      (mem_recordCutsAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor) (k := k)).2
        ⟨hRecord.2.1, hRecord⟩
  exact canonicalWeakBlocksFrom_of_cuts
    U
    (fun {k} R => canonicalRecordCut_isProperRoofCut U A hβ1 hm R)
    canonicalAnchor
    (canonicalRecordCuts β m height)
    hRoof hRelative hChain hRecords hComplete

/--
strict cut chain を隣接差へ変換すると、その length 列は `RoofBlockChainFrom` を成す。

この定理は rank を使わず、start 以後の全 proper cut が roof 上にあることだけを使う。
-/
theorem roofBlockChainFrom_blockLengths_of_cuts
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (cuts : List ℕ),
      StrictCutChainFrom m a cuts →
      (∀ k ∈ cuts, IsProperRoofCut β m height k) →
      RoofBlockChainFrom β m height a
        (blockLengthsFromCuts m a cuts)
  | a, [], hChain, _hRoofs => by
      simp only [StrictCutChainFrom] at hChain
      simp only [blockLengthsFromCuts, RoofBlockChainFrom]
      exact
        ⟨Nat.sub_pos_of_lt hChain,
          Nat.add_sub_of_le (Nat.le_of_lt hChain)⟩
  | a, k :: ks, hChain, hRoofs => by
      simp only [StrictCutChainFrom] at hChain
      have hak : a < k := hChain.1
      have hRoofK : IsProperRoofCut β m height k :=
        hRoofs k (by simp)
      have hTailRoofs :
          ∀ q ∈ ks, IsProperRoofCut β m height q := by
        intro q hq
        exact hRoofs q (by simp [hq])
      have hTail :=
        roofBlockChainFrom_blockLengths_of_cuts
          k ks hChain.2.2 hTailRoofs
      let tailLengths : List ℕ :=
        blockLengthsFromCuts m k ks
      have hTailNe : tailLengths ≠ [] := by
        dsimp [tailLengths]
        exact blockLengthsFromCuts_ne_nil m k ks
      change
        RoofBlockChainFrom β m height a
          ((k - a) :: tailLengths)
      change
        RoofBlockChainFrom β m height k tailLengths
        at hTail
      cases hTailEq : tailLengths with
      | nil =>
          exact False.elim (hTailNe hTailEq)
      | cons s ss =>
          simp only [RoofBlockChainFrom]
          have hIndex : a + (k - a) = k :=
            Nat.add_sub_of_le (Nat.le_of_lt hak)
          refine ⟨Nat.sub_pos_of_lt hak, ?_, ?_⟩
          · rw [hIndex]
            exact hRoofK
          · rw [hIndex]
            rw [hTailEq] at hTail
            exact hTail

/--
`canonicalRecordLengths` は、標準 anchor `1` から terminal `m` までを結ぶ
実際の roof block chain である。

これが第5段階の最終 bridge。第6段階ではこの theorem をそのまま
`Experimental2.RecordCarryLaw` の chain 仮定として使える。
-/
theorem canonicalRecordLengths_roofBlockChain
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    RoofBlockChainFrom β m height canonicalAnchor
      (canonicalRecordLengths β m height) := by
  have hAnchor : canonicalAnchor < m := by
    simpa [canonicalAnchor] using hm
  have hChain :
      StrictCutChainFrom m canonicalAnchor
        (recordCutsAfter β m height canonicalAnchor) :=
    recordCutsAfter_strictCutChain
      (β := β) (m := m) (height := height)
      (anchor := canonicalAnchor) hAnchor
  have hRoofs :
      ∀ k ∈ recordCutsAfter β m height canonicalAnchor,
        IsProperRoofCut β m height k := by
    intro k hk
    have hSpec :=
      (mem_recordCutsAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor) (k := k)).1 hk
    exact canonicalRecordCut_isProperRoofCut U A hβ1 hm hSpec.2
  unfold canonicalRecordLengths recordLengthsAfter
  exact roofBlockChainFrom_blockLengths_of_cuts
    canonicalAnchor
    (recordCutsAfter β m height canonicalAnchor)
    hChain hRoofs

end GenericRecordFerrers
end Experimental2
end Collatz3
