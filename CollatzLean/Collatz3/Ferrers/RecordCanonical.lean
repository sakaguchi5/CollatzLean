import CollatzLean.Collatz3.Ferrers.RecordPartition
import CollatzLean.Collatz3.Critical.RecordSkeleton
import CollatzLean.Collatz3.Critical.BestUpperWidth
import CollatzLean.Collatz3.Critical.RecordRankArithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3: RecordView から canonical critical record skeleton へ

このファイルは weak `RecordView` と `CriticalRecordSkeleton` の間の bridge を扱う。

設計上の要点は次の通り。

* `initialRecordCuts` と `canonicalRecordLengths` は `RecordPartition` で有限計算する。
* exact な障害は「全 rank が相異なること」ではなく、weak running minimum が
  同じ level に戻る `record-level tie` である。
* `NoRecordLevelTie` は block length を選ぶためには使わない。
  profile から既に計算された canonical partition が genuine strict skeleton であることを
  証明するためだけに使う。
* `IsPrimitiveWidth` は exact 条件ではなく、record-level tie を排除する
  算術的な十分条件として使う。
* `CriticalRecordSkeleton` が同じ profile 上に二つ存在すれば、その block length 列は一意。

従来の theorem-level choice による data constructor は置かない。
真の `RecordFerrers` はここではまだ定義しない。
-/

namespace Collatz3
namespace Ferrers

open Critical

/--
anchor より後の cut `k` が、それ以前の区間に対する weak running minimum。
strict record cut との違いは `≤` を使うことだけである。
-/
def IsWeakRecordCutAfter
    {m : ℕ}
    (h : Profile m)
    (anchor k : ℕ) : Prop :=
  anchor < k ∧
    k < m ∧
    ∀ j : Fin k,
      anchor ≤ j.1 →
        profileChordRank h k ≤ profileChordRank h j.1

/-- weak record cut の通常の自然数区間による仕様。 -/
theorem isWeakRecordCutAfter_iff
    {m : ℕ}
    {h : Profile m}
    {anchor k : ℕ} :
    IsWeakRecordCutAfter h anchor k ↔
      anchor < k ∧
      k < m ∧
      ∀ j : ℕ,
        anchor ≤ j →
        j < k →
          profileChordRank h k ≤ profileChordRank h j := by
  constructor
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj hjk
    exact H.2.2 ⟨j, hjk⟩ haj
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj
    exact H.2.2 j.1 haj j.2

/--
weak running minimum が現れたなら必ず strict running minimum である。
これが critical record skeleton の exact な `record-level tie` 排除条件。
-/
def NoRecordLevelTie
    {m : ℕ}
    (h : Profile m)
    (anchor : ℕ) : Prop :=
  ∀ k : ℕ,
    IsWeakRecordCutAfter h anchor k →
      IsRecordCutAfter h anchor k

/-- primitive width では proper cut の chord rank は injective。 -/
theorem profileChordRank_injective_of_primitive
    {m : ℕ}
    {h : Profile m}
    (P : IsPrimitiveWidth m)
    {a b : ℕ}
    (ha : a < m)
    (hb : b < m)
    (hEq : profileChordRank h a = profileChordRank h b) :
    a = b := by
  have hm : 0 < m := by omega
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hCast :=
    congrArg (fun z : ℤ => (z : ZMod m)) hEq
  have hMul :
      (((criticalTwoDepth m * a : ℕ) : ZMod m)) =
        (((criticalTwoDepth m * b : ℕ) : ZMod m)) := by
    simpa [profileChordRank, Nat.cast_mul] using hCast
  let U : (ZMod m)ˣ :=
    ZMod.unitOfCoprime (criticalTwoDepth m)
      (by simpa [IsPrimitiveWidth] using P)
  have hHU :
      ((criticalTwoDepth m : ℕ) : ZMod m) = (↑U : ZMod m) := by
    simp [U]
  have hMul' :
      (↑U : ZMod m) * ((a : ℕ) : ZMod m) =
        (↑U : ZMod m) * ((b : ℕ) : ZMod m) := by
    have hMul0 := hMul
    simp only [Nat.cast_mul] at hMul0
    rw [hHU] at hMul0
    exact hMul0
  have hCancel :=
    congrArg
      (fun z : ZMod m => (↑(U⁻¹) : ZMod m) * z)
      hMul'
  have hAB :
      ((a : ℕ) : ZMod m) = ((b : ℕ) : ZMod m) := by
    simpa [← mul_assoc] using hCancel
  have hVal := congrArg ZMod.val hAB
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] using hVal

/-- primitive width は record-level tie を排除する十分条件。 -/
theorem noRecordLevelTie_of_primitive
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    (P : IsPrimitiveWidth m) :
    NoRecordLevelTie h anchor := by
  intro k W
  apply (isRecordCutAfter_iff).2
  have hW := (isWeakRecordCutAfter_iff).1 W
  refine ⟨hW.1, hW.2.1, ?_⟩
  intro j haj hjk
  have hLe := hW.2.2 j haj hjk
  have hjm : j < m := lt_trans hjk hW.2.1
  have hNe : profileChordRank h k ≠ profileChordRank h j := by
    intro hEq
    have hkj :=
      profileChordRank_injective_of_primitive
        (h := h) P hW.2.1 hjm hEq
    omega
  exact lt_of_le_of_ne hLe hNe

/-- proper cut の profile height は Beatty roof 以下。 -/
theorem profileHeight_le_beatty
    {m : ℕ}
    {h : Profile m}
    {k : ℕ}
    (hk : k < m) :
    profileHeight h k ≤ beattyIndex k := by
  rw [profileHeight_of_lt h hk]
  unfold checkpoint
  exact Nat.sub_le _ _

/--
proper positive cut が roof 上にいなければ、その chord rank は width `m` より大きい。
-/
theorem width_lt_profileChordRank_of_not_roof
    {m : ℕ}
    {h : Profile m}
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < m)
    (hNotRoof : ¬ IsRoofCut h k) :
    (m : ℤ) < profileChordRank h k := by
  have hm : 0 < m := lt_trans hkPos hkLt
  have hLe := profileHeight_le_beatty (h := h) hkLt
  have hNe : profileHeight h k ≠ beattyIndex k := by
    intro hEq
    exact hNotRoof ⟨hkPos, hkLt, hEq⟩
  have hLt : profileHeight h k < beattyIndex k :=
    lt_of_le_of_ne hLe hNe
  have hChord :=
    beattyIndex_below_criticalChord
      (m := m) (r := k) hm hkPos
  have hScaled :
      m * profileHeight h k + m <
        criticalTwoDepth m * k := by
    calc
      m * profileHeight h k + m
          = m * (profileHeight h k + 1) := by ring
      _ ≤ m * beattyIndex k :=
        Nat.mul_le_mul_left m (Nat.succ_le_of_lt hLt)
      _ < criticalTwoDepth m * k := hChord
  have hScaledZ :
      (m : ℤ) * (profileHeight h k : ℤ) + (m : ℤ) <
        (criticalTwoDepth m : ℤ) * (k : ℤ) := by
    exact_mod_cast hScaled
  have hCut : cutDepth h k = profileHeight h k := by
    simp [cutDepth_of_lt, profileHeight_of_lt, hkLt]
  unfold profileChordRank
  rw [hCut]
  linarith

/--
canonical anchor `1` より後の strict record cut は自動的に critical roof cut。
primitive 性は不要である。
-/
theorem isRoofCut_of_isRecordCutAfter
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {k : ℕ}
    (R : IsRecordCutAfter h initialRoofAnchor k) :
    IsRoofCut h k := by
  have hR := (isRecordCutAfter_iff).1 R
  have hkPos : 0 < k := by
    simp [initialRoofAnchor] at hR
    omega
  have hm : 2 < m := by
    simp [initialRoofAnchor] at hR
    omega
  have hRankLtAnchor :
      profileChordRank h k <
        profileChordRank h initialRoofAnchor :=
    hR.2.2 initialRoofAnchor (le_rfl) hR.1
  by_contra hNot
  have hAbove :=
    width_lt_profileChordRank_of_not_roof
      hkPos hR.2.1 hNot
  have hAnchor :=
    profileChordRank_initialRoofAnchor_lt_width A hm
  linarith

/-- anchor から見て start `a` が relative strict record である。 -/
def IsRelativeRecordStart
    {m : ℕ}
    (h : Profile m)
    (anchor a : ℕ) : Prop :=
  anchor ≤ a ∧
    a < m ∧
    ∀ j : ℕ,
      anchor ≤ j →
      j < a →
        profileChordRank h a < profileChordRank h j

/-- anchor 自身は relative record start。 -/
theorem isRelativeRecordStart_anchor
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    (ha : anchor < m) :
    IsRelativeRecordStart h anchor anchor := by
  refine ⟨le_rfl, ha, ?_⟩
  intro j haj hja
  omega

/-- strict record cut は relative record start でもある。 -/
theorem isRelativeRecordStart_of_recordCut
    {m : ℕ}
    {h : Profile m}
    {anchor k : ℕ}
    (R : IsRecordCutAfter h anchor k) :
    IsRelativeRecordStart h anchor k := by
  have hR := (isRecordCutAfter_iff).1 R
  exact ⟨Nat.le_of_lt hR.1, hR.2.1, hR.2.2⟩

/--
relative record start `a` の後で、

* endpoint `k` の rank が start rank 以下
* `a < t < k` の内部では start rank 以上

なら、`k` は元の anchor から見た weak record cut である。
-/
private theorem weakRecordCutAfter_of_relativeStart
    {m : ℕ}
    {h : Profile m}
    {anchor a k : ℕ}
    (haRecord : IsRelativeRecordStart h anchor a)
    (hak : a < k)
    (hkm : k < m)
    (hEndLe :
      profileChordRank h k ≤ profileChordRank h a)
    (hInteriorLe :
      ∀ t : ℕ,
        a < t →
        t < k →
        profileChordRank h a ≤ profileChordRank h t) :
    IsWeakRecordCutAfter h anchor k := by
  apply (isWeakRecordCutAfter_iff).2
  refine ⟨lt_of_le_of_lt haRecord.1 hak, hkm, ?_⟩
  intro t hat htk
  by_cases hta : t < a
  · have hPrev :
        profileChordRank h a < profileChordRank h t :=
      haRecord.2.2 t hat hta
    exact le_of_lt (lt_of_le_of_lt hEndLe hPrev)
  · have hatLe : a ≤ t :=
      Nat.le_of_not_gt hta
    by_cases htaEq : t = a
    · subst t
      exact hEndLe
    · have hatStrict : a < t :=
        lt_of_le_of_ne hatLe (Ne.symm htaEq)
      have htLe :
          profileChordRank h a ≤ profileChordRank h t :=
        hInteriorLe t hatStrict htk
      exact le_trans hEndLe htLe

/--
relative record start `a` より後の `j` について、

* `rank a ≤ rank j`
* `a < t < j` では `rank a ≤ rank t`

が成り立つなら、record-level tie が無い限り
実際には `rank a < rank j` である。
-/
private theorem strictRankAbove_of_noRecordLevelTie
    {m : ℕ}
    {h : Profile m}
    {anchor a j : ℕ}
    (T : NoRecordLevelTie h anchor)
    (haRecord : IsRelativeRecordStart h anchor a)
    (haj : a < j)
    (hjm : j < m)
    (hLe :
      profileChordRank h a ≤ profileChordRank h j)
    (hInteriorLe :
      ∀ t : ℕ,
        a < t →
        t < j →
        profileChordRank h a ≤ profileChordRank h t) :
    profileChordRank h a < profileChordRank h j := by
  apply lt_of_le_of_ne hLe
  intro hEq
  have hWeakJ :
      IsWeakRecordCutAfter h anchor j :=
    weakRecordCutAfter_of_relativeStart
      haRecord haj hjm
      (le_of_eq hEq.symm)
      hInteriorLe
  have hRecordJ :
      IsRecordCutAfter h anchor j :=
    T j hWeakJ
  have hRJ :=
    (isRecordCutAfter_iff).1 hRecordJ
  have hDrop :
      profileChordRank h j <
        profileChordRank h a :=
    hRJ.2.2 a haRecord.1 haj
  exact (ne_of_lt hDrop) hEq.symm


/-! ## deterministic canonical cuts の weak geometry -/

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

ここでの `Nat.find` は theorem 内の有限存在証明にだけ現れ、
計算データを構成する定義には現れない。
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
  have hqm : q < m :=
    lt_of_lt_of_le hq.2.1 hEndLeM
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
        have haj : a < a + j := by omega
        have hjm : a + j < m := by omega
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
      have hak : a < k := hChain.1
      have hkm : k < m := hChain.2.1
      have hTailChain := hChain.2.2
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
  have hChain :=
    initialRecordCuts_strictCutChain (h := h) hm
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
    exact
      (mem_recordCutsAfter_iff).2
        ⟨hRecord.2.1, hRecord⟩
  exact canonicalWeakBlocksFrom_of_cuts
    (isRoofCut_of_isRecordCutAfter A)
    initialRoofAnchor
    (initialRecordCuts h)
    hRoof hRelative hChain hRecords hComplete

/-! ## tie-free canonical strict geometry -/

/-- canonical partition の各区間を genuine strict record block として読む。 -/
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
weak block の内部で等号が起きれば、その位置は weak record cut になる。
`NoRecordLevelTie` はそれを strict record cut に昇格させるため、
次の canonical cut より前には等号が残れない。
-/
private theorem isRecordBlock_of_weak_of_noRecordLevelTie
    {m : ℕ}
    {h : Profile m}
    {anchor a r : ℕ}
    (T : NoRecordLevelTie h anchor)
    (haRecord : IsRelativeRecordStart h anchor a)
    (hEnd : a + r ≤ m)
    (W : IsWeakRecordBlock h a r) :
    Combinatorics.IsRecordBlock (profileChordRank h) a r := by
  refine ⟨W.length_pos, ?_, W.end_drop⟩
  intro j hjPos hjLt
  have haj : a < a + j := by omega
  have hjm : a + j < m := by omega
  have hLe :
      profileChordRank h a ≤
        profileChordRank h (a + j) :=
    W.interior hjPos hjLt
  have hInteriorLe :
      ∀ t : ℕ,
        a < t →
        t < a + j →
          profileChordRank h a ≤ profileChordRank h t := by
    intro t hat htj
    have htPos : 0 < t - a := by omega
    have htLt : t - a < r := by omega
    have hInt :=
      W.interior (j := t - a) htPos htLt
    have hIndex : a + (t - a) = t := by omega
    rw [hIndex] at hInt
    exact hInt
  exact strictRankAbove_of_noRecordLevelTie
    T haRecord haj hjm hLe hInteriorLe

private theorem canonicalStrictBlocksFrom_of_weak_of_noRecordLevelTie
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    (T : NoRecordLevelTie h anchor) :
    ∀ (a : ℕ) (cuts : List ℕ),
      IsRelativeRecordStart h anchor a →
      StrictCutChainFrom m a cuts →
      (∀ k ∈ cuts, IsRecordCutAfter h anchor k) →
      CanonicalWeakBlocksFrom h a cuts →
      CanonicalStrictBlocksFrom h a cuts
  | a, [], hRelative, hChain, _hRecords, hWeak => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom] at hWeak
      simp only [CanonicalStrictBlocksFrom]
      have hEnd : a + (m - a) ≤ m := by omega
      exact
        isRecordBlock_of_weak_of_noRecordLevelTie
          T hRelative hEnd hWeak
  | a, k :: ks, hRelative, hChain, hRecords, hWeak => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom] at hWeak
      simp only [CanonicalStrictBlocksFrom]
      have hRecordK :
          IsRecordCutAfter h anchor k :=
        hRecords k (by simp)
      have hEnd : a + (k - a) ≤ m := by omega
      have hStrict :
          Combinatorics.IsRecordBlock
            (profileChordRank h) a (k - a) :=
        isRecordBlock_of_weak_of_noRecordLevelTie
          T hRelative hEnd hWeak.1
      have hRelativeK :
          IsRelativeRecordStart h anchor k :=
        isRelativeRecordStart_of_recordCut hRecordK
      have hTailRecords :
          ∀ q ∈ ks,
            IsRecordCutAfter h anchor q := by
        intro q hq
        exact hRecords q (by simp [hq])
      refine ⟨hStrict, hWeak.2.1, ?_⟩
      exact canonicalStrictBlocksFrom_of_weak_of_noRecordLevelTie
        T k ks
        hRelativeK
        hChain.2.2
        hTailRecords
        hWeak.2.2

/--
`NoRecordLevelTie` があれば、profile から有限計算した deterministic partition が
そのまま genuine strict canonical blocks になる。
-/
theorem canonicalStrictBlocksFrom_of_noRecordLevelTie
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m)
    (T : NoRecordLevelTie h initialRoofAnchor) :
    CanonicalStrictBlocksFrom
      h initialRoofAnchor (initialRecordCuts h) := by
  have hRelative :
      IsRelativeRecordStart h initialRoofAnchor initialRoofAnchor :=
    isRelativeRecordStart_anchor
      (by simpa [initialRoofAnchor] using hm)
  have hChain :=
    initialRecordCuts_strictCutChain (h := h) hm
  have hRecords :
      ∀ k ∈ initialRecordCuts h,
        IsRecordCutAfter h initialRoofAnchor k := by
    intro k hk
    change k ∈ recordCutsAfter h initialRoofAnchor at hk
    exact ((mem_recordCutsAfter_iff).1 hk).2
  exact
    canonicalStrictBlocksFrom_of_weak_of_noRecordLevelTie
      T initialRoofAnchor (initialRecordCuts h)
      hRelative
      hChain
      hRecords
      (canonicalWeakBlocksFrom_initialRecordCuts A hm)

/--
strict cut chain を隣接差へ変換すると、
`CanonicalStrictBlocksFrom` は既存の roof-record length realization を与える。

ここでは一方向だけを使う。exact な逆向き bridge は後段の `RecordCarryBridge` に残す。
-/
theorem realizesBlocksFrom_blockLengths_of_canonicalStrictBlocks
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (cuts : List ℕ),
      StrictCutChainFrom m a cuts →
      CanonicalStrictBlocksFrom h a cuts →
      RoofRecordSkeleton.RealizesBlocksFrom
        h a (blockLengthsFromCuts m a cuts)
  | a, [], hChain, hStrict => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalStrictBlocksFrom] at hStrict
      simp only [
        blockLengthsFromCuts,
        RoofRecordSkeleton.RealizesBlocksFrom
      ]
      exact
        ⟨hStrict,
          Nat.add_sub_of_le (Nat.le_of_lt hChain)⟩
  | a, k :: ks, hChain, hStrict => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalStrictBlocksFrom] at hStrict
      have hak : a < k := hChain.1
      have hIndex :
          a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hak)
      let tailLengths : List ℕ :=
        blockLengthsFromCuts m k ks
      have hTailNe : tailLengths ≠ [] := by
        dsimp [tailLengths]
        exact blockLengthsFromCuts_ne_nil m k ks
      have hTail :=
        realizesBlocksFrom_blockLengths_of_canonicalStrictBlocks
          k ks hChain.2.2 hStrict.2.2
      change
        RoofRecordSkeleton.RealizesBlocksFrom
          h k tailLengths
        at hTail
      cases hTailEq : tailLengths with
      | nil =>
          exact False.elim (hTailNe hTailEq)
      | cons s ss =>
          rw [hTailEq] at hTail
          simp only [blockLengthsFromCuts]
          change
            RoofRecordSkeleton.RealizesBlocksFrom
              h a ((k - a) :: tailLengths)
          rw [hTailEq]
          simp only [RoofRecordSkeleton.RealizesBlocksFrom]
          rw [hIndex]
          exact ⟨hStrict.1, hStrict.2.1, hTail⟩

/--
tie-free admissible profile では、有限計算された `canonicalRecordLengths` が
roof-record realization を実現する。
-/
theorem realizesCanonicalRecordLengths_of_noRecordLevelTie
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m)
    (T : NoRecordLevelTie h initialRoofAnchor) :
    RoofRecordSkeleton.RealizesBlocksFrom
      h initialRoofAnchor (canonicalRecordLengths h) := by
  unfold canonicalRecordLengths
  exact
    realizesBlocksFrom_blockLengths_of_canonicalStrictBlocks
      initialRoofAnchor
      (initialRecordCuts h)
      (initialRecordCuts_strictCutChain (h := h) hm)
      (canonicalStrictBlocksFrom_of_noRecordLevelTie A hm T)


/-- roof-compatible realization の全 block length は正。 -/
theorem realizesBlocksFrom_lengths_pos
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (rs : List ℕ),
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
        ∀ r ∈ rs, 0 < r
  | _a, [], hFalse => by
      have h : False := by
        simp [RoofRecordSkeleton.RealizesBlocksFrom] at hFalse
      exact h.elim
  | a, [r], hOne => by
      intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      exact hOne.1.length_pos
  | a, r :: s :: rs, hMany => by
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hEq | hTail
      · subst q
        exact hMany.1.length_pos
      · exact realizesBlocksFrom_lengths_pos
          (a + r) (s :: rs) hMany.2.2 q
          (by
            simpa only [List.mem_cons] using hTail)

/--
`NoRecordLevelTie` を満たす admissible profile から canonical critical record skeleton を作る。

保存する block length は profile から有限計算された `canonicalRecordLengths` そのもの。
`T` は data selection には使わず、その deterministic partition が genuine strict
roof-record skeleton を実現することの証明にだけ使う。
-/
def criticalRecordSkeletonOfProfile
    {m : ℕ}
    (H : AdmissibleProfile m)
    (hm : 1 < m)
    (T : NoRecordLevelTie H.1 initialRoofAnchor) :
    CriticalRecordSkeleton m := by
  let hRoof :=
    initialRoofAnchor_isRoofCut H.2 hm
  let hRealizes :
      RoofRecordSkeleton.RealizesBlocksFrom
        H.1 initialRoofAnchor (canonicalRecordLengths H.1) :=
    realizesCanonicalRecordLengths_of_noRecordLevelTie
      H.2 hm T
  let S : Combinatorics.RecordSkeleton :=
    { lengths := canonicalRecordLengths H.1
      positive :=
        canonicalRecordLengths_pos
          (h := H.1) hm }
  exact {
    profile := H
    skeleton := S
    realizes := ⟨hRoof, hRealizes⟩
  }

namespace RecordView

/-- weak RecordView を、tie-free 仮定の下で critical record skeleton へ持ち上げる。 -/
def toCriticalRecordSkeleton
    {m : ℕ}
    (R : RecordView m)
    (hm : 1 < m)
    (T : NoRecordLevelTie R.profile.1 initialRoofAnchor) :
    CriticalRecordSkeleton m :=
  criticalRecordSkeletonOfProfile R.profile hm T

/-- primitive width は canonical skeleton を構成する十分条件。 -/
def toCriticalRecordSkeletonOfPrimitive
    {m : ℕ}
    (R : RecordView m)
    (hm : 1 < m)
    (P : IsPrimitiveWidth m) :
    CriticalRecordSkeleton m :=
  R.toCriticalRecordSkeleton hm (noRecordLevelTie_of_primitive P)

@[simp] theorem toCriticalRecordSkeleton_profile
    {m : ℕ}
    (R : RecordView m)
    (hm : 1 < m)
    (T : NoRecordLevelTie R.profile.1 initialRoofAnchor) :
    (R.toCriticalRecordSkeleton hm T).profile = R.profile :=
  rfl

end RecordView

/-- 同じ start から始まる二つの strict record block は長さが一致する。 -/
theorem recordBlock_length_eq_of_same_start
    {rank : ℕ → ℤ}
    {a r s : ℕ}
    (R : Combinatorics.IsRecordBlock rank a r)
    (S : Combinatorics.IsRecordBlock rank a s) :
    r = s := by
  by_cases hrs : r < s
  · have hInt := S.interior R.length_pos hrs
    have hEnd := R.end_drop
    omega
  by_cases hsr : s < r
  · have hInt := R.interior S.length_pos hsr
    have hEnd := S.end_drop
    omega
  omega

/-- block length 列から terminal を除いた proper endpoint 列を読む。 -/
def properEndpointsFrom : ℕ → List ℕ → List ℕ
  | _a, [] => []
  | _a, [_r] => []
  | a, r :: s :: rs =>
      (a + r) :: properEndpointsFrom (a + r) (s :: rs)

/-- relative record start から始まる一 block の endpoint は relative strict record。 -/
theorem isRecordCutAfter_of_recordBlock
    {m : ℕ}
    {h : Profile m}
    {anchor a r : ℕ}
    (haRecord : IsRelativeRecordStart h anchor a)
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hEndLt : a + r < m) :
    IsRecordCutAfter h anchor (a + r) := by
  apply (isRecordCutAfter_iff).2
  have hAnchorLe : anchor ≤ a :=
    haRecord.1
  have hrPos : 0 < r :=
    B.length_pos
  have haEnd : a < a + r :=
    Nat.lt_add_of_pos_right hrPos
  have hAnchorEnd : anchor < a + r :=
    lt_of_le_of_lt hAnchorLe haEnd
  refine ⟨hAnchorEnd, hEndLt, ?_⟩
  intro j haj hjEnd
  have hDrop := B.end_drop
  by_cases hja : j < a
  · have hPrev := haRecord.2.2 j haj hja
    omega
  by_cases hEq : j = a
  · subst j
    exact hDrop
  have hajStrict : a < j := by omega
  let t := j - a
  have htPos : 0 < t := by
    dsimp [t]
    omega
  have htLt : t < r := by
    dsimp [t]
    omega
  have hInt := B.interior htPos htLt
  have hIndex : a + t = j := by
    dsimp [t]
    omega
  rw [hIndex] at hInt
  omega

/-- realization の proper endpoint はすべて deterministic strict record cut。 -/
theorem properEndpointsFrom_are_recordCuts
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      IsRelativeRecordStart h anchor a →
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      ∀ k ∈ properEndpointsFrom a rs,
        IsRecordCutAfter h anchor k
  | _a, [], _ha, hFalse, _k, _hk => False.elim hFalse
  | _a, [_r], _ha, _hOne, k, hk => by
      simp [properEndpointsFrom] at hk
  | a, r :: s :: rs, ha, hMany, k, hk => by
      simp only [properEndpointsFrom, List.mem_cons] at hk
      have hFirst : IsRecordCutAfter h anchor (a + r) :=
        isRecordCutAfter_of_recordBlock ha hMany.1 hMany.2.1.lt_width
      rcases hk with hEq | hTail
      · subst k
        exact hFirst
      · have hNext := isRelativeRecordStart_of_recordCut hFirst
        exact properEndpointsFrom_are_recordCuts
          (a + r) (s :: rs) hNext hMany.2.2 k hTail

/--
realization の current start より後にある strict record cut は、必ず proper endpoint 列に現れる。
-/
theorem recordCut_mem_properEndpointsFrom
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ} :
    ∀ (a : ℕ) (rs : List ℕ) (k : ℕ),
      IsRelativeRecordStart h anchor a →
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      IsRecordCutAfter h anchor k →
      a < k →
      k ∈ properEndpointsFrom a rs
  | _a, [], _k, _ha, hFalse, _hRecord, _hak => False.elim hFalse
  | a, [r], k, ha, hOne, hRecord, hak => by
      have hR := (isRecordCutAfter_iff).1 hRecord
      have hTerm : a + r = m := hOne.2
      have hkLtEnd : k < a + r := by omega
      have tPos : 0 < k - a := by omega
      have tLt : k - a < r := by omega
      have hInt := hOne.1.interior tPos tLt
      have hIndex : a + (k - a) = k := by omega
      rw [hIndex] at hInt
      have hDrop := hR.2.2 a ha.1 hak
      omega
  | a, r :: s :: rs, k, ha, hMany, hRecord, hak => by
      have hFirst :
          IsRecordCutAfter h anchor (a + r) :=
        isRecordCutAfter_of_recordBlock
          ha hMany.1 hMany.2.1.lt_width
      by_cases hkEnd : k = a + r
      · subst k
        simp [properEndpointsFrom]
      by_cases hkBefore : k < a + r
      · have tPos : 0 < k - a := by
          omega
        have tLt : k - a < r := by
          omega
        have hInt :=
          hMany.1.interior tPos tLt
        have hIndex :
            a + (k - a) = k := by
          omega
        rw [hIndex] at hInt
        have hR :=
          (isRecordCutAfter_iff).1 hRecord
        have hDrop :=
          hR.2.2 a ha.1 hak
        omega
      · have hEndLtK :
            a + r < k := by
          omega
        have hNext :
            IsRelativeRecordStart h anchor (a + r) :=
          isRelativeRecordStart_of_recordCut hFirst
        have hTail :
            k ∈ properEndpointsFrom (a + r) (s :: rs) :=
          recordCut_mem_properEndpointsFrom
            (a + r) (s :: rs) k
            hNext hMany.2.2 hRecord hEndLtK
        simp only [properEndpointsFrom, List.mem_cons]
        exact Or.inr hTail

/-- critical record skeleton の terminal を除いた endpoint 列。 -/
def criticalRecordSkeletonEndpoints
    {m : ℕ}
    (R : CriticalRecordSkeleton m) : List ℕ :=
  properEndpointsFrom initialRoofAnchor R.skeleton.lengths

/--
critical record skeleton の proper endpoints は deterministic `initialRecordCuts` と exact に一致する。
ここでは list の membership として述べる。従って skeleton は weak RecordView の cut を飛ばさない。
-/
theorem mem_criticalRecordSkeletonEndpoints_iff
    {m : ℕ}
    (R : CriticalRecordSkeleton m)
    {k : ℕ} :
    k ∈ criticalRecordSkeletonEndpoints R ↔
      k ∈ initialRecordCuts R.profile.1 := by
  have hAnchorRel :
      IsRelativeRecordStart R.profile.1 initialRoofAnchor initialRoofAnchor :=
    isRelativeRecordStart_anchor R.realizes.anchor_roof.lt_width
  constructor
  · intro hk
    have hRecord := properEndpointsFrom_are_recordCuts
      initialRoofAnchor R.skeleton.lengths
      hAnchorRel R.realizes.2 k hk
    change k ∈ recordCutsAfter R.profile.1 initialRoofAnchor
    exact (mem_recordCutsAfter_iff).2 ⟨hRecord.2.1, hRecord⟩
  · intro hk
    change k ∈ recordCutsAfter R.profile.1 initialRoofAnchor at hk
    have hSpec := (mem_recordCutsAfter_iff).1 hk
    have hRecord := hSpec.2
    have hAfter := hRecord.1
    exact recordCut_mem_properEndpointsFrom
      initialRoofAnchor R.skeleton.lengths k
      hAnchorRel R.realizes.2 hRecord hAfter

/--
roof record realization が存在する区間では、current start より後の weak record は strict record になる。
-/
theorem weakRecordCut_is_strict_of_realization
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ} :
    ∀ (a : ℕ) (rs : List ℕ) (k : ℕ),
      IsRelativeRecordStart h anchor a →
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      IsWeakRecordCutAfter h anchor k →
      a < k →
      IsRecordCutAfter h anchor k
  | _a, [], _k, _ha, hFalse, _hWeak, _hak => False.elim hFalse
  | a, [r], k, ha, hOne, hWeak, hak => by
      have hW := (isWeakRecordCutAfter_iff).1 hWeak
      have hTerm := hOne.2
      have hkLtEnd : k < a + r := by omega
      have tPos : 0 < k - a := by omega
      have tLt : k - a < r := by omega
      have hInt := hOne.1.interior tPos tLt
      have hIndex : a + (k - a) = k := by omega
      rw [hIndex] at hInt
      have hWeakAtA := hW.2.2 a ha.1 hak
      omega
  | a, r :: s :: rs, k, ha, hMany, hWeak, hak => by
      let b := a + r
      have hFirst : IsRecordCutAfter h anchor b :=
        isRecordCutAfter_of_recordBlock ha hMany.1 hMany.2.1.lt_width
      by_cases hEq : k = b
      · subst k
        exact hFirst
      by_cases hBefore : k < b
      · have hW := (isWeakRecordCutAfter_iff).1 hWeak
        have tPos : 0 < k - a := by omega
        have tLt : k - a < r := by omega
        have hInt := hMany.1.interior tPos tLt
        have hIndex : a + (k - a) = k := by omega
        rw [hIndex] at hInt
        have hWeakAtA := hW.2.2 a ha.1 hak
        omega
      · have hAfter : b < k := by omega
        have hNext := isRelativeRecordStart_of_recordCut hFirst
        exact weakRecordCut_is_strict_of_realization
          b (s :: rs) k hNext hMany.2.2 hWeak hAfter

/-- critical record skeleton が存在すれば record-level tie は存在しない。 -/
theorem noRecordLevelTie_of_criticalRecordSkeleton
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    NoRecordLevelTie R.profile.1 initialRoofAnchor := by
  intro k hWeak
  have hAnchorRel :
      IsRelativeRecordStart R.profile.1 initialRoofAnchor initialRoofAnchor :=
    isRelativeRecordStart_anchor R.realizes.anchor_roof.lt_width
  have hkAfter := hWeak.1
  exact weakRecordCut_is_strict_of_realization
    initialRoofAnchor R.skeleton.lengths k
    hAnchorRel R.realizes.2 hWeak hkAfter

/--
幅 `m>1` の admissible profile では、`NoRecordLevelTie` は
critical record skeleton が存在するための exact 条件。
-/
theorem exists_criticalRecordSkeleton_iff_noRecordLevelTie
    {m : ℕ}
    (H : AdmissibleProfile m)
    (hm : 1 < m) :
    (∃ R : CriticalRecordSkeleton m, R.profile = H) ↔
      NoRecordLevelTie H.1 initialRoofAnchor := by
  constructor
  · rintro ⟨R, hProfile⟩
    cases hProfile
    exact noRecordLevelTie_of_criticalRecordSkeleton R
  · intro T
    exact ⟨criticalRecordSkeletonOfProfile H hm T, rfl⟩

/-- primitive width では任意の admissible profile に critical record skeleton が存在する。 -/
theorem exists_criticalRecordSkeleton_of_primitive
    {m : ℕ}
    (H : AdmissibleProfile m)
    (hm : 1 < m)
    (P : IsPrimitiveWidth m) :
    ∃ R : CriticalRecordSkeleton m, R.profile = H := by
  apply (exists_criticalRecordSkeleton_iff_noRecordLevelTie H hm).2
  exact noRecordLevelTie_of_primitive P

/-- 同じ profile・start 上の roof record block length 列は一意。 -/
theorem realizesBlocksFrom_unique
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (rs ts : List ℕ),
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      RoofRecordSkeleton.RealizesBlocksFrom h a ts →
      rs = ts
  | _a, [], _ts, hFalse, _ => False.elim hFalse
  | _a, _rs, [], _, hFalse => False.elim hFalse
  | a, [r], [s], hR, hS => by
      have hrs := recordBlock_length_eq_of_same_start hR.1 hS.1
      subst s
      rfl
  | a, [r], s :: t :: ts, hR, hS => by
      have hrs :=
        recordBlock_length_eq_of_same_start hR.1 hS.1
      subst s
      have hRoof :
          a + r < m :=
        hS.2.1.lt_width
      have hTerm :
          a + r = m :=
        hR.2
      exact False.elim
        ((Nat.ne_of_lt hRoof) hTerm)
  | a, r :: t :: rs, [s], hR, hS => by
      have hrs :=
        recordBlock_length_eq_of_same_start hR.1 hS.1
      subst s
      have hRoof :
          a + r < m :=
        hR.2.1.lt_width
      have hTerm :
          a + r = m :=
        hS.2
      exact False.elim
        ((Nat.ne_of_lt hRoof) hTerm)
  | a, r :: t :: rs, s :: u :: ts, hR, hS => by
      have hrs := recordBlock_length_eq_of_same_start hR.1 hS.1
      subst s
      have hTail := realizesBlocksFrom_unique
        (a + r) (t :: rs) (u :: ts) hR.2.2 hS.2.2
      rw [hTail]

/-- 同じ admissible profile 上の critical record skeleton は一意。 -/
@[ext] theorem criticalRecordSkeleton_ext
    {m : ℕ}
    (R S : CriticalRecordSkeleton m)
    (hProfile : R.profile = S.profile) :
    R = S := by
  cases R with
  | mk rp rs rr =>
      cases S with
      | mk sp ss sr =>
          dsimp at hProfile
          subst sp
          have hLengths :=
            realizesBlocksFrom_unique
              initialRoofAnchor rs.lengths ss.lengths rr.2 sr.2
          cases rs with
          | mk rls rpos =>
              cases ss with
              | mk sls spos =>
                  dsimp at hLengths
                  subst sls
                  rfl

/-- tie-free RecordView から作った skeleton は、同じ profile の任意の realization と一致。 -/
theorem criticalRecordSkeleton_eq_recordView_constructor
    {m : ℕ}
    (S : CriticalRecordSkeleton m)
    (R : RecordView m)
    (hm : 1 < m)
    (T : NoRecordLevelTie R.profile.1 initialRoofAnchor)
    (hProfile : S.profile = R.profile) :
    S = R.toCriticalRecordSkeleton hm T := by
  apply criticalRecordSkeleton_ext
  simpa using hProfile

end Ferrers
end Collatz3
