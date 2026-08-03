import CollatzLean.CollatzSecondLayer.LimitWord

/-!
# first-crossingとone-sided meanderの分岐

各future-minimum tailについて、純乗法的収縮が初めて起こる有限語か、
永久に膨張するone-sided meanderかを区別する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- すべてのproper prefixが膨張すること。 -/
def ProperPrefixesExpanding (w : ExpWord) : Prop :=
  ∀ m : ℕ,
    0 < m →
    m < w.length →
    Expanding (w.take m)

/-- proper prefixでは膨張し、語全体で初めて収縮すること。 -/
structure FirstCrossing (w : ExpWord) : Prop where
  nonempty : w ≠ []
  properExpanding : ProperPrefixesExpanding w
  terminalContracting : Contracting w

/-- 位置`n`から始まるtailが永久に純乗法的膨張側にあること。 -/
def MeanderAt (O : OddOrbit) (n : ℕ) : Prop :=
  ∀ m : ℕ,
    0 < m →
    Expanding (O.segmentWord n m)

/-- 位置`n`から長さ`p`でfirst-crossingが起こること。 -/
def FirstCrossingAt (O : OddOrbit) (n p : ℕ) : Prop :=
  FirstCrossing (O.segmentWord n p)

/-- first-crossingの長さは正である。 -/
lemma FirstCrossingAt.length_pos
    {O : OddOrbit} {n p : ℕ}
    (h : FirstCrossingAt O n p) :
    0 < p := by
  unfold FirstCrossingAt at h
  cases p with
  | zero =>
      exact False.elim (h.nonempty rfl)
  | succ p =>
      omega

/-- 有効非空語は膨張か収縮のどちらかである。 -/
lemma expanding_or_contracting_of_valid_nonempty
    {w : ExpWord}
    (hw : Valid w)
    (hne : w ≠ []) :
    Expanding w ∨ Contracting w := by
  unfold Expanding Contracting
  rcases lt_trichotomy
      (2 ^ twoSteps w)
      (3 ^ oddSteps w) with h | h | h
  · exact Or.inl h
  · exact False.elim
      (twoPow_ne_threePow_of_valid_nonempty hw hne h)
  · exact Or.inr h

/--
位置`n`のtailがmeanderでないなら、
正の長さを持つ非膨張segmentが存在する。
-/
lemma exists_nonexpanding_segment_of_not_meander
    (O : OddOrbit)
    (n : ℕ)
    (hM : ¬MeanderAt O n) :
    ∃ p : ℕ,
      0 < p ∧
      ¬Expanding (O.segmentWord n p) := by
  classical
  by_contra hnone
  apply hM
  intro p hp
  by_contra hpbad
  exact hnone ⟨p, hp, hpbad⟩

/-- 正の長さを持つsegment wordは空語ではない。 -/
lemma segmentWord_nonempty_of_length_pos
    {O : OddOrbit}
    {n p : ℕ}
    (hp : 0 < p) :
    O.segmentWord n p ≠ [] := by
  intro hnil
  have hpzero : p = 0 := by
    simpa using congrArg List.length hnil
  omega

/--
正の非膨張segmentが長さについて最小なら、
そのすべてのproper prefixは膨張する。

`Nat.find`そのものではなく、最小性を仮定として受け取ることで、
定理の型に古典的な決定可能性を要求しない形にしている。
-/
lemma properPrefixesExpanding_of_minimal_nonexpanding
    (O : OddOrbit)
    (n p : ℕ)
    (hminimal :
      ∀ q : ℕ,
        0 < q →
        ¬Expanding (O.segmentWord n q) →
        p ≤ q) :
    ProperPrefixesExpanding (O.segmentWord n p) := by
  intro q hqpos hqlen
  have hqlt : q < p := by
    simpa using hqlen
  have hqle : q ≤ p :=
    Nat.le_of_lt hqlt
  rw [O.segmentWord_take_of_le hqle]
  by_contra hqbad
  have hpq : p ≤ q :=
    hminimal q hqpos hqbad
  omega

/--
有効な非空語が膨張しないなら、その語は収縮する。
膨張と収縮の間の等号は、有効非空性によって排除される。
-/
lemma contracting_of_valid_nonempty_not_expanding
    {w : ExpWord}
    (hw : Valid w)
    (hne : w ≠ [])
    (hnot : ¬Expanding w) :
    Contracting w := by
  rcases
      expanding_or_contracting_of_valid_nonempty hw hne with
    hE | hC
  · exact False.elim (hnot hE)
  · exact hC

/--
正の長さを持つ非膨張segmentが一つでも存在すれば、
その最小長segmentがfirst-crossingを与える。
-/
lemma exists_firstCrossingAt_of_exists_nonexpanding
    (O : OddOrbit)
    (n : ℕ)
    (hbad :
      ∃ p : ℕ,
        0 < p ∧
        ¬Expanding (O.segmentWord n p)) :
    ∃ p : ℕ,
      FirstCrossingAt O n p := by
  classical
  let p := Nat.find hbad
  have hp :
      0 < p ∧
      ¬Expanding (O.segmentWord n p) := by
    simpa [p] using Nat.find_spec hbad
  have hminimal :
      ∀ q : ℕ,
        0 < q →
        ¬Expanding (O.segmentWord n q) →
        p ≤ q := by
    intro q hqpos hqbad
    simpa [p] using
      Nat.find_min' hbad ⟨hqpos, hqbad⟩
  have hne :
      O.segmentWord n p ≠ [] :=
    segmentWord_nonempty_of_length_pos hp.1
  have hproper :
      ProperPrefixesExpanding (O.segmentWord n p) :=
    properPrefixesExpanding_of_minimal_nonexpanding
      O n p hminimal
  have hvalid :
      Valid (O.segmentWord n p) :=
    (O.runs_segment n p).valid
  have hcontract :
      Contracting (O.segmentWord n p) :=
    contracting_of_valid_nonempty_not_expanding
      hvalid hne hp.2
  refine ⟨p, ?_⟩
  unfold FirstCrossingAt
  exact ⟨hne, hproper, hcontract⟩

/--
一つのtailはone-sided meanderであるか、
有限first-crossingを持つ。
-/
theorem meander_or_firstCrossing_at
    (O : OddOrbit)
    (n : ℕ) :
    MeanderAt O n ∨
      ∃ p : ℕ, FirstCrossingAt O n p := by
  by_cases hM : MeanderAt O n
  · exact Or.inl hM
  · have hbad :
        ∃ p : ℕ,
          0 < p ∧
          ¬Expanding (O.segmentWord n p) :=
      exists_nonexpanding_segment_of_not_meander
        O n hM
    exact Or.inr
      (exists_firstCrossingAt_of_exists_nonexpanding
        O n hbad)

/-- moving-limit列の一つの実anchorがone-sided meanderになること。 -/
structure OneSidedMeanderData (O : OddOrbit) where
  limit : MovingLimitData O
  sequenceIndex : ℕ
  meander : MeanderAt O (limit.minima.index sequenceIndex)

/-- 各moving anchorにfirst-crossingがあり、その長さが無限大へ進むデータ。 -/
structure FirstCrossingSequenceData (O : OddOrbit) where
  limit : MovingLimitData O
  crossingLength : ℕ → ℕ
  crossing : ∀ j,
    FirstCrossingAt O (limit.minima.index j) (crossingLength j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < crossingLength j

/--
どのfuture-minimum tailもmeanderでないなら、
各future-minimum tailは有限first-crossingを持つ。
-/
lemma firstCrossingAt_each_minimum_of_no_meander
    {O : OddOrbit}
    (D : MovingLimitData O)
    (hM :
      ¬∃ j : ℕ,
        MeanderAt O (D.minima.index j)) :
    ∀ j : ℕ,
      ∃ p : ℕ,
        FirstCrossingAt O (D.minima.index j) p := by
  intro j
  rcases
      meander_or_firstCrossing_at
        O (D.minima.index j) with
    hm | hc
  · exact False.elim (hM ⟨j, hm⟩)
  · exact hc


/--
各future-minimumにfirst-crossingが存在するなら、
その長さを与える関数を一つ選択できる。
-/
lemma exists_firstCrossing_length_function
    {O : OddOrbit}
    (D : MovingLimitData O)
    (hcross :
      ∀ j : ℕ,
        ∃ p : ℕ,
          FirstCrossingAt O (D.minima.index j) p) :
    ∃ p : ℕ → ℕ,
      ∀ j : ℕ,
        FirstCrossingAt O
          (D.minima.index j)
          (p j) := by
  classical
  let p : ℕ → ℕ :=
    fun j => Classical.choose (hcross j)
  refine ⟨p, ?_⟩
  intro j
  exact Classical.choose_spec (hcross j)


/--
安定した長さ`M`のprefix内には、
first-crossing全体は収まらない。

仮にfirst-crossing長`p`が`M`以下なら、
その語は極限語の長さ`p`のprefixと一致する。
極限語側では膨張するが、first-crossing側では収縮するため矛盾する。
-/
lemma firstCrossing_length_gt_of_stable_prefix
    {O : OddOrbit}
    (D : MovingLimitData O)
    {j M p : ℕ}
    (hstable :
      O.segmentWord (D.minima.index j) M =
        prefixWord D.limitExponent M)
    (hp :
      FirstCrossingAt O
        (D.minima.index j)
        p) :
    M < p := by
  by_contra hnot
  have hple : p ≤ M :=
    Nat.le_of_not_gt hnot
  have hEq :=
    congrArg (List.take p) hstable
  rw [
    O.segmentWord_take_of_le hple,
    prefixWord_take_of_le D.limitExponent hple
  ] at hEq
  have hSame :
      O.segmentWord (D.minima.index j) p =
        D.limitWord p := by
    simpa [MovingLimitData.limitWord] using hEq
  have hExp :
      Expanding (D.limitWord p) :=
    limitWord_expanding D hp.length_pos
  have hTerminal :
      Contracting
        (O.segmentWord (D.minima.index j) p) :=
    hp.terminalContracting
  rw [hSame] at hTerminal
  unfold Expanding at hExp
  unfold Contracting at hTerminal
  omega


/--
future-minimumごとに選んだfirst-crossing長は、
任意の固定長を最終的に超える。
-/
lemma firstCrossing_lengths_eventually_large
    {O : OddOrbit}
    (D : MovingLimitData O)
    (p : ℕ → ℕ)
    (hp :
      ∀ j : ℕ,
        FirstCrossingAt O
          (D.minima.index j)
          (p j)) :
    ∀ M : ℕ,
      ∃ J : ℕ,
        ∀ j : ℕ,
          J ≤ j →
          M < p j := by
  intro M
  obtain ⟨J, hstable⟩ :=
    D.prefix_stabilizes M
  refine ⟨J, ?_⟩
  intro j hj
  exact firstCrossing_length_gt_of_stable_prefix
    D
    (hstable j hj)
    (hp j)


/--
極限語の全prefix膨張を用いると、moving-limit列は
one-sided meanderか、長さが無限大へ進むfirst-crossing列へ分岐する。
-/
theorem firstCrossingSequence_or_meander
    {O : OddOrbit}
    (D : MovingLimitData O) :
    Nonempty (OneSidedMeanderData O) ∨
      Nonempty (FirstCrossingSequenceData O) := by
  classical
  by_cases hM :
      ∃ j : ℕ,
        MeanderAt O (D.minima.index j)
  · rcases hM with ⟨j, hj⟩
    exact Or.inl ⟨⟨D, j, hj⟩⟩
  · have hcross :
        ∀ j : ℕ,
          ∃ p : ℕ,
            FirstCrossingAt O
              (D.minima.index j)
              p :=
      firstCrossingAt_each_minimum_of_no_meander
        D hM
    obtain ⟨p, hp⟩ :=
      exists_firstCrossing_length_function
        D hcross
    have htend :
        ∀ M : ℕ,
          ∃ J : ℕ,
            ∀ j : ℕ,
              J ≤ j →
              M < p j :=
      firstCrossing_lengths_eventually_large
        D p hp
    exact Or.inr
      ⟨⟨D, p, hp, htend⟩⟩

/-- プロジェクト全体で使うone-sided meander例外。 -/
def HasOneSidedMeander : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧ Nonempty (OneSidedMeanderData O)

end CollatzSecondLayer
