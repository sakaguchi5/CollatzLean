import CollatzLean.CollatzOrbitCore.FutureMinimum
import CollatzLean.CollatzFirstLayer.Affine

import Mathlib.Tactic.Linarith


/-!
# one-sided meanderとmoving first-crossing

各future-minimum tailを、永久膨張するtailか最初に収縮する有限語へ分ける。
さらにfuture-minimum値の増大とfirst-crossingのアフィン上界だけから、
first-crossing長が無限大へ進むことを証明する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- すべてのproper prefixが純乗法的に膨張する。 -/
def ProperPrefixesExpanding (w : ExpWord) : Prop :=
  ∀ m : ℕ, 0 < m → m < w.length → Expanding (w.take m)

/-- proper prefixは膨張し、語全体で初めて収縮する。 -/
structure FirstCrossing (w : ExpWord) : Prop where
  nonempty : w ≠ []
  properExpanding : ProperPrefixesExpanding w
  terminalContracting : Contracting w

/-- 位置`n`から始まるtailが永久に膨張する。 -/
def MeanderAt (O : OddOrbit) (n : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → Expanding (O.segmentWord n m)

/-- 位置`n`から長さ`p`でfirst crossingが起こる。 -/
def FirstCrossingAt (O : OddOrbit) (n p : ℕ) : Prop :=
  FirstCrossing (O.segmentWord n p)

namespace FirstCrossingAt

/-- first-crossing長は正。 -/
theorem length_pos
    {O : OddOrbit} {n p : ℕ}
    (h : FirstCrossingAt O n p) : 0 < p := by
  unfold FirstCrossingAt at h
  cases p with
  | zero => exact False.elim (h.nonempty rfl)
  | succ p => omega

end FirstCrossingAt

/-- 有効な非空語では、`2^H`と`3^p`は等しくならない。 -/
lemma twoPow_ne_threePow_of_valid_nonempty
    {w : ExpWord} (hw : Valid w) (hne : w ≠ []) :
    2 ^ twoSteps w ≠ 3 ^ oddSteps w := by
  intro heq
  have hH : 0 < twoSteps w :=
    twoSteps_pos_of_valid_nonempty hw hne
  have hodd3 : Odd (3 : ℕ) := ⟨1, by omega⟩
  have hodd : Odd (3 ^ oddSteps w) :=
    hodd3.pow
  have heven2 : Even (2 : ℕ) := ⟨1, by omega⟩
  have heven : Even (2 ^ twoSteps w) :=
    heven2.pow_of_ne_zero (Nat.ne_of_gt hH)
  have hboth : Even (3 ^ oddSteps w) := by
    rw [← heq]
    exact heven
  exact odd_even_false_nat hodd hboth

/-- 有効非空語は膨張または収縮のどちらか。 -/
theorem expanding_or_contracting_of_valid_nonempty
    {w : ExpWord} (hw : Valid w) (hne : w ≠ []) :
    Expanding w ∨ Contracting w := by
  unfold Expanding Contracting
  rcases lt_trichotomy (2 ^ twoSteps w) (3 ^ oddSteps w) with h | h | h
  · exact Or.inl h
  · exact False.elim (twoPow_ne_threePow_of_valid_nonempty hw hne h)
  · exact Or.inr h

/-- meanderでないtailには正長の非膨張segmentがある。 -/
theorem exists_nonexpanding_segment_of_not_meander
    (O : OddOrbit) (n : ℕ) (hM : ¬ MeanderAt O n) :
    ∃ p : ℕ, 0 < p ∧ ¬ Expanding (O.segmentWord n p) := by
  classical
  by_contra hnone
  apply hM
  intro p hp
  by_contra hpbad
  exact hnone ⟨p, hp, hpbad⟩

/-- 正長segmentは非空。 -/
theorem segmentWord_nonempty_of_length_pos
    {O : OddOrbit} {n p : ℕ} (hp : 0 < p) :
    O.segmentWord n p ≠ [] := by
  intro hnil
  have hpzero : p = 0 := by
    simpa using congrArg List.length hnil
  omega

/-- 最小非膨張segmentのproper prefixはすべて膨張する。 -/
theorem properPrefixesExpanding_of_minimal_nonexpanding
    (O : OddOrbit) (n p : ℕ)
    (hminimal :
      ∀ q : ℕ, 0 < q → ¬ Expanding (O.segmentWord n q) → p ≤ q) :
    ProperPrefixesExpanding (O.segmentWord n p) := by
  intro q hqpos hqlen
  have hqlt : q < p := by simpa using hqlen
  have hqle : q ≤ p := Nat.le_of_lt hqlt
  rw [O.segmentWord_take_of_le hqle]
  by_contra hqbad
  have hpq : p ≤ q := hminimal q hqpos hqbad
  omega

/-- 有効非空な非膨張語は収縮する。 -/
theorem contracting_of_valid_nonempty_not_expanding
    {w : ExpWord} (hw : Valid w) (hne : w ≠ [])
    (hnot : ¬ Expanding w) : Contracting w := by
  rcases expanding_or_contracting_of_valid_nonempty hw hne with hE | hC
  · exact False.elim (hnot hE)
  · exact hC

/-- 非膨張segmentが存在すれば最小長first-crossingが存在する。 -/
theorem exists_firstCrossingAt_of_exists_nonexpanding
    (O : OddOrbit) (n : ℕ)
    (hbad : ∃ p : ℕ, 0 < p ∧ ¬ Expanding (O.segmentWord n p)) :
    ∃ p : ℕ, FirstCrossingAt O n p := by
  classical
  let p := Nat.find hbad
  have hp : 0 < p ∧ ¬ Expanding (O.segmentWord n p) := by
    simpa [p] using Nat.find_spec hbad
  have hminimal :
      ∀ q : ℕ, 0 < q → ¬ Expanding (O.segmentWord n q) → p ≤ q := by
    intro q hqpos hqbad
    simpa [p] using Nat.find_min' hbad ⟨hqpos, hqbad⟩
  have hne : O.segmentWord n p ≠ [] :=
    segmentWord_nonempty_of_length_pos hp.1
  have hproper : ProperPrefixesExpanding (O.segmentWord n p) :=
    properPrefixesExpanding_of_minimal_nonexpanding O n p hminimal
  have hvalid : Valid (O.segmentWord n p) :=
    (O.runs_segment n p).valid
  have hcontract : Contracting (O.segmentWord n p) :=
    contracting_of_valid_nonempty_not_expanding hvalid hne hp.2
  exact ⟨p, ⟨hne, hproper, hcontract⟩⟩

/-- 任意のtailはmeanderか有限first-crossingを持つ。 -/
theorem meander_or_firstCrossing_at (O : OddOrbit) (n : ℕ) :
    MeanderAt O n ∨ ∃ p : ℕ, FirstCrossingAt O n p := by
  by_cases hM : MeanderAt O n
  · exact Or.inl hM
  · exact Or.inr
      (exists_firstCrossingAt_of_exists_nonexpanding O n
        (exists_nonexpanding_segment_of_not_meander O n hM))

/-- prefix積に許される重み付き膨張条件。 -/
def WeightedPrefixBound (a c : ℕ) (w : ExpWord) : Prop :=
  ∀ j : ℕ, j < w.length →
    a * 2 ^ twoSteps (w.take j) ≤ c * 3 ^ j

/-- 重み付きprefix boundからアフィン定数を評価する。 -/
theorem weighted_affineConst_le
    (w : ExpWord) (a c : ℕ)
    (h : WeightedPrefixBound a c w) :
    a * affineConst w ≤ w.length * c * 3 ^ w.length := by
  induction w generalizing a c with
  | nil => simp [affineConst]
  | cons e w ih =>
      have h0 : a ≤ c := by
        have hh := h 0 (by simp)
        simpa [WeightedPrefixBound, twoSteps] using hh
      have htail : WeightedPrefixBound (a * 2 ^ e) (c * 3) w := by
        intro j hj
        have hh := h (j + 1) (by simp; omega)
        simpa [WeightedPrefixBound, List.take_succ_cons,
          twoSteps_cons, pow_add, pow_succ,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh
      have hi := ih (a := a * 2 ^ e) (c := c * 3) htail
      calc
        a * affineConst (e :: w)
            = a * 3 ^ w.length + (a * 2 ^ e) * affineConst w := by
                simp [affineConst]
                ring
        _ ≤ c * 3 ^ w.length +
              (w.length * (c * 3) * 3 ^ w.length) := by
                exact Nat.add_le_add
                  (Nat.mul_le_mul_right _ h0)
                  hi
        _ ≤ (e :: w).length * c * 3 ^ (e :: w).length := by
                simp only [List.length_cons]
                rw [pow_succ]
                nlinarith [Nat.zero_le (c * 3 ^ w.length)]

/-- `take j`のodd step数は`j`。 -/
theorem oddSteps_take_eq
    {w : ExpWord} {j : ℕ} (hj : j ≤ w.length) :
    oddSteps (w.take j) = j := by
  simp [oddSteps, List.length_take, Nat.min_eq_left hj]

/-- first-crossingの各prefixは重み1で`3^j`以下。 -/
theorem firstCrossing_weightedPrefixBound
    {w : ExpWord} (hC : FirstCrossing w) :
    WeightedPrefixBound 1 1 w := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp only [List.take_zero, twoSteps_nil, pow_zero, mul_one, Std.le_refl]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hE : Expanding (w.take j) := hC.properExpanding j hjpos hj
    have hbound :
        2 ^ twoSteps (w.take j) ≤ 3 ^ oddSteps (w.take j) := by
      unfold Expanding at hE
      exact Nat.le_of_lt hE
    have hodd : oddSteps (w.take j) = j :=
      oddSteps_take_eq (Nat.le_of_lt hj)
    simpa [WeightedPrefixBound, hodd] using hbound

/-- first-crossing語では`affineConst ≤ p·3^p`。 -/
theorem affineConst_le_length_mul_threePow
    {w : ExpWord} (hC : FirstCrossing w) :
    affineConst w ≤ w.length * 3 ^ w.length := by
  have h := weighted_affineConst_le w 1 1
      (firstCrossing_weightedPrefixBound hC)
  simpa using h

/-- future-minimumから始まるfirst-crossingの開始値は`p·3^p`以下。 -/
theorem futureMinimum_start_le_length_mul_threePow
    {O : OddOrbit} {n p : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    O.value n ≤ p * 3 ^ p := by
  let w := O.segmentWord n p
  have hrun : Realizes w (O.value n) (O.value (n + p)) :=
    O.realizes_segment n p
  have hend : O.value n ≤ O.value (n + p) :=
    O.futureMinimum_le_segment_end hmin p
  have hscaled :
      2 ^ twoSteps w * O.value n ≤
        3 ^ oddSteps w * O.value n + affineConst w := by
    calc
      2 ^ twoSteps w * O.value n
          ≤ 2 ^ twoSteps w * O.value (n + p) :=
        Nat.mul_le_mul_left _ hend
      _ = 3 ^ oddSteps w * O.value n + affineConst w := hrun
  have hcontract : 3 ^ oddSteps w < 2 ^ twoSteps w := by
    exact hC.terminalContracting
  have hgapPos : 0 < 2 ^ twoSteps w - 3 ^ oddSteps w :=
    Nat.sub_pos_of_lt hcontract
  have hgap :
      (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n ≤
        affineConst w := by
    have hdecomp :
        2 ^ twoSteps w =
          3 ^ oddSteps w +
            (2 ^ twoSteps w - 3 ^ oddSteps w) :=
      (Nat.add_sub_of_le hcontract.le).symm
    have hcancel :
        3 ^ oddSteps w * O.value n +
            (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
          ≤
        3 ^ oddSteps w * O.value n + affineConst w := by
      calc
        3 ^ oddSteps w * O.value n +
            (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
            = 2 ^ twoSteps w * O.value n := by
                calc
                  3 ^ oddSteps w * O.value n +
                      (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
                      =
                    (3 ^ oddSteps w +
                        (2 ^ twoSteps w - 3 ^ oddSteps w)) *
                      O.value n := by
                        rw [Nat.add_mul]
                  _ = 2 ^ twoSteps w * O.value n := by
                        rw [← hdecomp]
        _ ≤ 3 ^ oddSteps w * O.value n + affineConst w := hscaled
    exact Nat.le_of_add_le_add_left hcancel
  have hone : 1 ≤ 2 ^ twoSteps w - 3 ^ oddSteps w := hgapPos
  have hstart : O.value n ≤ affineConst w := by
    calc
      O.value n = 1 * O.value n := by simp
      _ ≤ (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n :=
        Nat.mul_le_mul_right _ hone
      _ ≤ affineConst w := hgap
  calc
    O.value n ≤ affineConst w := hstart
    _ ≤ w.length * 3 ^ w.length :=
      affineConst_le_length_mul_threePow hC
    _ = p * 3 ^ p := by simp [w]

/-- bounded first-crossing長ではfuture-minimum開始値も一様有界。 -/
theorem futureMinimum_start_le_of_crossingLength_le
    {O : OddOrbit} {n p M : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p)
    (hp : p ≤ M) :
    O.value n ≤ M * 3 ^ M := by
  have hs := futureMinimum_start_le_length_mul_threePow hmin hC
  have hpow : 3 ^ p ≤ 3 ^ M :=
    Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hp
  calc
    O.value n ≤ p * 3 ^ p := hs
    _ ≤ M * 3 ^ M := Nat.mul_le_mul hp hpow

/-- 一つの非有界軌道上に実在するone-sided meander。 -/
structure OneSidedMeanderData (O : OddOrbit) where
  unbounded : O.Unbounded
  anchor : ℕ
  futureMinimum : O.FutureMinimumAt anchor
  meander : MeanderAt O anchor

/-- 非有界軌道上のone-sided meanderが存在する。 -/
def HasOneSidedMeander : Prop :=
  ∃ O : OddOrbit, Nonempty (OneSidedMeanderData O)

/-- moving future-minimumごとのfirst-crossing列。 -/
structure MovingFirstCrossingData (O : OddOrbit) where
  unbounded : O.Unbounded
  minima : O.FutureMinimumSequence
  crossingLength : ℕ → ℕ
  crossing : ∀ j,
    FirstCrossingAt O (minima.index j) (crossingLength j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < crossingLength j

/-- future-minimum上にmeanderがなければ、moving first-crossing列を構成できる。 -/
noncomputable def movingFirstCrossingData_of_no_meander
    (O : OddOrbit) (hU : O.Unbounded)
    (S : O.FutureMinimumSequence)
    (hM : ¬ ∃ j : ℕ, MeanderAt O (S.index j)) :
    MovingFirstCrossingData O := by
  have hex : ∀ j : ℕ, ∃ p : ℕ,
      FirstCrossingAt O (S.index j) p := by
    intro j
    rcases meander_or_firstCrossing_at O (S.index j) with hm | hc
    · exact False.elim (hM ⟨j, hm⟩)
    · exact hc
  let p : ℕ → ℕ := fun j => Classical.choose (hex j)
  have hp : ∀ j : ℕ, FirstCrossingAt O (S.index j) (p j) :=
    fun j => Classical.choose_spec (hex j)
  have htend :
      ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < p j := by
    intro M
    obtain ⟨J, hJ⟩ := S.values_eventually_large (M * 3 ^ M)
    refine ⟨J, ?_⟩
    intro j hj
    by_contra hnot
    have hple : p j ≤ M := Nat.le_of_not_gt hnot
    have hbound : O.value (S.index j) ≤ M * 3 ^ M :=
      futureMinimum_start_le_of_crossingLength_le
        (S.futureMinimum j) (hp j) hple
    exact Nat.not_lt_of_ge hbound (hJ j hj)
  exact
    { unbounded := hU
      minima := S
      crossingLength := p
      crossing := hp
      lengths_tend_to_infinity := htend }

end CollatzSecondLayer2
