import CollatzLean.Collatz.Word.Affine
import CollatzLean.Collatz.TwoAdic.Factorization
import Mathlib.Tactic.Linarith

/-!
# 有限語のprefix/suffix幾何

first crossingとall-suffix contractingを無限軌道から独立させる。
-/

namespace Collatz
namespace Word

/-- すべてのproper prefixがexpanding。 -/
def ProperPrefixesExpanding (w : Collatz.Word) : Prop :=
  ∀ m : ℕ, 0 < m → m < w.length → Expanding (w.take m)

/-- proper prefixはexpandingで、語全体で初めてcontracting。 -/
structure FirstCrossing (w : Collatz.Word) : Prop where
  nonempty : w ≠ []
  properExpanding : w.ProperPrefixesExpanding
  terminalContracting : w.Contracting

/-- すべての非空suffixがcontracting。 -/
def AllSuffixesContracting : Collatz.Word → Prop
  | [] => True
  | e :: w => Contracting (e :: w) ∧ AllSuffixesContracting w

/-- prefix積に対する重み付き上界。 -/
def WeightedPrefixBound (a c : ℕ) (w : Collatz.Word) : Prop :=
  ∀ j : ℕ, j < w.length →
    a * 2 ^ twoSteps (w.take j) ≤ c * 3 ^ j

/-- takeのodd step数。 -/
theorem oddSteps_take_eq {w : Collatz.Word} {j : ℕ}
    (h : j ≤ w.length) : oddSteps (w.take j) = j := by
  simp [oddSteps, List.length_take, h]

/-- proper prefix expandingから重み付きprefix boundを得る。 -/
theorem ProperPrefixesExpanding.weightedPrefixBound
    {w : Collatz.Word}
    (h : w.ProperPrefixesExpanding) :
    WeightedPrefixBound 1 1 w := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp
  · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
    have hExp := h j hjPos hj
    have hodd := oddSteps_take_eq (w := w) (Nat.le_of_lt hj)
    unfold Expanding at hExp
    simpa [WeightedPrefixBound, hodd] using Nat.le_of_lt hExp

/-- valid非空語はexpandingまたはcontracting。 -/
theorem expanding_or_contracting_of_valid_nonempty
    {w : Collatz.Word} (hw : w.Valid) (hne : w ≠ []) :
    w.Expanding ∨ w.Contracting := by
  unfold Expanding Contracting
  rcases lt_trichotomy (2 ^ w.twoSteps) (3 ^ w.oddSteps) with h | h | h
  · exact Or.inl h
  · have hH : 0 < w.twoSteps := twoSteps_pos_of_valid_nonempty hw hne
    have hodd : Odd (3 ^ w.oddSteps) := (show Odd (3 : ℕ) by decide).pow
    have heven : Even (2 ^ w.twoSteps) :=
      (show Even (2 : ℕ) by decide).pow_of_ne_zero (Nat.ne_of_gt hH)
    have : Even (3 ^ w.oddSteps) := by rw [← h]; exact heven
    exact False.elim (Collatz.TwoAdic.odd_even_false hodd this)
  · exact Or.inr h

/-- all-suffix contractingなら語全体もcontracting。 -/
theorem AllSuffixesContracting.whole
    {w : Collatz.Word} (hne : w ≠ []) (h : w.AllSuffixesContracting) :
    w.Contracting := by
  cases w with
  | nil => contradiction
  | cons e w => exact h.1

/-- actual realizationが真に下がるvalid非空語はcontracting。 -/
theorem Realizes.contracting_of_start_gt_end
    {w : Collatz.Word} {x y : ℕ}
    (h : w.Realizes x y) (hw : w.Valid) (hne : w ≠ [])
    (hxy : y < x) : w.Contracting := by
  rcases expanding_or_contracting_of_valid_nonempty hw hne with hE | hC
  · unfold Realizes at h
    unfold Expanding at hE
    have hleft : 2 ^ w.twoSteps * y < 3 ^ w.oddSteps * x := by
      have hA : 0 < 2 ^ w.twoSteps := Nat.pow_pos (by omega : 0 < (2 : ℕ))
      have hC : 0 < 3 ^ w.oddSteps := Nat.pow_pos (by omega : 0 < (3 : ℕ))
      nlinarith
    rw [h] at hleft
    omega
  · exact hC

/-- contractingなvalid非空語には最小first crossingが存在する。 -/
theorem exists_firstCrossing_of_contracting
    {w : Collatz.Word}
    (hw : Valid w)
    (hne : w ≠ [])
    (hC : Contracting w) :
    ∃ p : ℕ, p ≤ w.length ∧ FirstCrossing (w.take p) := by
  classical
  let Bad : ℕ → Prop :=
    fun p =>
      0 < p ∧
      p ≤ w.length ∧
      ¬ Expanding (w.take p)
  have hlen : 0 < w.length := by
    exact List.length_pos_iff.mpr hne
  have hnotExpanding : ¬ Expanding w := by
    intro hE
    change 2 ^ twoSteps w < 3 ^ oddSteps w at hE
    change 3 ^ oddSteps w < 2 ^ twoSteps w at hC
    omega
  have hbad : ∃ p : ℕ, Bad p := by
    refine ⟨w.length, ?_⟩
    refine ⟨hlen, le_rfl, ?_⟩
    simpa using hnotExpanding
  let p := Nat.find hbad
  have hpBad : Bad p := by
    dsimp [p]
    exact Nat.find_spec hbad
  have hpPos : 0 < p :=
    hpBad.1
  have hpLe : p ≤ w.length :=
    hpBad.2.1
  have hpNotExpanding : ¬ Expanding (w.take p) :=
    hpBad.2.2
  have hlenTake : (w.take p).length = p := by
    exact List.length_take_of_le hpLe
  have hproper : ProperPrefixesExpanding (w.take p) := by
    intro q hqpos hqlen
    have hqp : q < p := by
      rw [hlenTake] at hqlen
      exact hqlen
    by_contra hqbad
    have hqleW : q ≤ w.length := by
      omega
    have hqbad' : ¬ Expanding (w.take q) := by
      simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hqp)] using hqbad
    have hqBad : Bad q := by
      exact ⟨hqpos, hqleW, hqbad'⟩
    have hmin : p ≤ q := by
      dsimp [p]
      exact Nat.find_min' hbad hqBad
    omega
  have htakeNonempty : w.take p ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hlenTake]
    exact hpPos
  have htakeValid : Valid (w.take p) := by
    intro e he
    apply hw e
    have hdecomp :
        w.take p ++ w.drop p = w :=
      List.take_append_drop p w
    rw [← hdecomp]
    exact List.mem_append.mpr (Or.inl he)
  have htakeContracting : Contracting (w.take p) :=
    (expanding_or_contracting_of_valid_nonempty
        htakeValid htakeNonempty).resolve_left hpNotExpanding
  exact
    ⟨p, hpLe,
      ⟨htakeNonempty, hproper, htakeContracting⟩⟩

end Word
end Collatz
