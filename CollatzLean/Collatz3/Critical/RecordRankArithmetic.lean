import CollatzLean.Collatz3.Critical.BestUpperWidth
import CollatzLean.Collatz3.Critical.RecordSkeleton
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3: critical record rank の基礎算術

RecordView の canonicalization と terminal block の議論の双方で使う、
critical chord rank の小さな共通補題だけを置く。
Ferrers record view や actual orbit は import しない。
-/

namespace Collatz3
namespace Critical

/-- `m > 2` なら critical terminal depth は `2m` より strict に小さい。 -/
theorem criticalTwoDepth_lt_two_mul
    {m : ℕ}
    (hm : 2 < m) :
    criticalTwoDepth m < 2 * m := by
  have h3 : 3 ≤ m := by omega
  rcases Nat.exists_eq_add_of_le h3 with ⟨t, ht⟩
  subst m
  have hPow : 3 ^ t ≤ 4 ^ t :=
    Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ≤ 4) t
  have hUpper :
      3 ^ (3 + t) ≤
        2 ^ ((2 * (3 + t) - 2) + 1) := by
    calc
      3 ^ (3 + t) = 27 * 3 ^ t := by
        rw [pow_add]
        norm_num
      _ ≤ 27 * 4 ^ t := Nat.mul_le_mul_left 27 hPow
      _ ≤ 32 * 4 ^ t :=
        Nat.mul_le_mul_right (4 ^ t) (by norm_num)
      _ = 2 ^ ((2 * (3 + t) - 2) + 1) := by
        have hExp : (2 * (3 + t) - 2) + 1 = 5 + 2 * t := by omega
        rw [hExp, pow_add, pow_mul]
        norm_num
  have hBeatty :
      beattyIndex (3 + t) ≤ 2 * (3 + t) - 2 :=
    beattyIndex_le_of_upper hUpper
  unfold criticalTwoDepth
  omega

/-- roof cut の chord rank は strict に正。 -/
theorem profileChordRank_pos_of_roofCut
    {m : ℕ}
    {h : Profile m}
    {a : ℕ}
    (R : IsRoofCut h a) :
    0 < profileChordRank h a := by
  have hm : 0 < m := lt_trans R.pos R.lt_width
  have hNat :=
    beattyIndex_below_criticalChord
      (m := m) (r := a) hm R.pos
  have hCut : cutDepth h a = beattyIndex a := by
    calc
      cutDepth h a = profileHeight h a := by
        simp [cutDepth_of_lt, profileHeight_of_lt, R.lt_width]
      _ = beattyIndex a := R.height_eq
  have hNatZ :
      (m : ℤ) * (beattyIndex a : ℤ) <
        (criticalTwoDepth m : ℤ) * (a : ℤ) := by
    exact_mod_cast hNat
  unfold profileChordRank
  rw [hCut]
  linarith

/-- canonical anchor `1` の rank は `m>2` なら width 自身より小さい。 -/
theorem profileChordRank_initialRoofAnchor_lt_width
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 2 < m) :
    profileChordRank h initialRoofAnchor < (m : ℤ) := by
  have hDepth := criticalTwoDepth_lt_two_mul hm
  have hHeight := profileHeight_one_eq_one A (by omega)
  have hCut : cutDepth h initialRoofAnchor = 1 := by
    have hLt : initialRoofAnchor < m := by
      simp [initialRoofAnchor]
      omega
    calc
      cutDepth h initialRoofAnchor = profileHeight h initialRoofAnchor := by rfl
      _ = 1 := by
        simpa [initialRoofAnchor] using hHeight
  have hDepthZ :
      (criticalTwoDepth m : ℤ) < 2 * (m : ℤ) := by
    exact_mod_cast hDepth
  unfold profileChordRank
  rw [hCut]
  simp only [
    initialRoofAnchor,
    Nat.cast_one,
    mul_one
  ]
  linarith


end Critical
end Collatz3
