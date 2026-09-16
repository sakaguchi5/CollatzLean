import CollatzLean.Collatz3.CSTConditional.IntegerReduction.BlockDefect
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: 純整数 block counting

許容 block length では

`2 * 3^r ≤ 3 * 2^beattyIndex(r)`

が成り立つ。この有限積だけから、actual orbit や実数 log を使わずに

* 任意の 3 block で defect rise は高々 2
* 任意の 5 block で defect rise は高々 3

を導く。

これは既存 A/C の `AAA` 禁止と 5-window `#A ≤ 3` の純整数版。
-/

namespace Collatz3
namespace IntegerReduction

open Critical

/-- 許容長一個の scale bound。 -/
theorem two_mul_threePow_le_three_mul_twoPow_of_admissibleLength
    {r : ℕ}
    (h : IsAdmissibleLength r) :
    2 * 3 ^ r ≤ 3 * 2 ^ Critical.beattyIndex r := by
  rcases h with ⟨hrPos, hrOne | hJump⟩
  · subst r
    simp [beattyIndex_one]
  · exact
      two_mul_threePow_le_three_mul_twoPow_of_finalJumpTwo
        hrPos hJump

/--
許容長の有限 list では scale bound が積に持ち上がる。

`2^q * 3^(Σr) ≤ 3^q * 2^(Σ beattyIndex r)`。
-/
theorem admissibleLengths_scale_bound
    {rs : List ℕ}
    (h : ∀ r ∈ rs, IsAdmissibleLength r) :
    2 ^ rs.length * 3 ^ rs.sum ≤
      3 ^ rs.length * 2 ^ (rs.map Critical.beattyIndex).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      have hr : IsAdmissibleLength r := h r (by simp)
      have hrs : ∀ s ∈ rs, IsAdmissibleLength s := by
        intro s hs
        exact h s (by simp [hs])
      have hHead :=
        two_mul_threePow_le_three_mul_twoPow_of_admissibleLength hr
      have hTail := ih hrs
      calc
        2 ^ (r :: rs).length * 3 ^ (r :: rs).sum
            =
            (2 * 3 ^ r) *
              (2 ^ rs.length * 3 ^ rs.sum) := by
                simp [pow_succ, pow_add]
                ring
        _ ≤
            (3 * 2 ^ Critical.beattyIndex r) *
              (3 ^ rs.length *
                2 ^ (rs.map Critical.beattyIndex).sum) :=
              Nat.mul_le_mul hHead hTail
        _ =
            3 ^ (r :: rs).length *
              2 ^ ((r :: rs).map Critical.beattyIndex).sum := by
                simp [pow_succ, pow_add]
                ring

private theorem three_admissible_lengths_beatty_bound
    (F r0 r1 r2 : ℕ)
    (h0 : IsAdmissibleLength r0)
    (h1 : IsAdmissibleLength r1)
    (h2 : IsAdmissibleLength r2) :
    Critical.beattyIndex (F + r0 + r1 + r2) ≤
      Critical.beattyIndex F +
        Critical.beattyIndex r0 +
        Critical.beattyIndex r1 +
        Critical.beattyIndex r2 + 2 := by
  have hScale :=
    admissibleLengths_scale_bound
      (rs := [r0, r1, r2]) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2)
  have hScale' :
      8 * 3 ^ (r0 + r1 + r2) ≤
        27 * 2 ^
          (Critical.beattyIndex r0 +
            Critical.beattyIndex r1 +
            Critical.beattyIndex r2) := by
    simpa [Nat.add_assoc] using hScale
  have hF := Critical.threePow_lt_twoPow_criticalTwoDepth F
  have hF' :
      3 ^ F < 2 ^ (Critical.beattyIndex F + 1) := by
    simpa [Critical.criticalTwoDepth] using hF
  by_contra hNot
  have hGap :
      Critical.beattyIndex F +
          Critical.beattyIndex r0 +
          Critical.beattyIndex r1 +
          Critical.beattyIndex r2 + 3 ≤
        Critical.beattyIndex (F + r0 + r1 + r2) := by
    omega
  have hTotalPos : 0 < F + r0 + r1 + r2 := by
    have hr0 := h0.1
    omega
  have hLower := Critical.beattyIndex_lower_strict hTotalPos
  have hPowGap :
      2 ^
          (Critical.beattyIndex F +
            Critical.beattyIndex r0 +
            Critical.beattyIndex r1 +
            Critical.beattyIndex r2 + 3) ≤
        2 ^ Critical.beattyIndex (F + r0 + r1 + r2) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hGap
  have hLowerScaled :
      8 * 2 ^
          (Critical.beattyIndex F +
            Critical.beattyIndex r0 +
            Critical.beattyIndex r1 +
            Critical.beattyIndex r2 + 3) <
        8 * 3 ^ (F + r0 + r1 + r2) := by
    exact
      (Nat.mul_lt_mul_left (by norm_num : 0 < (8 : ℕ))).2
        (lt_of_le_of_lt hPowGap hLower)
  have hUpperScaled :
      8 * 3 ^ (F + r0 + r1 + r2) <
        27 * 2 ^
          (Critical.beattyIndex F + 1 +
            (Critical.beattyIndex r0 +
              Critical.beattyIndex r1 +
              Critical.beattyIndex r2)) := by
    calc
      8 * 3 ^ (F + r0 + r1 + r2)
          = 3 ^ F * (8 * 3 ^ (r0 + r1 + r2)) := by
              rw [show F + r0 + r1 + r2 = F + (r0 + r1 + r2) by omega,
                pow_add]
              ring
      _ ≤
          3 ^ F *
            (27 * 2 ^
              (Critical.beattyIndex r0 +
                Critical.beattyIndex r1 +
                Critical.beattyIndex r2)) :=
            Nat.mul_le_mul_left _ hScale'
      _ <
          2 ^ (Critical.beattyIndex F + 1) *
            (27 * 2 ^
              (Critical.beattyIndex r0 +
                Critical.beattyIndex r1 +
                Critical.beattyIndex r2)) := by
            exact
              (Nat.mul_lt_mul_right
                (by positivity :
                  0 < 27 * 2 ^
                    (Critical.beattyIndex r0 +
                      Critical.beattyIndex r1 +
                      Critical.beattyIndex r2))).2 hF'
      _ =
          27 * 2 ^
            (Critical.beattyIndex F + 1 +
              (Critical.beattyIndex r0 +
                Critical.beattyIndex r1 +
                Critical.beattyIndex r2)) := by
              rw [pow_add]
              ring
  have hContr := lt_trans hLowerScaled hUpperScaled
  let P : ℕ :=
    2 ^
      (Critical.beattyIndex F +
        Critical.beattyIndex r0 +
        Critical.beattyIndex r1 +
        Critical.beattyIndex r2)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hContr' : 64 * P < 54 * P := by
    have h := hContr
    dsimp [P] at h ⊢
    simp only [pow_add] at h ⊢
    ring_nf at h ⊢
    exact h
  nlinarith

private theorem five_admissible_lengths_beatty_bound
    (F r0 r1 r2 r3 r4 : ℕ)
    (h0 : IsAdmissibleLength r0)
    (h1 : IsAdmissibleLength r1)
    (h2 : IsAdmissibleLength r2)
    (h3 : IsAdmissibleLength r3)
    (h4 : IsAdmissibleLength r4) :
    Critical.beattyIndex (F + r0 + r1 + r2 + r3 + r4) ≤
      Critical.beattyIndex F +
        Critical.beattyIndex r0 +
        Critical.beattyIndex r1 +
        Critical.beattyIndex r2 +
        Critical.beattyIndex r3 +
        Critical.beattyIndex r4 + 3 := by
  have hScale :=
    admissibleLengths_scale_bound
      (rs := [r0, r1, r2, r3, r4]) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4)
  have hScale' :
      32 * 3 ^ (r0 + r1 + r2 + r3 + r4) ≤
        243 * 2 ^
          (Critical.beattyIndex r0 +
            Critical.beattyIndex r1 +
            Critical.beattyIndex r2 +
            Critical.beattyIndex r3 +
            Critical.beattyIndex r4) := by
    simpa [Nat.add_assoc] using hScale
  have hF := Critical.threePow_lt_twoPow_criticalTwoDepth F
  have hF' :
      3 ^ F < 2 ^ (Critical.beattyIndex F + 1) := by
    simpa [Critical.criticalTwoDepth] using hF
  by_contra hNot
  have hGap :
      Critical.beattyIndex F +
          Critical.beattyIndex r0 +
          Critical.beattyIndex r1 +
          Critical.beattyIndex r2 +
          Critical.beattyIndex r3 +
          Critical.beattyIndex r4 + 4 ≤
        Critical.beattyIndex (F + r0 + r1 + r2 + r3 + r4) := by
    omega
  have hTotalPos : 0 < F + r0 + r1 + r2 + r3 + r4 := by
    have hr0 := h0.1
    omega
  have hLower := Critical.beattyIndex_lower_strict hTotalPos
  have hPowGap :
      2 ^
          (Critical.beattyIndex F +
            Critical.beattyIndex r0 +
            Critical.beattyIndex r1 +
            Critical.beattyIndex r2 +
            Critical.beattyIndex r3 +
            Critical.beattyIndex r4 + 4) ≤
        2 ^ Critical.beattyIndex (F + r0 + r1 + r2 + r3 + r4) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hGap
  have hLowerScaled :
      32 * 2 ^
          (Critical.beattyIndex F +
            Critical.beattyIndex r0 +
            Critical.beattyIndex r1 +
            Critical.beattyIndex r2 +
            Critical.beattyIndex r3 +
            Critical.beattyIndex r4 + 4) <
        32 * 3 ^ (F + r0 + r1 + r2 + r3 + r4) := by
    exact
      (Nat.mul_lt_mul_left (by norm_num : 0 < (32 : ℕ))).2
        (lt_of_le_of_lt hPowGap hLower)
  have hUpperScaled :
      32 * 3 ^ (F + r0 + r1 + r2 + r3 + r4) <
        243 * 2 ^
          (Critical.beattyIndex F + 1 +
            (Critical.beattyIndex r0 +
              Critical.beattyIndex r1 +
              Critical.beattyIndex r2 +
              Critical.beattyIndex r3 +
              Critical.beattyIndex r4)) := by
    calc
      32 * 3 ^ (F + r0 + r1 + r2 + r3 + r4)
          =
          3 ^ F *
            (32 * 3 ^ (r0 + r1 + r2 + r3 + r4)) := by
              rw [show F + r0 + r1 + r2 + r3 + r4 =
                    F + (r0 + r1 + r2 + r3 + r4) by omega,
                pow_add]
              ring
      _ ≤
          3 ^ F *
            (243 * 2 ^
              (Critical.beattyIndex r0 +
                Critical.beattyIndex r1 +
                Critical.beattyIndex r2 +
                Critical.beattyIndex r3 +
                Critical.beattyIndex r4)) :=
            Nat.mul_le_mul_left _ hScale'
      _ <
          2 ^ (Critical.beattyIndex F + 1) *
            (243 * 2 ^
              (Critical.beattyIndex r0 +
                Critical.beattyIndex r1 +
                Critical.beattyIndex r2 +
                Critical.beattyIndex r3 +
                Critical.beattyIndex r4)) := by
            exact
              (Nat.mul_lt_mul_right
                (by positivity :
                  0 < 243 * 2 ^
                    (Critical.beattyIndex r0 +
                      Critical.beattyIndex r1 +
                      Critical.beattyIndex r2 +
                      Critical.beattyIndex r3 +
                      Critical.beattyIndex r4))).2 hF'
      _ =
          243 * 2 ^
            (Critical.beattyIndex F + 1 +
              (Critical.beattyIndex r0 +
                Critical.beattyIndex r1 +
                Critical.beattyIndex r2 +
                Critical.beattyIndex r3 +
                Critical.beattyIndex r4)) := by
              rw [pow_add]
              ring
  have hContr := lt_trans hLowerScaled hUpperScaled
  let P : ℕ :=
    2 ^
      (Critical.beattyIndex F +
        Critical.beattyIndex r0 +
        Critical.beattyIndex r1 +
        Critical.beattyIndex r2 +
        Critical.beattyIndex r3 +
        Critical.beattyIndex r4)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hContr' : 512 * P < 486 * P := by
    have h := hContr
    dsimp [P] at h ⊢
    simp only [pow_add] at h ⊢
    ring_nf at h ⊢
    exact h
  nlinarith

/--
任意の 3 許容 block について、連続 Beatty carry の和は高々 2。
これは純整数版の `AAA` 禁止。
-/
theorem three_admissible_block_carries_le_two
    (F r0 r1 r2 : ℕ)
    (h0 : IsAdmissibleLength r0)
    (h1 : IsAdmissibleLength r1)
    (h2 : IsAdmissibleLength r2) :
    Critical.beattyCarry F r0 +
        Critical.beattyCarry (F + r0) r1 +
        Critical.beattyCarry (F + r0 + r1) r2 ≤ 2 := by
  have hBound :=
    three_admissible_lengths_beatty_bound F r0 r1 r2 h0 h1 h2
  have hEq0 := Critical.beattyIndex_add_eq F r0
  have hEq1 := Critical.beattyIndex_add_eq (F + r0) r1
  have hEq2 := Critical.beattyIndex_add_eq (F + r0 + r1) r2
  omega

/--
任意の 5 許容 block について、連続 Beatty carry の和は高々 3。
これは純整数版の「5 transition 中 A は高々 3 個」。
-/
theorem five_admissible_block_carries_le_three
    (F r0 r1 r2 r3 r4 : ℕ)
    (h0 : IsAdmissibleLength r0)
    (h1 : IsAdmissibleLength r1)
    (h2 : IsAdmissibleLength r2)
    (h3 : IsAdmissibleLength r3)
    (h4 : IsAdmissibleLength r4) :
    Critical.beattyCarry F r0 +
        Critical.beattyCarry (F + r0) r1 +
        Critical.beattyCarry (F + r0 + r1) r2 +
        Critical.beattyCarry (F + r0 + r1 + r2) r3 +
        Critical.beattyCarry (F + r0 + r1 + r2 + r3) r4 ≤ 3 := by
  have hBound :=
    five_admissible_lengths_beatty_bound
      F r0 r1 r2 r3 r4 h0 h1 h2 h3 h4
  have hEq0 := Critical.beattyIndex_add_eq F r0
  have hEq1 := Critical.beattyIndex_add_eq (F + r0) r1
  have hEq2 := Critical.beattyIndex_add_eq (F + r0 + r1) r2
  have hEq3 := Critical.beattyIndex_add_eq (F + r0 + r1 + r2) r3
  have hEq4 := Critical.beattyIndex_add_eq (F + r0 + r1 + r2 + r3) r4
  omega

end IntegerReduction
end Collatz3
