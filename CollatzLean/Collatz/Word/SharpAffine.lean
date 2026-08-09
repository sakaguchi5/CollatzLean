import CollatzLean.Collatz.Word.Geometry

/-!
# 有限語のsharp affine bounds

proper-prefix expanding と all-suffix contracting から得られる
二つのsharp affine budgetを有限語層へ戻す。
-/

namespace Collatz
namespace Word

/-- WeightedPrefixBoundの長さ0 prefixから先頭係数のboundを得る。 -/
private theorem weightedPrefixBound_head_le
    (e : ℕ) (w : Collatz.Word) (a c : ℕ)
    (h : WeightedPrefixBound a c (e :: w)) :
    a ≤ c := by
  have hh := h 0 (by simp)
  simpa [WeightedPrefixBound, twoSteps] using hh

/-- cons語のWeightedPrefixBoundをtailへ移す。 -/
private theorem weightedPrefixBound_tail
    (e : ℕ) (w : Collatz.Word) (a c : ℕ)
    (h : WeightedPrefixBound a c (e :: w)) :
    WeightedPrefixBound (a * 2 ^ e) (c * 3) w := by
  intro j hj
  have hh := h (j + 1) (by simp; omega)
  simpa [WeightedPrefixBound, List.take_succ_cons, twoSteps_cons,
    pow_add, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

private theorem three_pow_length_eq_mul_pred
    (w : Collatz.Word) (hw : w ≠ []) :
    3 ^ w.length = 3 * 3 ^ (w.length - 1) := by
  have hwpos : 0 < w.length :=
    List.length_pos_of_ne_nil hw
  have hlen :
      w.length = (w.length - 1) + 1 := by
    omega
  conv_lhs =>
    rw [hlen, pow_succ]
  exact Nat.mul_comm _ _

/-- sharp weighted affine boundのcons step。 -/
private theorem weighted_affineConst_cons_step
    (e : ℕ) (w : Collatz.Word) (a c : ℕ)
    (hw : w ≠ [])
    (h0 : a ≤ c)
    (hi :
      (a * 2 ^ e) * w.affineConst ≤
        w.length * (c * 3) * 3 ^ (w.length - 1)) :
    a * affineConst (e :: w) ≤
      (e :: w).length * c * 3 ^ ((e :: w).length - 1) := by
  have hhead : a * 3 ^ w.length ≤ c * 3 ^ w.length :=
    Nat.mul_le_mul_right (3 ^ w.length) h0
  have hpow := three_pow_length_eq_mul_pred w hw
  calc
    a * affineConst (e :: w)
        = a * 3 ^ w.length + (a * 2 ^ e) * w.affineConst := by
            simp [affineConst]
            ring
    _ ≤ c * 3 ^ w.length +
          w.length * (c * 3) * 3 ^ (w.length - 1) :=
      Nat.add_le_add hhead hi
    _ = (w.length + 1) * c * 3 ^ w.length := by
      rw [hpow]
      ring
    _ = (e :: w).length * c * 3 ^ ((e :: w).length - 1) := by simp

/-- WeightedPrefixBoundから余分な3倍のないsharp affine boundを得る。 -/
theorem WeightedPrefixBound.affineConst_le_sharp
    {w : Collatz.Word} {a c : ℕ}
    (h : WeightedPrefixBound a c w) :
    a * w.affineConst ≤ w.length * c * 3 ^ (w.length - 1) := by
  induction w generalizing a c with
  | nil => simp [affineConst]
  | cons e w ih =>
      have h0 : a ≤ c := weightedPrefixBound_head_le e w a c h
      by_cases hw : w = []
      · subst w
        simpa [affineConst] using h0
      · have htail : WeightedPrefixBound (a * 2 ^ e) (c * 3) w :=
          weightedPrefixBound_tail e w a c h
        have hi := ih (a := a * 2 ^ e) (c := c * 3) htail
        exact weighted_affineConst_cons_step e w a c hw h0 hi

/-- proper-prefix expanding語のsharp affine bound。 -/
theorem ProperPrefixesExpanding.affineConst_le_sharp
    {w : Collatz.Word}
    (h : w.ProperPrefixesExpanding) :
    w.affineConst ≤ w.length * 3 ^ (w.length - 1) := by
  have hb := h.weightedPrefixBound.affineConst_le_sharp
  simpa using hb

/-- first crossing語のsharp affine bound。 -/
theorem FirstCrossing.affineConst_le_sharp
    {w : Collatz.Word} (h : FirstCrossing w) :
    w.affineConst ≤ w.length * 3 ^ (w.length - 1) :=
  h.properExpanding.affineConst_le_sharp

/-- contracting cons語のhead項評価。 -/
private theorem contracting_cons_head_bound
    {e : ℕ} {w : Collatz.Word}
    (hWhole : Contracting (e :: w)) :
    3 * 3 ^ w.oddSteps < 2 ^ (e + w.twoSteps) := by
  unfold Contracting at hWhole
  simpa [pow_succ, Nat.mul_comm] using hWhole

/-- tailのsharp評価をhead指数ぶんscaleする。 -/
private theorem three_mul_affineConst_tail_scaled
    (e : ℕ) {w : Collatz.Word}
    (hi : 3 * w.affineConst < w.length * 2 ^ w.twoSteps) :
    3 * (2 ^ e * w.affineConst) <
      w.length * 2 ^ (e + w.twoSteps) := by
  have hpowPos : 0 < 2 ^ e := Nat.pow_pos (by omega)
  have hmul := (Nat.mul_lt_mul_left hpowPos).2 hi
  simpa [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

/-- all-suffix sharp評価のcons step。 -/
private theorem three_mul_affineConst_cons_step
    {e : ℕ} {w : Collatz.Word}
    (hWhole : Contracting (e :: w))
    (hi : 3 * w.affineConst < w.length * 2 ^ w.twoSteps) :
    3 * affineConst (e :: w) <
      (e :: w).length * 2 ^ twoSteps (e :: w) := by
  have hHead := contracting_cons_head_bound hWhole
  have hTailScaled := three_mul_affineConst_tail_scaled e hi
  calc
    3 * affineConst (e :: w)
        = 3 * 3 ^ w.oddSteps + 3 * (2 ^ e * w.affineConst) := by
            simp [affineConst, oddSteps]
            ring
    _ < 2 ^ (e + w.twoSteps) + w.length * 2 ^ (e + w.twoSteps) := by omega
    _ = (e :: w).length * 2 ^ twoSteps (e :: w) := by
      simp only [List.length_cons, twoSteps_cons]
      ring

/-- 全非空suffixがcontractingな非空語では`3B < length*2^H`。 -/
theorem AllSuffixesContracting.three_mul_affineConst_lt
    {w : Collatz.Word}
    (h : AllSuffixesContracting w) (hne : w ≠ []) :
    3 * affineConst w < w.length * 2 ^ twoSteps w := by
  revert hne h
  induction w with
  | nil =>
      intro h _
      contradiction
  | cons e w ih =>
      intro hAll _
      change Contracting (e :: w) ∧ AllSuffixesContracting w at hAll
      rcases hAll with ⟨hWhole, hTail⟩
      by_cases hw : w = []
      · subst w
        simpa [Contracting, oddSteps, twoSteps, affineConst] using hWhole
      · exact three_mul_affineConst_cons_step
          hWhole
          (ih hTail hw)

/-- valid語のscaled affine budget: `2^p B ≤ 3^p 2^H`。 -/
theorem Valid.twoPow_length_mul_affineConst_le
    {w : Collatz.Word} (hvalid : Valid w) :
    2 ^ oddSteps w * affineConst w ≤
      3 ^ oddSteps w * 2 ^ twoSteps w := by
  revert hvalid
  induction w with
  | nil =>
      intro _
      simp [oddSteps, twoSteps, affineConst]
  | cons e w ih =>
      intro hvalid
      have he : 0 < e := by
        exact hvalid e (by simp)
      have hw : Valid w := by
        intro a ha
        exact hvalid a (by simp [ha])
      have hih :
          2 ^ oddSteps w * affineConst w ≤
            3 ^ oddSteps w * 2 ^ twoSteps w :=
        ih hw
      have hlen : oddSteps w ≤ twoSteps w :=
        oddSteps_le_twoSteps hw
      have hexp :
          oddSteps w + 1 ≤ e + twoSteps w := by
        omega
      have hpow :
          2 ^ (oddSteps w + 1) ≤
            2 ^ (e + twoSteps w) := by
        exact Nat.pow_le_pow_right (n := 2) (by omega) hexp
      have hhead :
          2 ^ (oddSteps w + 1) * 3 ^ oddSteps w ≤
            3 ^ oddSteps w * 2 ^ (e + twoSteps w) := by
        have h :=
          Nat.mul_le_mul_left (3 ^ oddSteps w) hpow
        simpa [Nat.mul_comm] using h
      have htail0 :
          2 ^ (e + 1) *
              (2 ^ oddSteps w * affineConst w) ≤
            2 ^ (e + 1) *
              (3 ^ oddSteps w * 2 ^ twoSteps w) :=
        Nat.mul_le_mul_left (2 ^ (e + 1)) hih
      have htail :
          2 ^ (oddSteps w + 1) *
              (2 ^ e * affineConst w) ≤
            (2 * 3 ^ oddSteps w) *
              2 ^ (e + twoSteps w) := by
        simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htail0
      change
        2 ^ (oddSteps w + 1) *
            (3 ^ oddSteps w + 2 ^ e * affineConst w) ≤
          3 ^ (oddSteps w + 1) *
            2 ^ (e + twoSteps w)
      calc
        2 ^ (oddSteps w + 1) *
            (3 ^ oddSteps w + 2 ^ e * affineConst w)
            =
          2 ^ (oddSteps w + 1) * 3 ^ oddSteps w +
            2 ^ (oddSteps w + 1) *
              (2 ^ e * affineConst w) := by
                ring
        _ ≤
          3 ^ oddSteps w * 2 ^ (e + twoSteps w) +
            (2 * 3 ^ oddSteps w) *
              2 ^ (e + twoSteps w) :=
          Nat.add_le_add hhead htail
        _ =
          3 ^ (oddSteps w + 1) *
            2 ^ (e + twoSteps w) := by
              rw [Nat.pow_add_one]
              ring

/-- 連続二prefixがともにexpandingなら得られる`7/4`整数bound。 -/
theorem prefixPair_seven_fourths_bound
    {j H e : ℕ}
    (he : 0 < e)
    (h0 : 2 ^ H < 3 ^ j)
    (h1 : 2 ^ (H + e) < 3 ^ (j + 1)) :
    4 * (3 * 2 ^ H + 2 ^ (H + e)) < 7 * 3 ^ (j + 1) := by
  by_cases heOne : e = 1
  · subst e
    have h20 : 20 * 2 ^ H < 20 * 3 ^ j :=
      (Nat.mul_lt_mul_left (by omega : 0 < 20)).2 h0
    have hpos : 0 < 3 ^ j := Nat.pow_pos (by omega)
    simp only [pow_succ]
    nlinarith
  · have heTwo : 2 ≤ e := by omega
    have hpowFour : 4 ≤ 2 ^ e := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heTwo
    have hA : 4 * 2 ^ H ≤ 2 ^ (H + e) := by
      rw [pow_add]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2 ^ H) hpowFour
    have hA3 : 4 * 2 ^ H < 3 * 3 ^ j := by
      exact lt_of_le_of_lt hA (by simpa [pow_succ, Nat.mul_comm] using h1)
    have hB : 4 * 2 ^ (H + e) < 12 * 3 ^ j := by
      calc
        4 * 2 ^ (H + e) < 4 * 3 ^ (j + 1) :=
          (Nat.mul_lt_mul_left (by omega : 0 < 4)).2 h1
        _ = 12 * 3 ^ j := by rw [pow_succ]; ring
    nlinarith

end Word
end Collatz
