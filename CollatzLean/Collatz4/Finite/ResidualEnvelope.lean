import CollatzLean.Collatz4.Finite.ResidualBounds

/-!
# Collatz4.Finite.ResidualEnvelope

残余語の正確な上側包絡線 `residualGMax` と、語長を忘れた全体包絡線を結ぶ一般層。

`r ≤ E` のとき、残余語の上側包絡線は

`3^(E+1) - 2^(E+2)`

を超えない。これにより、実際の `G` が `residualGMax E r` 以下であることから
全体 envelope の admissibility を導ける。
-/

namespace Collatz4.Finite

/-- 残り2指数 `E` だけで決まる全体 G 包絡線。 -/
def residualGlobalEnvelope (E : ℕ) : ℕ :=
  3 ^ (E + 1) - 2 ^ (E + 2)

/--
正の `d` では `4 * 2^d ≤ 3 * 3^d`。

`d=1` の `8≤9` と `2≤3` だけから得られる基本比較。
-/
private theorem four_mul_two_pow_le_three_mul_three_pow_of_pos
    {d : ℕ} (hd : 0 < d) :
    4 * 2 ^ d ≤ 3 * 3 ^ d := by
  cases d with
  | zero => omega
  | succ k =>
      calc
        4 * 2 ^ (k + 1) = 8 * 2 ^ k := by
          rw [pow_succ]
          ring
        _ ≤ 8 * 3 ^ k := by
          exact Nat.mul_le_mul_left 8
            (Nat.pow_le_pow_left (by norm_num : (2 : ℕ) ≤ 3) k)
        _ ≤ 9 * 3 ^ k := by
          exact Nat.mul_le_mul_right (3 ^ k) (by norm_num : (8 : ℕ) ≤ 9)
        _ = 3 * 3 ^ (k + 1) := by
          rw [pow_succ]
          ring

/--
`r ≤ E` なら、正確な残余上界は全体包絡線以下。

これは `ResidualData` から `qEnvelopeAdmissible` を独立仮定なしで取り出すための核。
-/
theorem residualGMax_le_globalEnvelope_of_le
    {E r : ℕ} (hrE : r ≤ E) :
    residualGMax E r ≤ residualGlobalEnvelope E := by
  by_cases hre : r = E
  · subst r
    by_cases hE0 : E = 0
    · subst E
      norm_num [residualGMax, residualGlobalEnvelope]
    · have hEpos : 0 < E := Nat.pos_of_ne_zero hE0
      have h23 : 2 ^ E ≤ 3 ^ E :=
        Nat.pow_le_pow_left (by norm_num : (2 : ℕ) ≤ 3) E
      have h4 : 4 * 2 ^ E ≤ 3 * 3 ^ E :=
        four_mul_two_pow_le_three_mul_three_pow_of_pos hEpos
      have h3 : 3 ^ (E + 1) = 3 * 3 ^ E := by
        rw [pow_succ]
        ac_rfl
      have h2 : 2 ^ (E + 2) = 4 * 2 ^ E := by
        rw [show E + 2 = (E + 1) + 1 by omega, pow_succ, pow_succ]
        ring
      unfold residualGMax residualGlobalEnvelope
      rw [Nat.sub_self, h3, h2]
      norm_num only [zero_add, pow_two]
      rw [Nat.mul_sub_left_distrib]
      omega
  · have hrlt : r < E := lt_of_le_of_ne hrE hre
    have hd : 0 < E - r := Nat.sub_pos_of_lt hrlt
    have hratio : 4 * 2 ^ (E - r) ≤ 3 * 3 ^ (E - r) :=
      four_mul_two_pow_le_three_mul_three_pow_of_pos hd
    have h23 : 2 ^ r ≤ 3 ^ r :=
      Nat.pow_le_pow_left (by norm_num : (2 : ℕ) ≤ 3) r
    have hA :
        2 ^ (E - r + 2) * 3 ^ r ≤ 3 ^ (E + 1) := by
      have hleft :
          2 ^ (E - r + 2) * 3 ^ r =
            (4 * 2 ^ (E - r)) * 3 ^ r := by
        rw [show E - r + 2 = 2 + (E - r) by omega, pow_add]
        norm_num
      have hfactor : 3 * 3 ^ (E - r) = 3 ^ (E - r + 1) := by
        rw [pow_succ]
        ac_rfl
      have hright :
          (3 * 3 ^ (E - r)) * 3 ^ r = 3 ^ (E + 1) := by
        rw [hfactor, ← pow_add]
        congr 1
        omega
      calc
        2 ^ (E - r + 2) * 3 ^ r
            = (4 * 2 ^ (E - r)) * 3 ^ r := hleft
        _ ≤ (3 * 3 ^ (E - r)) * 3 ^ r :=
          Nat.mul_le_mul_right (3 ^ r) hratio
        _ = 3 ^ (E + 1) := hright
    have hAC :
        2 ^ (E - r + 2) * 2 ^ r = 2 ^ (E + 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hcancel :
        2 ^ (E - r + 2) * (3 ^ r - 2 ^ r) + 2 ^ (E + 2) =
          2 ^ (E - r + 2) * 3 ^ r := by
      rw [Nat.mul_sub_left_distrib, ← hAC]
      exact Nat.sub_add_cancel (Nat.mul_le_mul_left _ h23)
    have hadd :
        residualGMax E r + 2 ^ (E + 2) ≤ 3 ^ (E + 1) := by
      calc
        residualGMax E r + 2 ^ (E + 2)
            ≤ 2 ^ (E - r + 2) * (3 ^ r - 2 ^ r) + 2 ^ (E + 2) :=
          Nat.add_le_add_right (Nat.sub_le _ _) _
        _ = 2 ^ (E - r + 2) * 3 ^ r := hcancel
        _ ≤ 3 ^ (E + 1) := hA
    unfold residualGlobalEnvelope
    omega

/--
正確な残余 G-bound と `r≤E` から、全体包絡線の必要条件を直接得る。
-/
theorem residual_le_globalEnvelope
    {G E r : ℕ}
    (h : ResidualGBounds G E r)
    (hrE : r ≤ E) :
    G ≤ residualGlobalEnvelope E := by
  exact h.upper.trans (residualGMax_le_globalEnvelope_of_le hrE)

end Collatz4.Finite
