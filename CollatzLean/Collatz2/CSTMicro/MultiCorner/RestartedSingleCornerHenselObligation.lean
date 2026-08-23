import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerDefectRecurrence

/-!
# MultiCorner restarted branch: narrowed arithmetic obligation

このファイルだけが未解決点を持つ。

前段では open obligation を arbitrary `(b,w)` から
actual `RestartedTerminalStraightPacket` に限定した。

ここではさらに width `1,2,3` を exact recurrence の直接計算で除去する。

`singleCornerDefect b w` から common dyadic factor

  2^(beattyIndex b - 1)

を外した unit recurrence は

  U_b(0) = 0
  U_b(n+1)
    = 3 U_b(n)
      + 2^n *
          (2^(beattyIndex (b+n) - (beattyIndex b - 1 + n)) - 1)

である。

Beatty index の一段増分は exact に `1` または `2` なので、

* width 1: `U = 1`,
* width 2: `U = 5` または `9`,
* width 3: `U = 19,27,39,55` のいずれか

となる。

したがって respective extra powers

  3^2, 3^3, 3^4

は defect を割らない。

未証明 obligation は `4 ≤ width` の actual restarted packet にだけ残す。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-! ## elementary local arithmetic -/

/-- `3` と `2` は整数環で coprime。 -/
private theorem restarted_three_two_isCoprime :
    IsCoprime (3 : ℤ) (2 : ℤ) := by
  refine ⟨1, -1, ?_⟩
  norm_num

/--
`3^e` と `2^a` は coprime なので、
constant `c` が `3^e` で割れなければ `2^a*c` も割れない。
-/
private theorem restarted_not_threePow_dvd_twoPow_mul_nat
    (e a c : ℕ)
    (hc : ¬ (3 : ℤ) ^ e ∣ (c : ℤ)) :
    ¬ (3 : ℤ) ^ e ∣
      (2 : ℤ) ^ a * (c : ℤ) := by
  intro hDiv
  have hCoprime :
      IsCoprime
        ((3 : ℤ) ^ e)
        ((2 : ℤ) ^ a) := by
    exact restarted_three_two_isCoprime.pow
  have hConst :
      (3 : ℤ) ^ e ∣ (c : ℤ) := by
    exact hCoprime.dvd_of_dvd_mul_left hDiv
  exact hc hConst

/--
Beatty index の一段増分は高々 2。

`3^n ≤ 2^(β_n+1)` を 3 倍し、`3 ≤ 4` を使う。
-/
private theorem restarted_beattyIndex_succ_le_add_two
    (n : ℕ) :
    beattyIndex (n + 1) ≤ beattyIndex n + 2 := by
  apply beattyIndex_le_of_upper
  have hUpper := beattyIndex_upper n
  have hMul :
      3 ^ n * 3 ≤
        2 ^ (beattyIndex n + 1) * 4 := by
    exact Nat.mul_le_mul hUpper (by norm_num)
  calc
    3 ^ (n + 1)
        = 3 ^ n * 3 := by
            rw [pow_succ]
    _ ≤ 2 ^ (beattyIndex n + 1) * 4 := hMul
    _ = 2 ^ ((beattyIndex n + 2) + 1) := by
      calc
        2 ^ (beattyIndex n + 1) * 4
            =
          2 ^ (beattyIndex n + 1) * 2 ^ 2 := by
            norm_num
        _ =
          2 ^ ((beattyIndex n + 1) + 2) := by
            rw [← pow_add]
        _ =
          2 ^ ((beattyIndex n + 2) + 1) := by
            congr 1

/-- Beatty index の一段増分は exact に 1 または 2。 -/
private theorem restarted_beattyIndex_succ_eq_add_one_or_two
    (n : ℕ) :
    beattyIndex (n + 1) = beattyIndex n + 1 ∨
      beattyIndex (n + 1) = beattyIndex n + 2 := by
  have hLower := beattyIndex_lt_succ n
  have hUpper := restarted_beattyIndex_succ_le_add_two n
  omega

/-- defect の dyadic factorization を `ℤ` へ持ち上げた wrapper。 -/
private theorem restarted_singleCornerDefect_cast_eq_pow_mul_unit
    {b n : ℕ}
    (hb : 0 < beattyIndex b) :
    (singleCornerDefect b n : ℤ) =
      (2 : ℤ) ^ (beattyIndex b - 1) *
        (singleCornerDefectUnit b n : ℤ) := by
  exact_mod_cast singleCornerDefect_eq_pow_mul_unit hb n

/-- width 1 の unit は exact に 1。 -/
private theorem restarted_singleCornerDefectUnit_one
    {b : ℕ}
    (hb : 0 < beattyIndex b) :
    singleCornerDefectUnit b 1 = 1 := by
  have hDiff :
      beattyIndex b - (beattyIndex b - 1) = 1 := by
    omega
  simp [singleCornerDefectUnit, hDiff]

/-- first Beatty gap が 1 なら width 2 unit は 5。 -/
private theorem restarted_singleCornerDefectUnit_two_of_gap_one
    {b : ℕ}
    (hb : 0 < beattyIndex b)
    (hGap :
      beattyIndex (b + 1) = beattyIndex b + 1) :
    singleCornerDefectUnit b 2 = 5 := by
  have hU1 := restarted_singleCornerDefectUnit_one hb
  have hLine :
      beattyIndex b - 1 + 1 = beattyIndex b := by
    omega
  change singleCornerDefectUnit b (1 + 1) = 5
  rw [singleCornerDefectUnit_succ, hU1, hLine, hGap]
  norm_num

/-- first Beatty gap が 2 なら width 2 unit は 9。 -/
private theorem restarted_singleCornerDefectUnit_two_of_gap_two
    {b : ℕ}
    (hb : 0 < beattyIndex b)
    (hGap :
      beattyIndex (b + 1) = beattyIndex b + 2) :
    singleCornerDefectUnit b 2 = 9 := by
  have hU1 := restarted_singleCornerDefectUnit_one hb
  have hLine :
      beattyIndex b - 1 + 1 = beattyIndex b := by
    omega
  change singleCornerDefectUnit b (1 + 1) = 9
  rw [singleCornerDefectUnit_succ, hU1, hLine, hGap]
  norm_num

/--
width 3 の unit は二つの Beatty gap の組に応じて
`19,27,39,55` のいずれか。
-/
private theorem restarted_singleCornerDefectUnit_three_cases
    {b : ℕ}
    (hb : 0 < beattyIndex b) :
    singleCornerDefectUnit b 3 = 19 ∨
      singleCornerDefectUnit b 3 = 27 ∨
      singleCornerDefectUnit b 3 = 39 ∨
      singleCornerDefectUnit b 3 = 55 := by
  rcases restarted_beattyIndex_succ_eq_add_one_or_two b with hGap0 | hGap0
  · rcases restarted_beattyIndex_succ_eq_add_one_or_two (b + 1) with hGap1 | hGap1
    · left
      have hU2 :=
        restarted_singleCornerDefectUnit_two_of_gap_one hb hGap0
      have hGap1' :
          beattyIndex (b + 2) = beattyIndex (b + 1) + 1 := by
        simpa [Nat.add_assoc] using hGap1
      have hB2 :
          beattyIndex (b + 2) = beattyIndex b + 2 := by
        omega
      have hLine :
          beattyIndex b - 1 + 2 = beattyIndex b + 1 := by
        omega
      change singleCornerDefectUnit b (2 + 1) = 19
      rw [singleCornerDefectUnit_succ, hU2, hLine, hB2]
      norm_num
      simp
    · right
      left
      have hU2 :=
        restarted_singleCornerDefectUnit_two_of_gap_one hb hGap0
      have hGap1' :
          beattyIndex (b + 2) = beattyIndex (b + 1) + 2 := by
        simpa [Nat.add_assoc] using hGap1
      have hB2 :
          beattyIndex (b + 2) = beattyIndex b + 3 := by
        omega
      have hLine :
          beattyIndex b - 1 + 2 = beattyIndex b + 1 := by
        omega
      change singleCornerDefectUnit b (2 + 1) = 27
      rw [singleCornerDefectUnit_succ, hU2, hLine, hB2]
      norm_num
      simp
  · rcases restarted_beattyIndex_succ_eq_add_one_or_two (b + 1) with hGap1 | hGap1
    · right
      right
      left
      have hU2 :=
        restarted_singleCornerDefectUnit_two_of_gap_two hb hGap0
      have hGap1' :
          beattyIndex (b + 2) = beattyIndex (b + 1) + 1 := by
        simpa [Nat.add_assoc] using hGap1
      have hB2 :
          beattyIndex (b + 2) = beattyIndex b + 3 := by
        omega
      have hLine :
          beattyIndex b - 1 + 2 = beattyIndex b + 1 := by
        omega
      change singleCornerDefectUnit b (2 + 1) = 39
      rw [singleCornerDefectUnit_succ, hU2, hLine, hB2]
      norm_num
      simp
    · right
      right
      right
      have hU2 :=
        restarted_singleCornerDefectUnit_two_of_gap_two hb hGap0
      have hGap1' :
          beattyIndex (b + 2) = beattyIndex (b + 1) + 2 := by
        simpa [Nat.add_assoc] using hGap1
      have hB2 :
          beattyIndex (b + 2) = beattyIndex b + 4 := by
        omega
      have hLine :
          beattyIndex b - 1 + 2 = beattyIndex b + 1 := by
        omega
      change singleCornerDefectUnit b (2 + 1) = 55
      rw [singleCornerDefectUnit_succ, hU2, hLine, hB2]
      norm_num
      simp

/--
actual restarted packet の width `1,2,3` は axiom なしで extra digit を排除できる。
-/
theorem restartedSingleCorner_noExtraThreeAdic_small
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hSmall : S.width ≤ 3) :
    ¬ (3 : ℤ) ^ (S.width + 1) ∣
      (singleCornerDefect S.b S.width : ℤ) := by
  have hWidthPos := S.width_pos
  have hBetaPos := S.beattyIndex_b_pos
  have hCases :
      S.width = 1 ∨ S.width = 2 ∨ S.width = 3 := by
    omega
  rcases hCases with hW | hW
  · intro hExtra
    have hU :=
      restarted_singleCornerDefectUnit_one hBetaPos
    have hCast :=
      restarted_singleCornerDefect_cast_eq_pow_mul_unit
        (b := S.b) (n := 1) hBetaPos
    rw [hU] at hCast
    have hExtra' :
        (3 : ℤ) ^ 2 ∣
          (2 : ℤ) ^ (beattyIndex S.b - 1) * (1 : ℤ) := by
      rw [hW] at hExtra
      simpa [hCast] using hExtra
    exact
      (restarted_not_threePow_dvd_twoPow_mul_nat
        2 (beattyIndex S.b - 1) 1 (by norm_num))
        hExtra'
  · rcases hW with hW | hW
    · intro hExtra
      rcases restarted_beattyIndex_succ_eq_add_one_or_two S.b with hGap | hGap
      · have hU :=
          restarted_singleCornerDefectUnit_two_of_gap_one
            hBetaPos hGap
        have hCast :=
          restarted_singleCornerDefect_cast_eq_pow_mul_unit
            (b := S.b) (n := 2) hBetaPos
        rw [hU] at hCast
        have hExtra' :
            (3 : ℤ) ^ 3 ∣
              (2 : ℤ) ^ (beattyIndex S.b - 1) * (5 : ℤ) := by
          rw [hW] at hExtra
          simpa [hCast] using hExtra
        exact
          (restarted_not_threePow_dvd_twoPow_mul_nat
            3 (beattyIndex S.b - 1) 5 (by norm_num))
            hExtra'
      · have hU :=
          restarted_singleCornerDefectUnit_two_of_gap_two
            hBetaPos hGap
        have hCast :=
          restarted_singleCornerDefect_cast_eq_pow_mul_unit
            (b := S.b) (n := 2) hBetaPos
        rw [hU] at hCast
        have hExtra' :
            (3 : ℤ) ^ 3 ∣
              (2 : ℤ) ^ (beattyIndex S.b - 1) * (9 : ℤ) := by
          rw [hW] at hExtra
          simpa [hCast] using hExtra
        exact
          (restarted_not_threePow_dvd_twoPow_mul_nat
            3 (beattyIndex S.b - 1) 9 (by norm_num))
            hExtra'
    · intro hExtra
      rcases
          restarted_singleCornerDefectUnit_three_cases
            hBetaPos with hU | hU
      · have hCast :=
          restarted_singleCornerDefect_cast_eq_pow_mul_unit
            (b := S.b) (n := 3) hBetaPos
        rw [hU] at hCast
        have hExtra' :
            (3 : ℤ) ^ 4 ∣
              (2 : ℤ) ^ (beattyIndex S.b - 1) * (19 : ℤ) := by
          rw [hW] at hExtra
          simpa [hCast] using hExtra
        exact
          (restarted_not_threePow_dvd_twoPow_mul_nat
            4 (beattyIndex S.b - 1) 19 (by norm_num))
            hExtra'
      · rcases hU with hU | hU
        · have hCast :=
            restarted_singleCornerDefect_cast_eq_pow_mul_unit
              (b := S.b) (n := 3) hBetaPos
          rw [hU] at hCast
          have hExtra' :
              (3 : ℤ) ^ 4 ∣
                (2 : ℤ) ^ (beattyIndex S.b - 1) * (27 : ℤ) := by
            rw [hW] at hExtra
            simpa [hCast] using hExtra
          exact
            (restarted_not_threePow_dvd_twoPow_mul_nat
              4 (beattyIndex S.b - 1) 27 (by norm_num))
              hExtra'
        · rcases hU with hU | hU
          · have hCast :=
              restarted_singleCornerDefect_cast_eq_pow_mul_unit
                (b := S.b) (n := 3) hBetaPos
            rw [hU] at hCast
            have hExtra' :
                (3 : ℤ) ^ 4 ∣
                  (2 : ℤ) ^ (beattyIndex S.b - 1) * (39 : ℤ) := by
              rw [hW] at hExtra
              simpa [hCast] using hExtra
            exact
              (restarted_not_threePow_dvd_twoPow_mul_nat
                4 (beattyIndex S.b - 1) 39 (by norm_num))
                hExtra'
          · have hCast :=
              restarted_singleCornerDefect_cast_eq_pow_mul_unit
                (b := S.b) (n := 3) hBetaPos
            rw [hU] at hCast
            have hExtra' :
                (3 : ℤ) ^ 4 ∣
                  (2 : ℤ) ^ (beattyIndex S.b - 1) * (55 : ℤ) := by
              rw [hW] at hExtra
              simpa [hCast] using hExtra
            exact
              (restarted_not_threePow_dvd_twoPow_mul_nat
                4 (beattyIndex S.b - 1) 55 (by norm_num))
                hExtra'

/-! ## remaining open obligation -/

/--
restarted Case I に残る唯一の未証明算術補題。

width `1,2,3` は上で theorem として消去済み。
したがって open obligation は actual restarted packet かつ
`4 ≤ S.width` の場合だけに限定する。
-/
axiom restartedSingleCorner_noExtraThreeAdic_large
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : 4 ≤ S.width) :
    ¬ (3 : ℤ) ^ (S.width + 1) ∣
      (singleCornerDefect S.b S.width : ℤ)

end MultiCorner
end CSTMicro
end Collatz2
