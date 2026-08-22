import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerWholeRunDyadic

set_option linter.style.emptyLine false

/-!
# Pure B single-corner finite residue: sharp seed から width <= 112

このファイルは `m <= 6465` で使う purely elementary な有限側の指数比較を固定する。

sharp seed を `ell=13` に特殊化すると

  2^(n-1) <= 8*n^14*2^13.

一方 `n=113` では exact に

  8*113^14*2^13 < 2^112.

さらに `n>=113` では

  (n+1)^14 < 2*n^14

なので、一度 dyadic side が勝てば以後ずっと勝ち続ける。従って sharp seed を
満たす `n` は必ず `n<=112`。

前ファイルの `singleCorner_actual_dyadicSeed` と組み合わせると、残る local target
`SingleCornerLocalRhin14Bound` だけから actual single-corner width `<=112` が得られる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `n>=113` では 14 次冪は一段進んでも 2 倍未満。 -/
theorem add_one_pow14_lt_two_mul_pow14
    {n : ℕ}
    (hn : 113 ≤ n) :
    (n + 1) ^ 14 < 2 * n ^ 14 := by
  have hScale : 113 * (n + 1) ≤ 114 * n := by
    omega
  have hPow := Nat.pow_le_pow_left hScale 14
  rw [mul_pow, mul_pow] at hPow

  have hRatio : 114 ^ 14 < 2 * 113 ^ 14 := by
    norm_num
  have hnPowPos : 0 < n ^ 14 := by
    positivity
  have hRatioMul :=
    Nat.mul_lt_mul_of_pos_right hRatio hnPowPos

  have hCombined :
      113 ^ 14 * (n + 1) ^ 14 <
        113 ^ 14 * (2 * n ^ 14) := by
    calc
      113 ^ 14 * (n + 1) ^ 14
          ≤ 114 ^ 14 * n ^ 14 := hPow
      _ < (2 * 113 ^ 14) * n ^ 14 := hRatioMul
      _ = 113 ^ 14 * (2 * n ^ 14) := by ring

  exact
    (Nat.mul_lt_mul_left (by positivity : 0 < 113 ^ 14)).mp hCombined

/--
`n=113+d` では sharp-seed の polynomial side は常に dyadic side より strict に小さい。
-/
theorem eight_mul_add_113_pow14_mul_pow13_lt_pow_pred
    (d : ℕ) :
    8 * (113 + d) ^ 14 * 2 ^ 13 <
      2 ^ (113 + d - 1) := by
  induction d with
  | zero =>
      norm_num
  | succ d ih =>
      let n : ℕ := 113 + d
      have hn : 113 ≤ n := by
        dsimp [n]
        omega
      have hPoly : (n + 1) ^ 14 < 2 * n ^ 14 :=
        add_one_pow14_lt_two_mul_pow14 hn
      have hLeft0 :=
        Nat.mul_lt_mul_of_pos_left hPoly (by norm_num : 0 < 8)
      have hLeft1 :=
        Nat.mul_lt_mul_of_pos_right hLeft0
          (by positivity : 0 < 2 ^ 13)
      have hLeft :
          8 * (n + 1) ^ 14 * 2 ^ 13 <
            2 * (8 * n ^ 14 * 2 ^ 13) := by
        calc
          8 * (n + 1) ^ 14 * 2 ^ 13
              < 8 * (2 * n ^ 14) * 2 ^ 13 := hLeft1
          _ = 2 * (8 * n ^ 14 * 2 ^ 13) := by ring

      have hIH :
          8 * n ^ 14 * 2 ^ 13 < 2 ^ (n - 1) := by
        simpa [n] using ih
      have hDoubleIH :=
        Nat.mul_lt_mul_of_pos_left hIH (by norm_num : 0 < 2)

      have hPowStep : 2 * 2 ^ (n - 1) = 2 ^ n := by
        have hnPos : 0 < n := by omega
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        ring_nf
        simp

      have hMain :
          8 * (n + 1) ^ 14 * 2 ^ 13 < 2 ^ n := by
        calc
          8 * (n + 1) ^ 14 * 2 ^ 13
              < 2 * (8 * n ^ 14 * 2 ^ 13) := hLeft
          _ < 2 * 2 ^ (n - 1) := hDoubleIH
          _ = 2 ^ n := hPowStep

      have hIndex : 113 + (d + 1) = n + 1 := by
        dsimp [n]
        omega
      rw [hIndex]
      have hPred : n + 1 - 1 = n := by omega
      rw [hPred]
      exact hMain

/-- `ell=13` の sharp seed は `n<=112` を強制する。 -/
theorem width_le_112_of_dyadicSeed13
    {n : ℕ}
    (hSeed :
      2 ^ (n - 1) ≤ 8 * n ^ 14 * 2 ^ 13) :
    n ≤ 112 := by
  by_contra hnot
  have hn : 113 ≤ n := by omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hStrict :=
    eight_mul_add_113_pow14_mul_pow13_lt_pow_pred d
  exact (Nat.not_lt_of_ge hSeed) hStrict

namespace MinimalActualABObstructionPacket

/--
`m<=6465` かつ local Rhin target が成り立てば actual single-corner width は `112` 以下。

ここで local target 以外はすべて既存 actual realization と整数算術から証明されている。
-/
theorem singleCorner_width_le_112_of_m_le_6465
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hm :
      (M.toPureBProfileObstruction hL).m ≤ 6465)
    (hLocal : M.SingleCornerLocalRhin14Bound hL S 13) :
    S.width ≤ 112 := by
  have hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ 13 := by
    norm_num
    omega
  have hSeed :=
    M.singleCorner_actual_dyadicSeed hL S hmSize hLocal
  exact width_le_112_of_dyadicSeed13 hSeed

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
