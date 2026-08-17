import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BoundaryACandidate
import CollatzLean.Collatz2.External.TwoThreeGap

/-!
# Step 7: a Rhin-type integer corollary -> K = 16384, A = 14

Rhin の explicit linear-form lower boundそのものをこのファイルで再証明はしない。
代わりに、そこから得るべき安全な pure-integer corollary

  3^p < 2^H
  -> 3^p <= H^14 * (2^H - 3^p)

だけを外部 interface にする。

この corollary から Boundary A が要求する

  3^p <= 16384 * (p+1)^14 * (2^H - 3^p)

を Lean 内で導く。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- Boundary A で固定して使う安全な Rhin constants。 -/
def rhinGapK : ℕ := 16384

def rhinGapA : ℕ := 14

/--
Rhin `13.3` 型評価から丸めて得る pure-integer power-gap corollary。
この一 field が Step 7 の genuinely external input。
-/
structure RhinTwoThreePowerGap14 where
  relative_by_H :
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤ H ^ 14 * (2 ^ H - 3 ^ p)

private theorem natPow_le_natPow_of_le
    {a b : ℕ}
    (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul (natPow_le_natPow_of_le hab n) hab

private theorem threePow_lt_fourPow_of_pos
    {p : ℕ}
    (hp : 0 < p) :
    3 ^ p < 4 ^ p := by
  exact Nat.pow_lt_pow_left (by omega) (by omega)

namespace RhinTwoThreePowerGap14

/--
gap 自体が `3^p` 以上なら、polynomial factor の大きさによらず
Boundary A の relative gap bound は直ちに従う。
-/
theorem boundary_gap_of_gap_large
    {p H : ℕ}
    (hGapLarge : 3 ^ p ≤ 2 ^ H - 3 ^ p) :
    3 ^ p ≤
      rhinGapK * (p + 1) ^ rhinGapA *
        (2 ^ H - 3 ^ p) := by
  have hCoeff :
      1 ≤ rhinGapK * (p + 1) ^ rhinGapA := by
    have hCoeffPos :
        0 < rhinGapK * (p + 1) ^ rhinGapA := by
      unfold rhinGapK rhinGapA
      positivity
    omega
  calc
    3 ^ p ≤ 2 ^ H - 3 ^ p := hGapLarge
    _ = 1 * (2 ^ H - 3 ^ p) := by simp
    _ ≤
        (rhinGapK * (p + 1) ^ rhinGapA) *
          (2 ^ H - 3 ^ p) :=
      Nat.mul_le_mul_right (2 ^ H - 3 ^ p) hCoeff


/--
`2^H - 3^p < 3^p` という small-gap regime では、
指数 `H` は `2p` 以下に抑えられる。

もし `H ≥ 2p+1` なら
`2^H ≥ 2 * 4^p > 2 * 3^p`
となり、small-gap 条件と矛盾する。
-/
theorem exponent_le_twice_of_small_gap
    {p H : ℕ}
    (hp : 0 < p)
    (hPow : 3 ^ p < 2 ^ H)
    (hGapSmall : 2 ^ H - 3 ^ p < 3 ^ p) :
    H ≤ 2 * p := by
  by_contra hnot
  have hHbig :
      2 * p + 1 ≤ H := by
    omega
  have hPowMono :
      2 ^ (2 * p + 1) ≤ 2 ^ H :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      hHbig
  have hFour :
      3 ^ p < 4 ^ p :=
    threePow_lt_fourPow_of_pos hp
  have hTwoFour : 2 * 3 ^ p < 2 * 4 ^ p := by
    exact Nat.mul_lt_mul_of_pos_left hFour (by decide)
  have hPowEq :
      2 ^ (2 * p + 1) = 2 * 4 ^ p := by
    calc
      2 ^ (2 * p + 1)
          = 2 ^ (2 * p) * 2 := by
              rw [pow_succ]
      _ = (2 ^ 2) ^ p * 2 := by
            rw [pow_mul]
      _ = 4 ^ p * 2 := by
            norm_num
      _ = 2 * 4 ^ p := by
            omega
  have hSum :
      2 ^ H = 3 ^ p + (2 ^ H - 3 ^ p) := by
    omega
  have hUpper :
      2 ^ H < 2 * 3 ^ p := by
    rw [hSum]
    omega
  rw [hPowEq] at hPowMono
  omega


/--
small-gap regime で得られる `H ≤ 2p` を用いて、
Rhin の `H^14` factor を Boundary A 用の
`rhinGapK * (p+1)^rhinGapA` に丸める。
-/
theorem rhin_H_power_le_boundary_factor
    {p H : ℕ}
    (hHle : H ≤ 2 * p) :
    H ^ 14 ≤
      rhinGapK * (p + 1) ^ rhinGapA := by
  have hHbase :
      H ≤ 2 * (p + 1) := by
    omega
  have hHpow :
      H ^ 14 ≤ (2 * (p + 1)) ^ 14 :=
    natPow_le_natPow_of_le hHbase 14
  calc
    H ^ 14
        ≤ (2 * (p + 1)) ^ 14 := hHpow
    _ = 2 ^ 14 * (p + 1) ^ 14 := by
          rw [mul_pow]
    _ = rhinGapK * (p + 1) ^ rhinGapA := by
          norm_num [rhinGapK, rhinGapA]


/--
small-gap regime では `H ≤ 2p` により Rhin の H-based bound を
Boundary A の p-based polynomial relative gap に変換できる。
-/
theorem boundary_gap_of_gap_small
    (R : RhinTwoThreePowerGap14)
    {p H : ℕ}
    (hp : 0 < p)
    (hPow : 3 ^ p < 2 ^ H)
    (hGapSmall : 2 ^ H - 3 ^ p < 3 ^ p) :
    3 ^ p ≤
      rhinGapK * (p + 1) ^ rhinGapA *
        (2 ^ H - 3 ^ p) := by
  have hHle :
      H ≤ 2 * p :=
    exponent_le_twice_of_small_gap
      hp hPow hGapSmall
  have hR :=
    R.relative_by_H p H hp hPow
  have hFactor :
      H ^ 14 ≤
        rhinGapK * (p + 1) ^ rhinGapA :=
    rhin_H_power_le_boundary_factor hHle
  calc
    3 ^ p
        ≤ H ^ 14 * (2 ^ H - 3 ^ p) := by
            simpa using hR
    _ ≤
        (rhinGapK * (p + 1) ^ rhinGapA) *
          (2 ^ H - 3 ^ p) :=
      Nat.mul_le_mul_right
        (2 ^ H - 3 ^ p) hFactor


/--
Rhin の H-based bound を Boundary A の
p-based polynomial relative gap へ丸める。

gap が `3^p` 以上なら自明な大 gap branch で閉じ、
それ未満なら `H ≤ 2p` を経由して Rhin bound を移送する。
-/
theorem boundary_gap
    (R : RhinTwoThreePowerGap14) :
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤
        rhinGapK * (p + 1) ^ rhinGapA *
          (2 ^ H - 3 ^ p) := by
  intro p H hp hPow
  by_cases hGapLarge :
      3 ^ p ≤ 2 ^ H - 3 ^ p
  · exact boundary_gap_of_gap_large hGapLarge
  · have hGapSmall :
        2 ^ H - 3 ^ p < 3 ^ p := by
      omega
    exact
      boundary_gap_of_gap_small
        R hp hPow hGapSmall

/-- existing external interface も `(K,A)=(16384,14)` で構成できる。 -/
theorem toTwoThreeGapPolynomialBound
    (R : RhinTwoThreePowerGap14) :
    Collatz2.External.TwoThreeGapPolynomialBound := by
  refine ⟨rhinGapK, rhinGapA, ?_, ?_⟩
  · norm_num [rhinGapK]
  · exact R.boundary_gap

end RhinTwoThreePowerGap14

end ExternalArithmetic
end CSTMicro
end Collatz2
