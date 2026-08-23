import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFactorRepeat

/-!
# Restarted suffix Hensel: nonzero repeated block の large-width 排除

`RestartedSuffixHenselFactorRepeat` により、`2*m+1 <= width` なら actual restarted
Hensel chain 内に length `m` の `SameDeltaOffsetBlock` が必ず存在する。

本ファイルではその repeated block の scaled difference

  M_0 = Q_j - 2^Delta Q_i,   Q_i = q_i + 1

が nonzero である場合を size comparison だけで排除する。

核心は次の二つ。

* repeated block arithmetic から `2^m | M_0`。従って `M_0 != 0` なら
  `|M_0| >= 2^m`。
* actual Beatty staircase と suffix recurrence から

    3 * Q_i <= 2^(delta_i-1) * (4*(width-i)+3).

さらに repeat start `j <= m+1` と Beatty displacement bound を合わせると

    4^m <= (4*width+3) * 3^m

が必要になる。

`m = (width-1)/2` と取れば、この不等式は `width >= 37` で破れる。
従って large-width では forced repeat は必ず zero-scaled-state branch に入る。

ここでは zero branch 自体は排除しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RestartedTerminalStraightPacket

/-! ## Beatty displacement から得る term bound -/

/--
actual Hensel gap の offset growth は Beatty displacement の一段 carry で抑えられる。

  r + delta_(i+r) <= delta_i + beta(r) + 1.
-/
theorem suffixHenselDelta_add_offset_le
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i r : ℕ) :
    r + S.suffixHenselDelta (i + r) <=
      S.suffixHenselDelta i + beattyIndex r + 1 := by
  have h0 := S.suffixHenselBase_add_delta_eq_beattyIndex i
  have h1 := S.suffixHenselBase_add_delta_eq_beattyIndex (i + r)
  have hBase := S.suffixHenselBase_add i r
  rcases
      beattyIndex_add_eq_add_or_add_one (S.b + i) r with hNo | hCarry
  · have hBeatty :
        beattyIndex (S.b + (i + r)) =
          beattyIndex (S.b + i) + beattyIndex r := by
      simpa [Nat.add_assoc] using hNo
    rw [hBase] at h1
    rw [hBeatty] at h1
    omega
  · have hBeatty :
        beattyIndex (S.b + (i + r)) =
          beattyIndex (S.b + i) + beattyIndex r + 1 := by
      simpa [Nat.add_assoc] using hCarry
    rw [hBase] at h1
    rw [hBeatty] at h1
    omega

/-- suffix forcing term は nonnegative。 -/
theorem suffixHenselForcing_nonneg
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    0 <= S.suffixHenselForcing i := by
  rw [S.suffixHenselForcing_eq i]
  have hPow : 1 <= (2 : ℤ) ^ S.suffixHenselDelta i := by
    have hPos : 0 < (2 : ℤ) ^ S.suffixHenselDelta i := by positivity
    omega
  linarith

/-- suffix forcing term は `2^delta` 以下。 -/
theorem suffixHenselForcing_le_pow
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    S.suffixHenselForcing i <=
      (2 : ℤ) ^ S.suffixHenselDelta i := by
  rw [S.suffixHenselForcing_eq i]
  linarith

/--
一列 forcing の weighted term を entrance level `delta_i` で一様に抑える。
-/
theorem suffixHenselWeightedForcing_le
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i r : ℕ) :
    (2 : ℤ) ^ r * S.suffixHenselForcing (i + r) <=
      4 * (2 : ℤ) ^ (S.suffixHenselDelta i - 1) * (3 : ℤ) ^ r := by
  have hDeltaPos : 0 < S.suffixHenselDelta i :=
    S.suffixHenselDelta_pos i
  have hExp := S.suffixHenselDelta_add_offset_le i r
  have hPowMonoNat :
      2 ^ (r + S.suffixHenselDelta (i + r)) <=
        2 ^ (S.suffixHenselDelta i + beattyIndex r + 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExp
  have hBeta := beattyIndex_lower r
  have hRightNat :
      2 ^ (S.suffixHenselDelta i + beattyIndex r + 1) <=
        4 * 2 ^ (S.suffixHenselDelta i - 1) * 3 ^ r := by
    have hPowId :
        2 ^ (S.suffixHenselDelta i + beattyIndex r + 1) =
          4 * 2 ^ (S.suffixHenselDelta i - 1) *
            2 ^ beattyIndex r := by
      have hDeltaId :
          S.suffixHenselDelta i =
            (S.suffixHenselDelta i - 1) + 1 := by
        omega
      calc
        2 ^ (S.suffixHenselDelta i + beattyIndex r + 1)
            =
          2 ^ (((S.suffixHenselDelta i - 1) + 1) +
            beattyIndex r + 1) := by
              rw [hDeltaId]
              simp
        _ =
          2 ^ ((S.suffixHenselDelta i - 1) +
            (beattyIndex r + 2)) := by
              congr 1
              omega
        _ =
          2 ^ (S.suffixHenselDelta i - 1) *
            2 ^ (beattyIndex r + 2) := by
              rw [pow_add]
        _ =
          2 ^ (S.suffixHenselDelta i - 1) *
            (2 ^ beattyIndex r * 2 ^ 2) := by
              rw [pow_add]
        _ =
          4 * 2 ^ (S.suffixHenselDelta i - 1) *
            2 ^ beattyIndex r := by
              norm_num
              ring
    rw [hPowId]
    exact Nat.mul_le_mul_left
      (4 * 2 ^ (S.suffixHenselDelta i - 1)) hBeta
  have hPowNat :
      2 ^ r * 2 ^ S.suffixHenselDelta (i + r) <=
        4 * 2 ^ (S.suffixHenselDelta i - 1) * 3 ^ r := by
    rw [← pow_add]
    exact le_trans hPowMonoNat hRightNat
  have hForce := S.suffixHenselForcing_le_pow (i + r)
  have hTwoNonneg : 0 <= (2 : ℤ) ^ r := by positivity
  have hMul := mul_le_mul_of_nonneg_left hForce hTwoNonneg
  have hPowCast :
      (2 : ℤ) ^ r * (2 : ℤ) ^ S.suffixHenselDelta (i + r) <=
        4 * (2 : ℤ) ^ (S.suffixHenselDelta i - 1) * (3 : ℤ) ^ r := by
    exact_mod_cast hPowNat
  exact le_trans hMul hPowCast

/-! ## suffix unit / quotient の linear normalized bound -/

/--
長さ `r+1` の suffix unit は

  4*(r+1)*2^(delta_i-1)*3^r

以下。
-/
theorem suffixHenselUnit_succ_nonneg_and_le
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i r : ℕ) :
    0 <= S.suffixHenselUnit i (r + 1) ∧
    S.suffixHenselUnit i (r + 1) <=
      4 * (r + 1 : ℤ) *
        (2 : ℤ) ^ (S.suffixHenselDelta i - 1) * (3 : ℤ) ^ r := by
  induction r with
  | zero =>
      have hRec := S.suffixHenselUnit_succ i 0
      have hForceNonneg := S.suffixHenselForcing_nonneg i
      have hTerm := S.suffixHenselWeightedForcing_le i 0
      constructor
      · rw [hRec]
        simp only [suffixHenselUnit_zero, mul_zero, pow_zero, add_zero, one_mul, zero_add]
        exact hForceNonneg
      · rw [hRec]
        simp
        simpa using hTerm
  | succ r ih =>
      have hRec := S.suffixHenselUnit_succ i (r + 1)
      have hForceNonneg := S.suffixHenselForcing_nonneg (i + (r + 1))
      have hTerm := S.suffixHenselWeightedForcing_le i (r + 1)
      have hThreeNonneg : 0 <= (3 : ℤ) := by norm_num
      have hPowNonneg : 0 <= (2 : ℤ) ^ (r + 1) := by positivity
      constructor
      · rw [hRec]
        exact add_nonneg
          (mul_nonneg hThreeNonneg ih.1)
          (mul_nonneg hPowNonneg hForceNonneg)
      · rw [hRec]
        calc
          3 * S.suffixHenselUnit i (r + 1) +
              (2 : ℤ) ^ (r + 1) * S.suffixHenselForcing (i + (r + 1))
              <=
            3 *
                (4 * (r + 1 : ℤ) *
                  (2 : ℤ) ^ (S.suffixHenselDelta i - 1) * (3 : ℤ) ^ r) +
              4 * (2 : ℤ) ^ (S.suffixHenselDelta i - 1) * (3 : ℤ) ^ (r + 1) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left ih.2 (by norm_num))
                  hTerm
          _ =
            4 * (r + 2 : ℤ) *
              (2 : ℤ) ^ (S.suffixHenselDelta i - 1) * (3 : ℤ) ^ (r + 1) := by
                rw [pow_succ]
                ring

/-- actual suffix quotient は nonnegative。 -/
theorem suffixHenselQuotient_nonneg
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < S.width) :
    0 <= S.suffixHenselQuotient hStart i := by
  let n := S.width - i
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnPos)
  have hUnit := S.suffixHenselUnit_succ_nonneg_and_le i r
  have hSpec := S.suffixHenselQuotient_spec hStart (i := i) (Nat.le_of_lt hi)
  have hr' : S.width - i = r + 1 := by
    simpa [n, Nat.succ_eq_add_one] using hr
  have hSpec' :
      S.suffixHenselUnit i (r + 1) =
        (3 : ℤ) ^ (r + 1) * S.suffixHenselQuotient hStart i := by
    rw [← hr']
    exact hSpec
  rw [hSpec'] at hUnit
  have hPowPos : 0 < (3 : ℤ) ^ (r + 1) := by positivity
  by_contra hneg
  have hQneg : S.suffixHenselQuotient hStart i < 0 := by omega
  have hProdNeg :
      (3 : ℤ) ^ (r + 1) * S.suffixHenselQuotient hStart i < 0 :=
    mul_neg_of_pos_of_neg hPowPos hQneg
  linarith [hUnit.1]

/--
actual shifted quotient `Q_i=q_i+1` の normalized linear upper bound。
-/
theorem qOne_linear_upper
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < S.width) :
    let C := S.toMonotoneSuffixHenselChain hStart
    3 * C.qOne i <=
      (4 * (S.width - i : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by
  dsimp
  let n := S.width - i
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnPos)
  have hUnit := S.suffixHenselUnit_succ_nonneg_and_le i r
  have hSpec := S.suffixHenselQuotient_spec hStart (i := i) (Nat.le_of_lt hi)
  have hr' : S.width - i = r + 1 := by
    simpa [n, Nat.succ_eq_add_one] using hr
  have hSpec' :
      S.suffixHenselUnit i (r + 1) =
        (3 : ℤ) ^ (r + 1) * S.suffixHenselQuotient hStart i := by
    rw [← hr']
    exact hSpec
  have hBound :
      (3 : ℤ) ^ r *
          (3 * S.suffixHenselQuotient hStart i) <=
        (3 : ℤ) ^ r *
          (4 * (r + 1 : ℤ) *
            (2 : ℤ) ^ (S.suffixHenselDelta i - 1)) := by
    calc
      (3 : ℤ) ^ r *
          (3 * S.suffixHenselQuotient hStart i)
          =
        (3 : ℤ) ^ (r + 1) * S.suffixHenselQuotient hStart i := by
          rw [pow_succ]
          ring
      _ = S.suffixHenselUnit i (r + 1) := hSpec'.symm
      _ <=
        4 * (r + 1 : ℤ) *
          (2 : ℤ) ^ (S.suffixHenselDelta i - 1) * (3 : ℤ) ^ r := hUnit.2
      _ =
        (3 : ℤ) ^ r *
          (4 * (r + 1 : ℤ) *
            (2 : ℤ) ^ (S.suffixHenselDelta i - 1)) := by ring
  have hPowPos : 0 < (3 : ℤ) ^ r := by positivity
  have hQ :
      3 * S.suffixHenselQuotient hStart i <=
        4 * (r + 1 : ℤ) *
          (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by
    nlinarith [hBound]
  have hA : 1 <= (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by
    have hp : 0 < (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by positivity
    omega
  unfold MonotoneSuffixHenselChain.qOne
  change
    3 * (S.suffixHenselQuotient hStart i + 1) <=
      (4 * (S.width - i : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta i - 1)
  have hrInt :
      (S.width : ℤ) - (i : ℤ) = (r + 1 : ℤ) := by
    have hiLe : i ≤ S.width := Nat.le_of_lt hi
    rw [← Nat.cast_sub hiLe]
    exact_mod_cast hr'
  rw [hrInt]
  calc
    3 * (S.suffixHenselQuotient hStart i + 1)
        = 3 * S.suffixHenselQuotient hStart i + 3 := by ring
    _ <=
      4 * (r + 1 : ℤ) *
          (2 : ℤ) ^ (S.suffixHenselDelta i - 1) +
        3 * (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by
          exact add_le_add hQ (by nlinarith)
    _ =
      (4 * (r + 1 : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by ring

/-! ## repeat start での Beatty exponent bound -/

/--
actual gap の start `j` では

  2^(delta_j-1+j) <= 2*3^j.
-/
theorem suffixHenselDelta_pow_mul_twoPow_le
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (j : ℕ) :
    2 ^ (S.suffixHenselDelta j - 1) * 2 ^ j <=
      2 * 3 ^ j := by
  have hDeltaPos := S.suffixHenselDelta_pos j
  have hCast := S.suffixHenselDelta_cast_sub_one j
  rcases beattyIndex_add_eq_add_or_add_one S.b j with hNo | hCarry
  · have hDisp :
        S.suffixHenselDelta j - 1 + j = beattyIndex j := by
      have hInt :
          (S.suffixHenselDelta j : ℤ) - 1 + (j : ℤ) =
            (beattyIndex j : ℤ) := by
        rw [hNo] at hCast
        push_cast at hCast
        linarith
      have hSubCast :
          ((S.suffixHenselDelta j - 1 : ℕ) : ℤ) =
            (S.suffixHenselDelta j : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 <= S.suffixHenselDelta j)]
        norm_num
      have hInt' :
          ((S.suffixHenselDelta j - 1 : ℕ) : ℤ) + (j : ℤ) =
            (beattyIndex j : ℤ) := by
        rw [hSubCast]
        exact hInt
      exact_mod_cast hInt'
    rw [← pow_add, hDisp]
    exact le_trans (beattyIndex_lower j)
      (by omega)
  · have hDisp :
        S.suffixHenselDelta j - 1 + j = beattyIndex j + 1 := by
      have hInt :
          (S.suffixHenselDelta j : ℤ) - 1 + (j : ℤ) =
            (beattyIndex j : ℤ) + 1 := by
        rw [hCarry] at hCast
        push_cast at hCast
        linarith
      have hSubCast :
          ((S.suffixHenselDelta j - 1 : ℕ) : ℤ) =
            (S.suffixHenselDelta j : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 <= S.suffixHenselDelta j)]
        norm_num
      have hInt' :
          ((S.suffixHenselDelta j - 1 : ℕ) : ℤ) + (j : ℤ) =
            (beattyIndex j : ℤ) + 1 := by
        rw [hSubCast]
        exact hInt
      exact_mod_cast hInt'
    rw [← pow_add, hDisp, pow_succ]
    have hBeta := beattyIndex_lower j
    nlinarith

/-! ## elementary large-width numeric inequality -/

private theorem odd_width_growth
    {k : ℕ}
    (hk : 18 <= k) :
    (8 * k + 7) * 3 ^ k < 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
      norm_num
  | succ k hk18 ih =>
      have hCoeff :
          3 * (8 * (k + 1) + 7) < 4 * (8 * k + 7) := by
        omega
      have hPowPos : 0 < 3 ^ k := by positivity
      have h1 := Nat.mul_lt_mul_of_pos_right hCoeff hPowPos
      have h2 := Nat.mul_lt_mul_of_pos_left ih (by norm_num : 0 < 4)
      calc
        (8 * (k + 1) + 7) * 3 ^ (k + 1)
            = 3 * (8 * (k + 1) + 7) * 3 ^ k := by
                simp [pow_succ]
                ring
        _ < 4 * (8 * k + 7) * 3 ^ k := h1
        _ < 4 * 4 ^ k := by
              simpa only [Nat.mul_assoc] using h2
        _ = 4 ^ (k + 1) := by
              rw [pow_succ]
              ring

/-- 偶数幅の場合に使う係数 `8*n+11` の指数成長評価。 -/
private theorem even_width_growth_aux
    {n : ℕ}
    (hn : 18 <= n) :
    (8 * n + 11) * 3 ^ n < 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn18 ih =>
      have hCoeff :
          3 * (8 * (n + 1) + 11) < 4 * (8 * n + 11) := by
        omega
      have hPowPos : 0 < 3 ^ n := by positivity
      have h1 := Nat.mul_lt_mul_of_pos_right hCoeff hPowPos
      have h2 := Nat.mul_lt_mul_of_pos_left ih (by norm_num : 0 < 4)
      calc
        (8 * (n + 1) + 11) * 3 ^ (n + 1)
            = 3 * (8 * (n + 1) + 11) * 3 ^ n := by
                rw [pow_succ]
                ring
        _ < 4 * (8 * n + 11) * 3 ^ n := h1
        _ < 4 * 4 ^ n := by
              simpa only [Nat.mul_assoc] using h2
        _ = 4 ^ (n + 1) := by
              rw [pow_succ]
              ring

private theorem even_width_growth
    {k : ℕ}
    (hk : 19 <= k) :
    (8 * k + 3) * 3 ^ (k - 1) < 4 ^ (k - 1) := by
  let n := k - 1
  have hn : 18 <= n := by
    dsimp [n]
    omega
  have hkEq : k = n + 1 := by
    dsimp [n]
    omega
  have hBase := even_width_growth_aux hn
  rw [hkEq]
  have hPred : n + 1 - 1 = n := by omega
  rw [hPred]
  simpa [Nat.mul_add, Nat.add_assoc] using hBase

/--
`W>=37`, `m=(W-1)/2` なら nonzero branch の必要条件とは逆向きの strict inequality。
-/
theorem fourPow_gt_width_mul_threePow_of_ge_37
    {W : ℕ}
    (hW : 37 <= W) :
    let m := (W - 1) / 2
    (4 * W + 3) * 3 ^ m < 4 ^ m := by
  dsimp
  have hmodLt : W % 2 < 2 := Nat.mod_lt W (by norm_num)
  have hmodCases : W % 2 = 0 ∨ W % 2 = 1 := by omega
  have hDiv := Nat.mod_add_div W 2
  rcases hmodCases with hEven | hOdd
  · let k := W / 2
    have hWEq : W = 2 * k := by
      dsimp [k]
      rw [← hDiv, hEven]
      omega
    have hk : 19 <= k := by
      rw [hWEq] at hW
      omega
    have hm : (W - 1) / 2 = k - 1 := by
      rw [hWEq]
      omega
    rw [hm, hWEq]
    convert even_width_growth hk using 1
    ring
  · let k := W / 2
    have hWEq : W = 2 * k + 1 := by
      dsimp [k]
      rw [← hDiv, hOdd]
      omega
    have hk : 18 <= k := by
      rw [hWEq] at hW
      omega
    have hm : (W - 1) / 2 = k := by
      rw [hWEq]
      omega
    rw [hm, hWEq]
    convert odd_width_growth hk using 1
    ring

/-! ## nonzero forced repeat の排除 -/

/--
`qOne_linear_upper` の係数 `4*(width-i)+3` を、
位置に依存しない共通係数 `4*width+3` まで粗くした上界。

後続の repeated-block 比較では `i` と `j` の両方を同じ係数で
扱いたいため、この形を共通インターフェースとして使う。
-/
theorem qOne_width_upper
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < S.width) :
    let C := S.toMonotoneSuffixHenselChain hStart
    3 * C.qOne i <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by
  have hLocal := S.qOne_linear_upper hStart hi
  dsimp only at hLocal ⊢
  have hCoeff :
      4 * (S.width - i : ℤ) + 3 <=
        4 * (S.width : ℤ) + 3 := by
    omega
  have hPowNonneg :
      0 <= (2 : ℤ) ^ (S.suffixHenselDelta i - 1) := by
    positivity
  exact le_trans hLocal
    (mul_le_mul_of_nonneg_right hCoeff hPowNonneg)

/--
actual restarted Hensel chain では quotient は nonnegative なので、
shifted quotient `Q_i = q_i + 1` は常に正である。

scaled difference の符号ごとの比較で、反対側の `Q` 項を
安全に捨てるために使う。
-/
theorem qOne_pos_of_lt_width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < S.width) :
    let C := S.toMonotoneSuffixHenselChain hStart
    0 < C.qOne i := by
  have hQ := S.suffixHenselQuotient_nonneg hStart hi
  dsimp
  unfold MonotoneSuffixHenselChain.qOne
  change 0 < S.suffixHenselQuotient hStart i + 1
  omega

/--
`delta_j = delta_i + Delta` のとき、
`i` 側の `qOne` 上界を `2^Delta` 倍して
`j` 側の Hensel scale に揃える。

これにより scaled difference

  Q_j - 2^Delta Q_i

の両項を同じ

  (4*width+3) * 2^(delta_j-1)

で比較できる。
-/
theorem scaled_qOne_width_upper_of_delta_eq
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hi : i < S.width)
    (hDelta :
      S.suffixHenselDelta j =
        S.suffixHenselDelta i + Delta) :
    let C := S.toMonotoneSuffixHenselChain hStart
    3 * ((2 : ℤ) ^ Delta * C.qOne i) <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1) := by
  let C := S.toMonotoneSuffixHenselChain hStart
  have hBiW := S.qOne_width_upper hStart hi
  change
    3 * C.qOne i <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta i - 1)
    at hBiW
  have hDPosI : 0 < S.suffixHenselDelta i :=
    S.suffixHenselDelta_pos i
  have hDPosJ : 0 < S.suffixHenselDelta j :=
    S.suffixHenselDelta_pos j
  have hPowShift :
      (2 : ℤ) ^ Delta *
          (2 : ℤ) ^ (S.suffixHenselDelta i - 1) =
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1) := by
    have hNat :
        Delta + (S.suffixHenselDelta i - 1) =
          S.suffixHenselDelta j - 1 := by
      omega
    rw [← pow_add, hNat]
  have hScaleNonneg : 0 <= (2 : ℤ) ^ Delta := by
    positivity
  have hScaled :=
    mul_le_mul_of_nonneg_left hBiW hScaleNonneg
  change
    3 * ((2 : ℤ) ^ Delta * C.qOne i) <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1)
  calc
    3 * ((2 : ℤ) ^ Delta * C.qOne i)
        =
      (2 : ℤ) ^ Delta * (3 * C.qOne i) := by
        ring
    _ <=
      (2 : ℤ) ^ Delta *
        ((4 * (S.width : ℤ) + 3) *
          (2 : ℤ) ^ (S.suffixHenselDelta i - 1)) := hScaled
    _ =
      (4 * (S.width : ℤ) + 3) *
        ((2 : ℤ) ^ Delta *
          (2 : ℤ) ^ (S.suffixHenselDelta i - 1)) := by
        ring
    _ =
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1) := by
      rw [hPowShift]

/--
length `m` の repeated block の scaled difference が nonzero なら、
`2^m` divisibility により scaled difference の絶対値は少なくとも `2^m`。

その符号が正の場合は `Q_j`、負の場合は `2^Delta Q_i` が
少なくとも `2^m` を担う。両側の `qOne` 上界を使うことで、

  3 * 2^m
    <= (4*width+3) * 2^(delta_j-1)

を得る。

これは nonzero repeat から得られる主要な size lower bound。
-/
theorem three_mul_twoPow_le_width_deltaPow_of_nonzero_repeat
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {m i j Delta : ℕ}
    (hmPos : 0 < m)
    (hiEnd : i + m <= S.width)
    (hjEnd : j + m <= S.width)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i j m Delta)
    (hNonzero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i j Delta 0 ≠ 0) :
    let _C := S.toMonotoneSuffixHenselChain hStart
    3 * (2 : ℤ) ^ m <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1) := by
  let C := S.toMonotoneSuffixHenselChain hStart
  dsimp only at hBlock hNonzero
  have hiW : i < S.width := by
    omega
  have hjW : j < S.width := by
    omega
  have hDelta := hBlock 0 (by omega)
  simp only [Nat.add_zero] at hDelta
  change
    S.suffixHenselDelta j =
      S.suffixHenselDelta i + Delta
    at hDelta
  have hDiv :
      (2 : ℤ) ^ m ∣
        C.scaledDifference i j Delta 0 :=
    C.twoPow_dvd_scaledDifference_zero hiEnd hjEnd hBlock
  rcases hDiv with ⟨z, hz⟩
  have hzNe : z ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero] at hz
    exact hNonzero hz
  have hQiPos := S.qOne_pos_of_lt_width hStart hiW
  have hQjPos := S.qOne_pos_of_lt_width hStart hjW
  change 0 < C.qOne i at hQiPos
  change 0 < C.qOne j at hQjPos
  have hBiScaled :=
    S.scaled_qOne_width_upper_of_delta_eq
      hStart hiW hDelta
  change
    3 * ((2 : ℤ) ^ Delta * C.qOne i) <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1)
    at hBiScaled
  have hBjW := S.qOne_width_upper hStart hjW
  change
    3 * C.qOne j <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1)
    at hBjW
  change
    3 * (2 : ℤ) ^ m <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1)
  have hzCases : z < 0 ∨ 0 < z :=
    lt_or_gt_of_ne hzNe
  rcases hzCases with hzNeg | hzPos
  · have hzLe : z <= -1 := by
      omega
    have hPowPos : 0 < (2 : ℤ) ^ m := by
      positivity
    have hMle :
        C.scaledDifference i j Delta 0 <=
          - (2 : ℤ) ^ m := by
      rw [hz]
      have hmul :=
        mul_le_mul_of_nonneg_left hzLe (le_of_lt hPowPos)
      simpa using hmul
    unfold MonotoneSuffixHenselChain.scaledDifference at hMle
    simp only [Nat.add_zero] at hMle
    have hY :
        (2 : ℤ) ^ m <=
          (2 : ℤ) ^ Delta * C.qOne i - C.qOne j := by
      linarith
    have h3Y :
        3 * (2 : ℤ) ^ m <=
          3 * ((2 : ℤ) ^ Delta * C.qOne i) -
            3 * C.qOne j := by
      linarith
    have hQjNonneg :
        0 <= 3 * C.qOne j := by
      have : 0 <= C.qOne j := le_of_lt hQjPos
      positivity
    have hToScaled :
        3 * (2 : ℤ) ^ m <=
          3 * ((2 : ℤ) ^ Delta * C.qOne i) := by
      linarith
    exact le_trans hToScaled hBiScaled
  · have hzGe : 1 <= z := by
      omega
    have hPowPos : 0 < (2 : ℤ) ^ m := by
      positivity
    have hMge :
        (2 : ℤ) ^ m <=
          C.scaledDifference i j Delta 0 := by
      rw [hz]
      have hmul :=
        mul_le_mul_of_nonneg_left hzGe (le_of_lt hPowPos)
      simpa using hmul
    unfold MonotoneSuffixHenselChain.scaledDifference at hMge
    simp only [Nat.add_zero] at hMge
    have h3M :
        3 * (2 : ℤ) ^ m <=
          3 * C.qOne j -
            3 * ((2 : ℤ) ^ Delta * C.qOne i) := by
      linarith
    have hQiScaledNonneg :
        0 <=
          3 * ((2 : ℤ) ^ Delta * C.qOne i) := by
      positivity
    have hToJ :
        3 * (2 : ℤ) ^ m <=
          3 * C.qOne j := by
      linarith
    exact le_trans hToJ hBjW

/--
二つの2冪評価

  3 * 2^m <= B * 2^e

および

  2^e * 2^j <= 2 * 3^j

から、`j <= m+1` の範囲で

  4^m <= B * 3^m

を導く純粋な冪比較補題。

ここには restarted Hensel chain や scaled difference の情報は残っておらず、
後半の size arithmetic だけを切り出している。
-/
private theorem fourPow_le_mul_threePow_of_twoPower_bridge
    {m j e : ℕ}
    {B : ℤ}
    (hjBound : j <= m + 1)
    (hBNonneg : 0 <= B)
    (hPowerLower :
      3 * (2 : ℤ) ^ m <=
        B * (2 : ℤ) ^ e)
    (hDeltaPow :
      (2 : ℤ) ^ e * (2 : ℤ) ^ j <=
        2 * (3 : ℤ) ^ j) :
    (4 : ℤ) ^ m <=
      B * (3 : ℤ) ^ m := by
  have hTwoJNonneg :
      0 <= (2 : ℤ) ^ j := by
    positivity
  have hMulJ :=
    mul_le_mul_of_nonneg_right
      hPowerLower hTwoJNonneg
  have hUseDelta :=
    mul_le_mul_of_nonneg_left
      hDeltaPow hBNonneg
  have hMid :
      3 * (2 : ℤ) ^ (m + j) <=
        2 * B * (3 : ℤ) ^ j := by
    calc
      3 * (2 : ℤ) ^ (m + j)
          =
        (3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ j := by
          rw [pow_add]
          ring
      _ <=
        (B * (2 : ℤ) ^ e) *
          (2 : ℤ) ^ j := hMulJ
      _ <=
        B * (2 * (3 : ℤ) ^ j) := by
          simpa [mul_assoc] using hUseDelta
      _ =
        2 * B * (3 : ℤ) ^ j := by
          ring
  let d := m + 1 - j
  have hdEq :
      j + d = m + 1 := by
    dsimp [d]
    omega
  have hTwoDNonneg :
      0 <= (2 : ℤ) ^ d := by
    positivity
  have hMidScaled :=
    mul_le_mul_of_nonneg_right
      hMid hTwoDNonneg
  have hTwoLeThree :
      (2 : ℤ) ^ d <=
        (3 : ℤ) ^ d := by
    exact_mod_cast
      Nat.pow_le_pow_left
        (by norm_num : 2 <= (3 : ℕ)) d
  have hScaleNonneg :
      0 <=
        2 * B * (3 : ℤ) ^ j := by
    positivity
  have hRightScale :
      2 * B * (3 : ℤ) ^ j * (2 : ℤ) ^ d <=
        2 * B * (3 : ℤ) ^ j * (3 : ℤ) ^ d := by
    exact
      mul_le_mul_of_nonneg_left
        hTwoLeThree hScaleNonneg
  have hTwoProd :
      (2 : ℤ) ^ (m + j) * (2 : ℤ) ^ d =
        (2 : ℤ) ^ (2 * m + 1) := by
    rw [← pow_add]
    have hExp :
        m + j + d = 2 * m + 1 := by
      omega
    rw [hExp]
  have hPowFour :
      (2 : ℤ) ^ (2 * m + 1) =
        2 * (4 : ℤ) ^ m := by
    calc
      (2 : ℤ) ^ (2 * m + 1)
          =
        (2 : ℤ) ^ (2 * m) * 2 := by
          rw [pow_succ]
      _ =
        ((2 : ℤ) ^ 2) ^ m * 2 := by
          rw [pow_mul]
      _ =
        (4 : ℤ) ^ m * 2 := by
          norm_num
      _ =
        2 * (4 : ℤ) ^ m := by
          ring
  have hThreeProd :
      (3 : ℤ) ^ j * (3 : ℤ) ^ d =
        (3 : ℤ) ^ (m + 1) := by
    rw [← pow_add, hdEq]
  have hFinalSix :
      6 * (4 : ℤ) ^ m <=
        6 * B * (3 : ℤ) ^ m := by
    calc
      6 * (4 : ℤ) ^ m
          =
        3 *
          ((2 : ℤ) ^ (m + j) *
            (2 : ℤ) ^ d) := by
          rw [hTwoProd, hPowFour]
          ring
      _ =
        3 * (2 : ℤ) ^ (m + j) *
          (2 : ℤ) ^ d := by
          ring
      _ <=
        2 * B * (3 : ℤ) ^ j *
          (2 : ℤ) ^ d := by
          simpa [mul_assoc] using hMidScaled
      _ <=
        2 * B * (3 : ℤ) ^ j *
          (3 : ℤ) ^ d := hRightScale
      _ =
        2 * B *
          ((3 : ℤ) ^ j * (3 : ℤ) ^ d) := by
          ring
      _ =
        2 * B * (3 : ℤ) ^ (m + 1) := by
          rw [hThreeProd]
      _ =
        6 * B * (3 : ℤ) ^ m := by
          rw [pow_succ]
          ring
  nlinarith [hFinalSix]

/--
length `m` の repeated block の scaled difference が nonzero なら、
その repeat が存在するためには

  4^m <= (4*width+3) * 3^m

が必要である。

証明は、

* repeated-block arithmetic による `2^m` divisibility、
* actual restarted quotient の linear bound、
* Beatty staircase が与える `delta_j` の2冪評価、

を組み合わせ、最後は純粋な `2` と `3` の冪比較に還元する。

この不等式は後で `m = (width-1)/2` と置いたとき、
`width >= 37` では成り立たないため、
large-width repeat の nonzero branch を排除するための橋になる。
-/
theorem fourPow_le_width_mul_threePow_of_nonzero_repeat
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {m i j Delta : ℕ}
    (hjBound : j <= m + 1)
    (hiEnd : i + m <= S.width)
    (hjEnd : j + m <= S.width)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i j m Delta)
    (hNonzero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i j Delta 0 ≠ 0) :
    4 ^ m <=
      (4 * S.width + 3) * 3 ^ m := by
  dsimp only at hBlock hNonzero
  by_cases hmZero : m = 0
  · subst m
    norm_num
  have hmPos : 0 < m :=
    Nat.pos_of_ne_zero hmZero
  have hPowerLower :=
    S.three_mul_twoPow_le_width_deltaPow_of_nonzero_repeat
      hStart hmPos hiEnd hjEnd hBlock hNonzero
  change
    3 * (2 : ℤ) ^ m <=
      (4 * (S.width : ℤ) + 3) *
        (2 : ℤ) ^ (S.suffixHenselDelta j - 1)
    at hPowerLower
  have hDeltaPowNat :=
    S.suffixHenselDelta_pow_mul_twoPow_le j
  have hDeltaPow :
      (2 : ℤ) ^ (S.suffixHenselDelta j - 1) *
          (2 : ℤ) ^ j <=
        2 * (3 : ℤ) ^ j := by
    exact_mod_cast hDeltaPowNat
  have hBNonneg :
      0 <= 4 * (S.width : ℤ) + 3 := by
    positivity
  have hInt :
      (4 : ℤ) ^ m <=
        (4 * (S.width : ℤ) + 3) *
          (3 : ℤ) ^ m :=
    fourPow_le_mul_threePow_of_twoPower_bridge
      (m := m)
      (j := j)
      (e := S.suffixHenselDelta j - 1)
      (B := 4 * (S.width : ℤ) + 3)
      hjBound
      hBNonneg
      hPowerLower
      hDeltaPow
  exact_mod_cast hInt
/--
width `>=37` では、factor-complexity が強制する maximal half-width repeat は
必ず zero scaled-difference branch に入る。
-/
theorem exists_forced_zero_scaledDifference_of_width_ge_37
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : 37 <= S.width) :
    let C := S.toMonotoneSuffixHenselChain hStart
    let m := (S.width - 1) / 2
    ∃ i j Delta : ℕ,
      i < j ∧
      j <= m + 1 ∧
      j + m <= C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.scaledDifference i j Delta 0 = 0 := by
  dsimp
  let m := (S.width - 1) / 2
  have hFit : 2 * m + 1 <= S.width := by
    dsimp [m]
    omega
  rcases
      S.exists_sameDeltaOffsetBlock_of_two_mul_add_one_le_width
        hStart m hFit with
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock⟩
  have hiEnd : i + m <= S.width := by omega
  refine ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, ?_⟩
  by_contra hNonzero
  have hNecessary :=
    S.fourPow_le_width_mul_threePow_of_nonzero_repeat
      hStart hjBound hiEnd hjEnd hBlock hNonzero
  have hStrict :=
    fourPow_gt_width_mul_threePow_of_ge_37 hWidth
  dsimp [m] at hStrict
  exact (Nat.not_lt_of_ge hNecessary) hStrict

/--
large-width forced zero repeat は backward propagation により entrance scaled state を作る。

これで width `>=37` の actual restarted branch は zero-cycle branch だけに縮約される。
-/
theorem exists_entrance_scaledState_of_width_ge_37
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : 37 <= S.width) :
    let C := S.toMonotoneSuffixHenselChain hStart
    let m := (S.width - 1) / 2
    ∃ i j Delta : ℕ,
      i < j ∧
      j <= m + 1 ∧
      j + m <= C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.ScaledState 0 (j - i) Delta := by
  dsimp
  rcases
      S.exists_forced_zero_scaledDifference_of_width_ge_37
        hStart hWidth with
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, hZero⟩
  let C := S.toMonotoneSuffixHenselChain hStart
  have hQEq :
      C.qOne j = (2 : ℤ) ^ Delta * C.qOne i :=
    (C.scaledDifference_zero_eq_zero_iff).1 hZero
  have hDelta := hBlock 0 (by omega)
  simp only [Nat.add_zero] at hDelta
  have hState : C.ScaledState i j Delta := ⟨hDelta, hQEq⟩
  have hjW : j < C.width := by
    dsimp [C]
    have hmPos : 0 < (S.width - 1) / 2 := by omega
    omega
  have hProp := C.scaledState_propagate_to_zero
    (Nat.le_of_lt hij) hjW hState
  exact ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, hProp⟩

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
