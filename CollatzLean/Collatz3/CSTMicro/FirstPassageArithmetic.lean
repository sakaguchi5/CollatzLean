import CollatzLean.Collatz3.CSTMicro.Residue
import CollatzLean.Collatz3.Critical.Beatty
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Collatz3 CSTMicro: first-passage arithmetic

standard parity first-passage path から、次の二つを導く。

1. terminal standard length は endpoint odd count の critical depth に exact に一致する。
2. affine numerator は旧 `p * 3^p` より一段鋭い

     `B ≤ p * 3^(p-1)`

   を満たす。

第2点は affine scan の invariant を
`B ≤ m * 3^(m-1)` に強めることで得る。
-/

namespace Collatz3
namespace CSTMicro

/--
左から parity word を読む affine accumulator。

current numerator を `B`、current standard time を `k` とすると、
odd step で `B <- 3B + 2^k`、even step では `B` を保つ。
-/
def affineScan : ParityWord → ℕ → ℕ → ℕ
  | [], _k, B => B
  | false :: v, k, B => affineScan v (k + 1) B
  | true :: v, k, B => affineScan v (k + 1) (3 * B + 2 ^ k)

/-- affine scan と endpoint affine numerator の exact relation。 -/
theorem affineScan_eq
    (v : ParityWord) (k B : ℕ) :
    affineScan v k B =
      3 ^ oddCount v * B + 2 ^ k * affineConst v := by
  induction v generalizing k B with
  | nil =>
      simp [affineScan, oddCount, affineConst]
  | cons b v ih =>
      cases b
      · simp [affineScan, ih, pow_succ]
        ring
      · simp [affineScan, ih, pow_succ]
        ring

/--
current position `(k,m)` から見て、残り word の各 step 開始点が
critical power boundary の expanding 側または境界上にある。
-/
def PrefixPowerBoundedFrom
    (v : ParityWord) (k m : ℕ) : Prop :=
  ∀ j : ℕ, j < v.length →
    2 ^ (k + j) ≤
      3 ^ (m + prefixOddCount v j)

/-- prefix power bound は head を一つ読むと tail へ移る。 -/
theorem PrefixPowerBoundedFrom.tail
    {b : Bool} {v : ParityWord} {k m : ℕ}
    (h : PrefixPowerBoundedFrom (b :: v) k m) :
    PrefixPowerBoundedFrom v (k + 1) (m + bitNat b) := by
  unfold PrefixPowerBoundedFrom at h ⊢
  intro j hj
  have hs := h (j + 1) (by simp; omega)
  have hk : k + (j + 1) = (k + 1) + j := by omega
  have hm :
      m + prefixOddCount (b :: v) (j + 1) =
        (m + bitNat b) + prefixOddCount v j := by
    simp [prefixOddCount_cons_succ]
    omega
  rw [hk, hm] at hs
  exact hs

/-- first-passage path は時刻0から prefix power bound を満たす。 -/
theorem FirstPassagePath.prefixPowerBoundedFrom_zero
    (P : FirstPassagePath) :
    PrefixPowerBoundedFrom P.word 0 0 := by
  unfold PrefixPowerBoundedFrom
  intro j hj
  simp only [Nat.zero_add]
  exact P.prefix_twoPow_le_threePow (by simpa [FirstPassagePath.length] using hj)

/--
`3 * (m * 3^(m-1)) + 3^m` は次の invariant
`(m+1) * 3^m` 以下。

`m=0` も natural truncated subtraction により同じ式で扱える。
-/
private theorem affineInvariant_step_bound (m : ℕ) :
    3 * (m * 3 ^ (m - 1)) + 3 ^ m ≤
      (m + 1) * 3 ^ m := by
  cases m with
  | zero => simp
  | succ n =>
      simp [pow_succ]
      nlinarith [Nat.zero_le (3 ^ n)]

/--
critical boundary に沿う sharpened affine scan invariant。

current numerator が `B ≤ m * 3^(m-1)` なら、残りを読んだ後も
同じ形の bound が保存される。
-/
theorem affineScan_le_oddCount_mul_threePow_pred_of_prefixPowerBoundedFrom
    {v : ParityWord} {k m B : ℕ}
    (hPrefix : PrefixPowerBoundedFrom v k m)
    (hB : B ≤ m * 3 ^ (m - 1)) :
    affineScan v k B ≤
      (m + oddCount v) * 3 ^ (m + oddCount v - 1) := by
  induction v generalizing k m B with
  | nil =>
      simpa [affineScan, oddCount] using hB
  | cons b v ih =>
      cases b
      · have hTail : PrefixPowerBoundedFrom v (k + 1) m := by
          simpa using PrefixPowerBoundedFrom.tail hPrefix
        have hRec := ih (k := k + 1) (m := m) (B := B) hTail hB
        simpa [affineScan] using hRec
      · have hkRaw := hPrefix 0 (by simp)
        have hk : 2 ^ k ≤ 3 ^ m := by
          simpa [prefixOddCount] using hkRaw
        have hThreeB :
            3 * B ≤ 3 * (m * 3 ^ (m - 1)) :=
          Nat.mul_le_mul_left 3 hB
        have hNextRaw :
            3 * B + 2 ^ k ≤
              3 * (m * 3 ^ (m - 1)) + 3 ^ m :=
          Nat.add_le_add hThreeB hk
        have hNext :
            3 * B + 2 ^ k ≤
              (m + 1) * 3 ^ ((m + 1) - 1) := by
          have hStep := affineInvariant_step_bound m
          have hpow : (m + 1) - 1 = m := by omega
          rw [hpow]
          exact le_trans hNextRaw hStep
        have hTail : PrefixPowerBoundedFrom v (k + 1) (m + 1) := by
          simpa using PrefixPowerBoundedFrom.tail hPrefix
        have hRec :=
          ih (k := k + 1) (m := m + 1)
            (B := 3 * B + 2 ^ k) hTail hNext
        have hsum :
            (m + 1) + oddCount v = m + (oddCount v + 1) := by
          omega
        simpa [affineScan, hsum] using hRec

namespace FirstPassagePath

/--
first-passage geometry だけから affine numerator を

`B ≤ p * 3^(p-1)`

で抑える。旧 `p * 3^p` bound の factor 3 改善に相当する。
-/
theorem affineConst_le_endpointOddCount_mul_threePow_pred
    (P : FirstPassagePath) :
    affineConst P.word ≤
      P.endpointOddCount * 3 ^ (P.endpointOddCount - 1) := by
  have hScan :=
    affineScan_le_oddCount_mul_threePow_pred_of_prefixPowerBoundedFrom
      (v := P.word) (k := 0) (m := 0) (B := 0)
      P.prefixPowerBoundedFrom_zero
      (by simp)
  have hScanEq : affineScan P.word 0 0 = affineConst P.word := by
    simpa using affineScan_eq P.word 0 0
  rw [hScanEq] at hScan
  simpa [endpointOddCount] using hScan

/--
first coefficient crossing の standard length は、endpoint odd count に対する
critical two-depth `beattyIndex p + 1` と exact に一致する。
-/
theorem length_eq_criticalTwoDepth
    (P : FirstPassagePath) :
    P.length = Critical.criticalTwoDepth P.endpointOddCount := by
  have hlenPos : 0 < P.length := P.length_pos
  have hUpper :
      3 ^ P.endpointOddCount ≤ 2 ^ ((P.length - 1) + 1) := by
    have hterm : 3 ^ P.endpointOddCount ≤ 2 ^ P.length :=
      le_of_lt P.terminal_contracting
    have hlen : (P.length - 1) + 1 = P.length := by
      omega
    simpa [hlen] using hterm
  have hBeattyLe :
      Critical.beattyIndex P.endpointOddCount ≤ P.length - 1 :=
    Critical.beattyIndex_le_of_upper hUpper
  have hOther :
      P.length - 1 ≤ Critical.beattyIndex P.endpointOddCount := by
    by_contra hnot
    have hlt :
        Critical.beattyIndex P.endpointOddCount < P.length - 1 := by
      omega
    let k := Critical.beattyIndex P.endpointOddCount + 1
    have hkPos : 0 < k := by
      simp [k]
    have hkLt : k < P.length := by
      dsimp [k]
      omega
    have hExp := P.proper_expanding k hkPos (by simpa [length] using hkLt)
    unfold CoefficientExpandingAt at hExp
    have hPrefixLe :
        prefixOddCount P.word k ≤ P.endpointOddCount := by
      simpa [endpointOddCount] using prefixOddCount_le_oddCount P.word k
    have hThreeLe :
        3 ^ prefixOddCount P.word k ≤ 3 ^ P.endpointOddCount := by
      exact Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hPrefixLe
    have hBeattyUpper := Critical.beattyIndex_upper P.endpointOddCount
    have hkEq :
        k = Critical.beattyIndex P.endpointOddCount + 1 := rfl
    have hContr : 2 ^ k < 2 ^ k := by
      calc
        2 ^ k < 3 ^ prefixOddCount P.word k := hExp
        _ ≤ 3 ^ P.endpointOddCount := hThreeLe
        _ ≤ 2 ^ (Critical.beattyIndex P.endpointOddCount + 1) := hBeattyUpper
        _ = 2 ^ k := by rw [hkEq]
    omega
  have hEq : Critical.beattyIndex P.endpointOddCount = P.length - 1 := by
    omega
  unfold Critical.criticalTwoDepth
  rw [hEq]
  omega

/-- terminal gap も endpoint odd count だけの critical gap に書き直せる。 -/
theorem terminalGap_eq_criticalGap
    (P : FirstPassagePath) :
    P.terminalGap =
      2 ^ Critical.criticalTwoDepth P.endpointOddCount -
        3 ^ P.endpointOddCount := by
  unfold terminalGap
  rw [P.length_eq_criticalTwoDepth]

end FirstPassagePath
end CSTMicro
end Collatz3
