import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerFareyBeatty
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianFiniteScanIdentity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalStrongMatchProof

/-!
# Actual strong overlap から corrected finite Xi 恒等式へ

critical Xi を infinite 2-adic object として導入せず、
既存の `beattyInverseContribution` が持つ有限和だけを用いて
odd/even の corrected identity を証明する。

このファイルでは strong overlap、Beatty position、Christoffel `phi`、
有限 `ZMod (2^e)` 計算を直接接続する。外部 input は一切使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Beatty 逆寄与の連続区間を表す tail。

`a` から始まる `n` 個の項だけを `ZMod (2^K)` 上で保持し、
prefix と tail の分解や overlap 後の有限和移送に使う。
-/
def beattyInverseTail
    (K a : ℕ) : ℕ → ZMod (2 ^ K)
  | 0 => 0
  | n + 1 =>
      beattyInverseTail K a n +
        (2 : ZMod (2 ^ K)) ^ beattyIndex (a + n) *
          invThreePow K (a + n + 1)

@[simp] theorem beattyInverseTail_zero
    (K a : ℕ) : beattyInverseTail K a 0 = 0 := rfl

@[simp] theorem beattyInverseTail_succ
    (K a n : ℕ) :
    beattyInverseTail K a (n + 1) =
      beattyInverseTail K a n +
        (2 : ZMod (2 ^ K)) ^ beattyIndex (a + n) *
          invThreePow K (a + n + 1) := rfl

/--
Beatty 逆寄与を prefix と連続 tail に分解する。

`a+n` までの有限和は、最初の `a` 項と
`a` から始まる `n` 項の tail の和に等しい。
-/
theorem beattyInverseContribution_add_tail
    (K a n : ℕ) :
    beattyInverseContribution K (a + n) =
      beattyInverseContribution K a + beattyInverseTail K a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show a + (n + 1) = (a + n) + 1 by omega]
      rw [beattyInverseContribution_succ, ih]
      rw [beattyInverseTail_succ]
      ring

/--
3 の逆冪は指数の加法に沿って積へ分解できる。

後で `3^a` と先頭 `a` 個の逆因子を相殺するための基本補題。
-/
theorem invThreePow_add
    (K a b : ℕ) :
    invThreePow K (a + b) =
      invThreePow K a * invThreePow K b := by
  unfold invThreePow
  rw [pow_add]

/--
`3^a` は `invThreePow K (a+b)` の先頭 `a` 個を相殺する。

結果として残るのは `invThreePow K b` だけである。
-/
theorem threePow_mul_invThreePow_add
    (K a b : ℕ) :
    (3 : ZMod (2 ^ K)) ^ a * invThreePow K (a + b) =
      invThreePow K b := by
  rw [invThreePow_add]
  rw [← mul_assoc, threePow_mul_invThreePow]
  simp

/--
法 `2^K` 上では、指数が `K` 以上の 2 冪は 0 になる。
-/
theorem twoPow_eq_zero_of_le_exponent
    {K d : ℕ}
    (h : K ≤ d) :
    (2 : ZMod (2 ^ K)) ^ d = 0 := by
  exact ZMod.natCast_pow_eq_zero_of_le 2 h

/--
tail の最初の Beatty 位置が precision `K` 以上なら、
その tail 全体は `ZMod (2^K)` で 0 になる。

Beatty index の単調性により、後続項の 2 冪指数もすべて `K` 以上になる。
-/
theorem beattyInverseTail_zero_of_precision
    {K a n : ℕ}
    (h : K ≤ beattyIndex a) :
    beattyInverseTail K a n = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [beattyInverseTail_succ, ih]
      have hmono : beattyIndex a ≤ beattyIndex (a + n) := by
        by_cases hn : n = 0
        · subst n; exact le_rfl
        · exact le_of_lt (beattyIndex_strictMono (by omega))
      have hz :
          (2 : ZMod (2 ^ K)) ^ beattyIndex (a + n) = 0 :=
        twoPow_eq_zero_of_le_exponent (le_trans h hmono)
      rw [hz, zero_mul]
      simp

/--
`2^q` を掛けた tail の消滅条件を局所 precision `L` に分解する。

`K ≤ q+L` かつ `L ≤ beattyIndex a` なら、
各項の総 2 冪指数が `K` 以上になり、法 `2^K` で消える。
-/
theorem twoPow_mul_beattyTail_zero
    {K q L a n : ℕ}
    (hK : K ≤ q + L)
    (hL : L ≤ beattyIndex a) :
    (2 : ZMod (2 ^ K)) ^ q * beattyInverseTail K a n = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [beattyInverseTail_succ, mul_add, ih, zero_add]
      have hmono : beattyIndex a ≤ beattyIndex (a + n) := by
        by_cases hn : n = 0
        · subst n; exact le_rfl
        · exact le_of_lt (beattyIndex_strictMono (by omega))
      have hExp : K ≤ q + beattyIndex (a + n) := by
        omega
      rw [← mul_assoc, ← pow_add]
      rw [twoPow_eq_zero_of_le_exponent hExp, zero_mul]

/--
`e = beattyIndex m` の precision では、
truncation を `m` より先へ延長しても値は変わらない。

追加 tail がすべて `ZMod (2^e)` で消えることを使う。
-/
theorem beattyContribution_eq_of_count_le
    {e m M : ℕ}
    (he : e = beattyIndex m)
    (hM : m ≤ M) :
    beattyInverseContribution e M =
      beattyInverseContribution e m := by
  let n := M - m
  have hsum : m + n = M := by dsimp [n]; omega
  rw [← hsum, beattyInverseContribution_add_tail]
  have hzero : beattyInverseTail e m n = 0 := by
    apply beattyInverseTail_zero_of_precision
    rw [he]
  rw [hzero]
  simp

/--
Beatty の 1 項に `3^P` を掛けたときの exact scaling。

`i < P` の下で逆 3 冪を相殺し、
Christoffel 型の項 `3^(P-1-i) 2^beattyIndex(i)` に変換する。
-/
private theorem scale_one_beatty_term
    {K P i : ℕ}
    (hi : i < P) :
    (3 : ZMod (2 ^ K)) ^ P *
        ((2 : ZMod (2 ^ K)) ^ beattyIndex i *
          invThreePow K (i + 1)) =
      (3 : ZMod (2 ^ K)) ^ (P - 1 - i) *
        (2 : ZMod (2 ^ K)) ^ beattyIndex i := by
  have hExp :
      P = (P - 1 - i) + (i + 1) := by
    omega
  have hPow :
      (3 : ZMod (2 ^ K)) ^ P =
        (3 : ZMod (2 ^ K)) ^ (P - 1 - i) *
          (3 : ZMod (2 ^ K)) ^ (i + 1) := by
    rw [hExp, pow_add]
    simp
  rw [hPow]
  have hcancel :=
    threePow_mul_invThreePow K (i + 1)
  calc
    ((3 : ZMod (2 ^ K)) ^ (P - 1 - i) *
        (3 : ZMod (2 ^ K)) ^ (i + 1)) *
        ((2 : ZMod (2 ^ K)) ^ beattyIndex i *
          invThreePow K (i + 1))
        =
      (3 : ZMod (2 ^ K)) ^ (P - 1 - i) *
        (2 : ZMod (2 ^ K)) ^ beattyIndex i *
        ((3 : ZMod (2 ^ K)) ^ (i + 1) *
          invThreePow K (i + 1)) := by
      ring
    _ =
      (3 : ZMod (2 ^ K)) ^ (P - 1 - i) *
        (2 : ZMod (2 ^ K)) ^ beattyIndex i := by
      rw [hcancel]
      ring

/--
Christoffel 型の有限和を整数上の `foldl` として保持する補助定義。

sigma 記法を使わず、`List.range n` 上で
`3^(P-1-i) * 2^beattyIndex(i)` を順に加える。
-/
private def beattyPhiFold (P n : ℕ) : ℤ :=
  (List.range n).foldl
    (fun acc i =>
      acc +
        (3 : ℤ) ^ (P - 1 - i) *
          (2 : ℤ) ^ beattyIndex i)
    0

/--
先頭 `n` 個の Beatty 逆寄与を `3^P` 倍したものは、
対応する整数 `phi` fold の `ZMod (2^K)` 像に一致する。
-/
theorem scaled_beatty_prefix_eq_phiFold
    (K P n : ℕ)
    (hn : n ≤ P) :
    (3 : ZMod (2 ^ K)) ^ P *
        beattyInverseContribution K n =
      (beattyPhiFold P n : ZMod (2 ^ K)) := by
  induction n with
  | zero =>
      simp [beattyPhiFold]
  | succ n ih =>
      have hnP : n < P := by
        omega
      rw [beattyInverseContribution_succ, mul_add]
      rw [ih (by omega)]
      rw [scale_one_beatty_term hnP]
      have hFold :
          beattyPhiFold P (n + 1) =
            beattyPhiFold P n +
              (3 : ℤ) ^ (P - 1 - n) *
                (2 : ℤ) ^ beattyIndex n := by
        unfold beattyPhiFold
        rw [List.range_succ, List.foldl_append]
        rfl
      rw [hFold]
      push_cast
      ring

/--
`List.range n` 上で各項が一致すれば、加算 `foldl` の結果も一致する。

actual Christoffel の floor 項を Beatty 項へ項別変換するために使う。
-/
private theorem foldl_range_add_congr
    (n : ℕ)
    (f g : ℕ → ℤ)
    (hfg : ∀ i : ℕ, i < n → f i = g i) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      (List.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hprefix : ∀ i : ℕ, i < n → f i = g i := by
        intro i hi
        exact hfg i (by omega)
      rw [ih hprefix]
      rw [hfg n (by omega)]

/--
actual convergent 上では explicit Christoffel `phi` と
Beatty index で書いた `phi` fold が一致する。

ここで `actual_beattyIndex_eq_div` を使い、
floor 表現と Beatty 表現を項ごとに同定する。
-/
theorem actual_phi_eq_beattyPhiFold
    {j : ℕ}
    (hj : 9 ≤ j) :
    criticalChristoffelPhiAt actualCriticalContinuedFractionData j =
      beattyPhiFold (criticalPowerP j) (criticalPowerP j) := by
  unfold criticalChristoffelPhiAt criticalChristoffelPhi beattyPhiFold
  apply foldl_range_add_congr
  intro i hi
  change
    (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
        (2 : ℤ) ^
          (i * criticalPowerQ j / criticalPowerP j) =
      (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
        (2 : ℤ) ^ beattyIndex i
  rw [actual_beattyIndex_eq_div hj hi]

/--
critical Xi の先頭 `p_j` 項を `3^p_j` 倍すると、
actual Christoffel numerator `phi_j` に一致する。
-/
theorem actual_scaled_prefix_eq_phi
    {j K : ℕ}
    (hj : 9 ≤ j) :
    (3 : ZMod (2 ^ K)) ^ criticalPowerP j *
        beattyInverseContribution K (criticalPowerP j) =
      (criticalChristoffelPhiAt actualCriticalContinuedFractionData j :
        ZMod (2 ^ K)) := by
  rw [scaled_beatty_prefix_eq_phiFold K (criticalPowerP j) (criticalPowerP j) le_rfl]
  rw [← actual_phi_eq_beattyPhiFold hj]

/--
odd convergent の numerator `p_j` に対応する Beatty index は
ちょうど denominator `q_j` である。

current/next の Farey adjacency と power orientation から
`3^p_j` が `2^q_j` と `2^(q_j+1)` の間にあることを確定する。
-/
private theorem beattyIndex_p_odd
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1) :
    beattyIndex (criticalPowerP j) = criticalPowerQ j := by
  let cur := criticalPowerConvergent j
  let nxt := criticalPowerConvergent (j + 1)
  let x : CriticalPowerFraction := {
    p := criticalPowerP j
    q := criticalPowerQ j + 1
    q_pos := by positivity
  }
  have hCurAbove : cur.Above := by
    simpa [cur] using
      (criticalPower_orientation j).2 hjOdd
  have hNextBelow : nxt.Below := by
    have hEven : (j + 1) % 2 = 0 := by
      omega
    simpa [nxt] using
      (criticalPower_orientation (j + 1)).1 hEven
  have hadj := criticalPower_adjacent_next hj
  have hdet :
      nxt.p * cur.q + 1 = cur.p * nxt.q := by
    rcases hadj with h | h
    · have hcross :=
        CriticalPowerFraction.cross_lt_of_below_above
          hNextBelow hCurAbove
      dsimp [cur, nxt] at h hcross ⊢
      omega
    · simpa [cur, nxt] using h
  have hxLeNext :
      x.p * nxt.q ≤ nxt.p * x.q := by
    have hnp : 0 < nxt.p := by
      change 0 < criticalPowerP (j + 1)
      exact criticalPowerP_pos (by omega)
    have hnpOne : 1 ≤ nxt.p := by omega
    change cur.p * nxt.q ≤ nxt.p * (cur.q + 1)
    calc
      cur.p * nxt.q
          = nxt.p * cur.q + 1 := hdet.symm
      _ ≤ nxt.p * cur.q + nxt.p :=
        Nat.add_le_add_left hnpOne (nxt.p * cur.q)
      _ = nxt.p * (cur.q + 1) := by
        rw [Nat.mul_add]
        simp
  have hxBelow : x.Below :=
    CriticalPowerFraction.below_of_fraction_le_below
      hxLeNext hNextBelow
  apply Nat.le_antisymm
  · apply beattyIndex_le_of_upper
    have hxPow := hxBelow
    unfold CriticalPowerFraction.Below at hxPow
    simpa [x] using Nat.le_of_lt hxPow
  · by_contra hnot
    have hb :
        beattyIndex (criticalPowerP j) <
          criticalPowerQ j := by
      omega
    have hup :=
      beattyIndex_upper (criticalPowerP j)
    have hpow :
        2 ^ (beattyIndex (criticalPowerP j) + 1) ≤
          2 ^ criticalPowerQ j :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        (by omega)
    have hcur :
        2 ^ criticalPowerQ j <
          3 ^ criticalPowerP j := by
      have h := hCurAbove
      unfold CriticalPowerFraction.Above at h
      simpa [cur, criticalPowerP, criticalPowerQ] using h
    omega

/--
even convergent の numerator `p_j` に対応する Beatty index は
`q_j - 1` である。

even orientation と隣接 Farey fraction を使い、
`3^p_j` を `2^(q_j-1)` と `2^q_j` の間に挟む。
-/
private theorem beattyIndex_p_even
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    beattyIndex (criticalPowerP j) = criticalPowerQ j - 1 := by
  let cur := criticalPowerConvergent j
  let nxt := criticalPowerConvergent (j + 1)
  have hqTwo : 2 ≤ criticalPowerQ j := by
    have hmono :=
      criticalPowerQ_mono_of_le
        (show 9 ≤ j by exact hj)
    rw [criticalPowerQ_nine] at hmono
    omega
  let x : CriticalPowerFraction := {
    p := criticalPowerP j
    q := criticalPowerQ j - 1
    q_pos := by omega
  }
  have hCurBelow : cur.Below := by
    simpa [cur] using
      (criticalPower_orientation j).1 hjEven
  have hNextAbove : nxt.Above := by
    have hOdd : (j + 1) % 2 = 1 := by
      omega
    simpa [nxt] using
      (criticalPower_orientation (j + 1)).2 hOdd
  have hadj := criticalPower_adjacent_next hj
  have hdet :
      cur.p * nxt.q + 1 = nxt.p * cur.q := by
    rcases hadj with h | h
    · simpa [cur, nxt] using h
    · have hcross :=
        CriticalPowerFraction.cross_lt_of_below_above
          hCurBelow hNextAbove
      dsimp [cur, nxt] at h hcross ⊢
      omega
  have hNextLeX :
      nxt.p * x.q ≤ x.p * nxt.q := by
    have hnp : 0 < nxt.p := by
      change 0 < criticalPowerP (j + 1)
      exact criticalPowerP_pos (by omega)
    have hnpOne : 1 ≤ nxt.p := by omega
    have hqTwo' : 2 ≤ cur.q := by
      change 2 ≤ criticalPowerQ j
      exact hqTwo
    have hqEq : cur.q = (cur.q - 1) + 1 := by
      omega
    have hdetSplit :
        cur.p * nxt.q + 1 =
          nxt.p * (cur.q - 1) + nxt.p := by
      calc
        cur.p * nxt.q + 1
            = nxt.p * cur.q := hdet
        _ = nxt.p * ((cur.q - 1) + 1) := by
          rw [hqEq]
          simp
        _ = nxt.p * (cur.q - 1) + nxt.p := by
          rw [Nat.mul_add]
          simp
    change nxt.p * (cur.q - 1) ≤ cur.p * nxt.q
    omega
  have hxAbove : x.Above :=
    CriticalPowerFraction.above_of_above_le_fraction
      hNextLeX hNextAbove
  apply Nat.le_antisymm
  · apply beattyIndex_le_of_upper
    have hcur := hCurBelow
    unfold CriticalPowerFraction.Below at hcur
    have hcurPow :
        3 ^ criticalPowerP j <
          2 ^ criticalPowerQ j := by
      simpa [cur, criticalPowerP, criticalPowerQ] using hcur
    simpa [show (criticalPowerQ j - 1) + 1 =
        criticalPowerQ j by omega] using
      Nat.le_of_lt hcurPow
  · by_contra hnot
    have hb :
        beattyIndex (criticalPowerP j) <
          criticalPowerQ j - 1 := by
      omega
    have hup :=
      beattyIndex_upper (criticalPowerP j)
    have hpow :
        2 ^ (beattyIndex (criticalPowerP j) + 1) ≤
          2 ^ (criticalPowerQ j - 1) :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        (by omega)
    have hxPow := hxAbove
    unfold CriticalPowerFraction.Above at hxPow
    have hx :
        2 ^ (criticalPowerQ j - 1) <
          3 ^ criticalPowerP j := by
      simpa [x] using hxPow
    omega

/--
`j ≥ 9` では actual strong overlap length は正である。

`q_(j+1) > q_j > 0` から `q_(j+1)-1 > 0` を得る。
-/
private theorem overlap_length_pos
    {j : ℕ}
    (hj : 9 ≤ j) :
    0 < criticalStrongOverlapLength actualCriticalContinuedFractionData j := by
  change 0 < criticalPowerQ (j + 1) - 1
  have hq := criticalPowerQ_lt_next hj
  have hcur := criticalPowerQ_pos j
  omega

/--
正の strong overlap length における critical prefix height も正である。

critical height の expanding inequality が height 0 を排除する。
-/
private theorem height_at_overlap_length_pos
    {j : ℕ}
    (hj : 9 ≤ j) :
    0 < criticalPrefixHeight
      (criticalStrongOverlapLength actualCriticalContinuedFractionData j) := by
  let L :=
    criticalStrongOverlapLength actualCriticalContinuedFractionData j
  have hL : 0 < L := by
    simpa [L] using overlap_length_pos hj
  change 0 < criticalPrefixHeight L
  rw [criticalPrefixHeight_eq_criticalHeight_of_pos hL]
  have hExp := criticalHeight_expanding L
  by_contra hnot
  have hzero : criticalHeight L = 0 := by
    omega
  rw [hzero] at hExp
  simp at hExp

/--
任意の長さ `L` について、
その prefix height の Beatty 位置は `L` 以降にある。

overlap length から得た local precision を Beatty tail 消滅条件へ渡す。
-/
private theorem beattyIndex_height_ge_length
    {L : ℕ} :
    L ≤ beattyIndex (criticalPrefixHeight L) := by
  by_contra hnot
  have hsucc :
      beattyIndex (criticalPrefixHeight L) + 1 ≤ L := by
    omega
  have hheight :=
    (beattyIndex_is_nth_critical_one
      (criticalPrefixHeight L)).2
  have hmono :=
    criticalPrefixHeight_mono_of_le hsucc
  rw [hheight] at hmono
  omega

/--
height が `criticalPrefixHeight L` より小さいなら、
対応する Beatty index は `L` より前にある。

strong overlap の適用範囲へ Beatty 位置を戻すための逆向き評価。
-/
private theorem beattyIndex_lt_length_of_lt_height
    {L s : ℕ}
    (hs : s < criticalPrefixHeight L) :
    beattyIndex s < L := by
  by_contra hnot
  have hle : L ≤ beattyIndex s := by
    omega
  have hm :=
    criticalPrefixHeight_mono_of_le hle
  rw [criticalPrefixHeight_beattyIndex] at hm
  omega

/--
odd convergent の strong overlap 内では Beatty index が加法的に shift する。

`beattyIndex (p_j+s) = q_j + beattyIndex s`
を true-bit の位置一意性から導く。
-/
private theorem odd_beatty_shift
    {j s : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hs : s < criticalPrefixHeight
      (criticalStrongOverlapLength actualCriticalContinuedFractionData j)) :
    beattyIndex (criticalPowerP j + s) =
      criticalPowerQ j + beattyIndex s := by
  let D := actualCriticalContinuedFractionData
  let L := criticalStrongOverlapLength D j
  let r := beattyIndex s
  have hrLt : r < L := by
    simpa [r, L, D] using
      beattyIndex_lt_length_of_lt_height hs
  have hbit : criticalSturmianBit r = true := by
    simpa [r] using criticalSturmianBit_beattyIndex s
  have O :=
    actualCriticalBeattyConvergentCorridor.toCriticalSturmianStrongOverlap
  have hshiftBit :=
    O.odd_overlap j r hj hjOdd hrLt
  rw [hbit] at hshiftBit
  have hheight :=
    actualCriticalBeattyConvergentCorridor.odd_height_shift
      j r hj hjOdd (Nat.le_of_lt hrLt)
  have hrHeight :=
    criticalPrefixHeight_beattyIndex s
  have hheight' :
      criticalPrefixHeight (criticalPowerQ j + r) =
        criticalPowerP j + s := by
    simpa [D, r, actualCriticalContinuedFractionData, hrHeight] using hheight
  have hpos :=
    critical_true_position_eq_beattyIndex hshiftBit
  have hpos' :
      criticalPowerQ j + r =
        beattyIndex
          (criticalPrefixHeight (criticalPowerQ j + r)) := by
    simpa [D, actualCriticalContinuedFractionData] using hpos
  rw [hheight'] at hpos'
  simpa [r] using hpos'.symm

/--
even convergent の corrected overlap 内での Beatty shift。

最初の flat step を補正して
`beattyIndex (p_j+1+s) = q_j + beattyIndex (s+1)`
を得る。
-/
private theorem even_beatty_shift
    {j s : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hs : s + 1 < criticalPrefixHeight
      (criticalStrongOverlapLength actualCriticalContinuedFractionData j)) :
    beattyIndex (criticalPowerP j + 1 + s) =
      criticalPowerQ j + beattyIndex (s + 1) := by
  let D := actualCriticalContinuedFractionData
  let L := criticalStrongOverlapLength D j
  let r := beattyIndex (s + 1)
  have hrLt : r < L := by
    simpa [r, L, D] using
      beattyIndex_lt_length_of_lt_height hs
  have hrPos : 0 < r := by
    have hstrict :=
      beattyIndex_strictMono (show 0 < s + 1 by omega)
    simpa [r] using hstrict
  have hbit : criticalSturmianBit r = true := by
    simpa [r] using
      criticalSturmianBit_beattyIndex (s + 1)
  have O :=
    actualCriticalBeattyConvergentCorridor.toCriticalSturmianStrongOverlap
  have hshiftBit :=
    O.even_overlap j r hj hjEven hrLt
  have hzero :
      zeroShiftCriticalBit r = criticalSturmianBit r := by
    cases hr : r with
    | zero =>
        have hfalse : False := by
          rw [hr] at hrPos
          omega
        exact hfalse.elim
    | succ n =>
        rfl
  rw [hzero, hbit] at hshiftBit
  have hheight :=
    actualCriticalBeattyConvergentCorridor.even_height_shift_pos
      j r hj hjEven hrPos (Nat.le_of_lt hrLt)
  have hrHeight :=
    criticalPrefixHeight_beattyIndex (s + 1)
  have hheight' :
      criticalPrefixHeight (criticalPowerQ j + r) =
        criticalPowerP j + (s + 1) := by
    simpa [D, r, actualCriticalContinuedFractionData, hrHeight] using hheight
  have hpos :=
    critical_true_position_eq_beattyIndex hshiftBit
  have hpos' :
      criticalPowerQ j + r =
        beattyIndex
          (criticalPrefixHeight (criticalPowerQ j + r)) := by
    simpa [D, actualCriticalContinuedFractionData] using hpos
  rw [hheight'] at hpos'
  simpa [r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos'.symm

/--
odd convergent の overlap 内で tail を shift したときの scaling identity。

Beatty 位置の加法則により、`3^p_j` 倍した shifted tail を
`2^q_j` 倍した原点側 prefix へ移す。
-/
theorem scaled_odd_shift_tail
    {j K N : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hN : N ≤ criticalPrefixHeight
      (criticalStrongOverlapLength actualCriticalContinuedFractionData j)) :
    (3 : ZMod (2 ^ K)) ^ criticalPowerP j *
        beattyInverseTail K (criticalPowerP j) N =
      (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
        beattyInverseContribution K N := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hNLt :
          N < criticalPrefixHeight
            (criticalStrongOverlapLength
              actualCriticalContinuedFractionData j) := by
        omega
      rw [beattyInverseTail_succ, mul_add]
      rw [ih (by omega)]
      rw [beattyInverseContribution_succ, mul_add]
      have hpos :=
        odd_beatty_shift hj hjOdd hNLt
      have hInv :=
        threePow_mul_invThreePow_add
          K (criticalPowerP j) (N + 1)
      have hTerm :
          (3 : ZMod (2 ^ K)) ^ criticalPowerP j *
              ((2 : ZMod (2 ^ K)) ^
                  beattyIndex (criticalPowerP j + N) *
                invThreePow K
                  (criticalPowerP j + N + 1))
            =
          (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
              ((2 : ZMod (2 ^ K)) ^ beattyIndex N *
                invThreePow K (N + 1)) := by
        rw [hpos, pow_add]
        have hInv' :
            (3 : ZMod (2 ^ K)) ^ criticalPowerP j *
                invThreePow K
                  (criticalPowerP j + (N + 1)) =
              invThreePow K (N + 1) := hInv
        rw [show criticalPowerP j + N + 1 =
            criticalPowerP j + (N + 1) by omega]
        calc
          (3 : ZMod (2 ^ K)) ^ criticalPowerP j *
              (((2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
                  (2 : ZMod (2 ^ K)) ^ beattyIndex N) *
                invThreePow K
                  (criticalPowerP j + (N + 1)))
              =
            (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
              (2 : ZMod (2 ^ K)) ^ beattyIndex N *
              ((3 : ZMod (2 ^ K)) ^ criticalPowerP j *
                invThreePow K
                  (criticalPowerP j + (N + 1))) := by
              ring
          _ =
            (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
              ((2 : ZMod (2 ^ K)) ^ beattyIndex N *
                invThreePow K (N + 1)) := by
              rw [hInv']
              ring
      rw [hTerm]

/--
even convergent の corrected shift に対する tail scaling identity。

even 側では最初の flat step を 1 だけずらして扱う。
そのため odd 側の shift identity と異なり、右辺には追加の係数 `3` が現れる。

証明では、

* `even_beatty_shift` による 2 冪指数の分離
* `threePow_mul_invThreePow_add` による先頭 `3^(p_j+1)` の相殺
* 残った逆 3 冪を一段送ることで生じる係数 `3`

を個別に処理する。

`pow_add` を目標全体へ rewrite すると外側の `3^(p_j+1)` まで展開されるため、
2 冪の分離は専用の局所等式 `hTwoPow` として行う。
-/
theorem scaled_even_shift_tail
    {j K N : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hN : N + 1 ≤ criticalPrefixHeight
      (criticalStrongOverlapLength actualCriticalContinuedFractionData j)) :
    (3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) *
        beattyInverseTail K (criticalPowerP j + 1) N =
      (2 : ZMod (2 ^ K)) ^ criticalPowerQ j * 3 *
        beattyInverseTail K 1 N := by
  induction N with
  | zero =>
      change
        (3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) * 0 =
          (2 : ZMod (2 ^ K)) ^ criticalPowerQ j * 3 * 0
      ring
  | succ N ih =>
      have hNLt :
          N + 1 <
            criticalPrefixHeight
              (criticalStrongOverlapLength
                actualCriticalContinuedFractionData j) := by
        omega
      rw [beattyInverseTail_succ, mul_add]
      rw [ih (by omega)]
      rw [beattyInverseTail_succ, mul_add]
      have hpos :
          beattyIndex (criticalPowerP j + 1 + N) =
            criticalPowerQ j + beattyIndex (N + 1) :=
        even_beatty_shift hj hjEven hNLt
      /-
      shifted Beatty index の 2 冪だけを分離する。

      `rw [pow_add]` を大きな目標に直接使わず、
      外側の `3^(p_j+1)` をそのまま保持する。
      -/
      have hTwoPow :
          (2 : ZMod (2 ^ K)) ^
              beattyIndex (criticalPowerP j + 1 + N) =
            (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
              (2 : ZMod (2 ^ K)) ^ beattyIndex (N + 1) := by
        rw [hpos, pow_add]
      /-
      shifted inverse-3 factor から先頭 `p_j+1` 個を相殺する。
      -/
      have hInv :
          (3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) *
              invThreePow K
                (criticalPowerP j + 1 + N + 1) =
            invThreePow K (N + 1) := by
        have h :=
          threePow_mul_invThreePow_add
            K
            (criticalPowerP j + 1)
            (N + 1)
        rw [
          show criticalPowerP j + 1 + N + 1 =
              (criticalPowerP j + 1) + (N + 1) by
            omega
        ]
        exact h
      /-
      残った inverse-3 factor を一段先へ送る。

        invThreePow (N+1)
          = 3 * invThreePow (N+2)

      が even branch に現れる追加係数 `3` の由来。
      -/
      have hInvSucc :
          invThreePow K (N + 1) =
            3 * invThreePow K (N + 2) := by
        have h :=
          threePow_mul_invThreePow_add
            K 1 (N + 1)
        have hIndex :
            1 + (N + 1) = N + 2 := by
          omega
        rw [pow_one, hIndex] at h
        exact h.symm
      /-
      `beattyInverseTail K 1` 側で出る index 表記を
      `N+1`, `N+2` に正規化する。
      -/
      have hBeattyIndex :
          beattyIndex (1 + N) =
            beattyIndex (N + 1) := by
        congr 1
        omega
      have hInvIndex :
          invThreePow K (1 + N + 1) =
            invThreePow K (N + 2) := by
        congr 1
        omega
      /-
      induction step で追加された 1 項だけの scaling identity。
      -/
      have hTerm :
          (3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) *
              ((2 : ZMod (2 ^ K)) ^
                  beattyIndex (criticalPowerP j + 1 + N) *
                invThreePow K
                  (criticalPowerP j + 1 + N + 1))
            =
          (2 : ZMod (2 ^ K)) ^ criticalPowerQ j * 3 *
              ((2 : ZMod (2 ^ K)) ^ beattyIndex (1 + N) *
                invThreePow K (1 + N + 1)) := by
        calc
          (3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) *
              ((2 : ZMod (2 ^ K)) ^
                  beattyIndex (criticalPowerP j + 1 + N) *
                invThreePow K
                  (criticalPowerP j + 1 + N + 1))
              =
            (3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) *
              (((2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
                  (2 : ZMod (2 ^ K)) ^ beattyIndex (N + 1)) *
                invThreePow K
                  (criticalPowerP j + 1 + N + 1)) := by
                rw [hTwoPow]
          _ =
            (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
              (2 : ZMod (2 ^ K)) ^ beattyIndex (N + 1) *
              ((3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) *
                invThreePow K
                  (criticalPowerP j + 1 + N + 1)) := by
                ring
          _ =
            (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
              (2 : ZMod (2 ^ K)) ^ beattyIndex (N + 1) *
                invThreePow K (N + 1) := by
                rw [hInv]
          _ =
            (2 : ZMod (2 ^ K)) ^ criticalPowerQ j *
              (2 : ZMod (2 ^ K)) ^ beattyIndex (N + 1) *
                (3 * invThreePow K (N + 2)) := by
                rw [hInvSucc]
          _ =
            (2 : ZMod (2 ^ K)) ^ criticalPowerQ j * 3 *
              ((2 : ZMod (2 ^ K)) ^ beattyIndex (1 + N) *
                invThreePow K (1 + N + 1)) := by
                rw [hBeattyIndex, hInvIndex]
                ring
      rw [hTerm]

/--
even branch の corrected base prefix を explicit Christoffel `phi` に変換する。

先頭 `p_j` 項の既知の scaling に最後の 1 項を加え、
`3*phi_j + 2^(q_j-1)` を得る。
-/
private theorem actual_even_scaled_base
    {j K : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    (3 : ZMod (2 ^ K)) ^ (criticalPowerP j + 1) *
        beattyInverseContribution K (criticalPowerP j + 1) =
      3 * (criticalChristoffelPhiAt actualCriticalContinuedFractionData j :
        ZMod (2 ^ K)) +
        (2 : ZMod (2 ^ K)) ^ (criticalPowerQ j - 1) := by
  rw [beattyInverseContribution_succ]
  rw [pow_succ, mul_add]
  have hbase :=
    actual_scaled_prefix_eq_phi
      (j := j) (K := K) hj
  have hpos :=
    beattyIndex_p_even hj hjEven
  have hInv :=
    threePow_mul_invThreePow_add
      K (criticalPowerP j) 1
  have hFirst :
      (3 : ZMod (2 ^ K)) *
          ((3 : ZMod (2 ^ K)) ^ criticalPowerP j *
            beattyInverseContribution K (criticalPowerP j))
        =
      3 *
        (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ K)) := by
    rw [hbase]
  have hLast :
      (3 : ZMod (2 ^ K)) *
          ((3 : ZMod (2 ^ K)) ^ criticalPowerP j *
            ((2 : ZMod (2 ^ K)) ^ beattyIndex (criticalPowerP j) *
              invThreePow K (criticalPowerP j + 1)))
        =
      (2 : ZMod (2 ^ K)) ^ (criticalPowerQ j - 1) := by
    rw [hpos]
    have hInv' :
        (3 : ZMod (2 ^ K)) ^ criticalPowerP j *
            invThreePow K (criticalPowerP j + 1) =
          invThreePow K 1 :=
      hInv
    have hOne :
        (3 : ZMod (2 ^ K)) * invThreePow K 1 = 1 := by
      simpa only [pow_one] using threePow_mul_invThreePow K 1
    calc
      (3 : ZMod (2 ^ K)) *
          ((3 : ZMod (2 ^ K)) ^ criticalPowerP j *
            ((2 : ZMod (2 ^ K)) ^ (criticalPowerQ j - 1) *
              invThreePow K (criticalPowerP j + 1)))
          =
        (2 : ZMod (2 ^ K)) ^ (criticalPowerQ j - 1) *
          ((3 : ZMod (2 ^ K)) *
            ((3 : ZMod (2 ^ K)) ^ criticalPowerP j *
              invThreePow K (criticalPowerP j + 1))) := by
            ring
      _ =
        (2 : ZMod (2 ^ K)) ^ (criticalPowerQ j - 1) *
          ((3 : ZMod (2 ^ K)) * invThreePow K 1) := by
            rw [hInv']
      _ =
        (2 : ZMod (2 ^ K)) ^ (criticalPowerQ j - 1) := by
            rw [hOne]
            ring
  calc
    (3 : ZMod (2 ^ K)) ^ criticalPowerP j * 3 *
          beattyInverseContribution K (criticalPowerP j) +
        (3 : ZMod (2 ^ K)) ^ criticalPowerP j * 3 *
          ((2 : ZMod (2 ^ K)) ^ beattyIndex (criticalPowerP j) *
            invThreePow K (criticalPowerP j + 1))
        =
      3 *
          ((3 : ZMod (2 ^ K)) ^ criticalPowerP j *
            beattyInverseContribution K (criticalPowerP j)) +
        3 *
          ((3 : ZMod (2 ^ K)) ^ criticalPowerP j *
            ((2 : ZMod (2 ^ K)) ^ beattyIndex (criticalPowerP j) *
              invThreePow K (criticalPowerP j + 1))) := by
        ring
    _ =
      3 *
          (criticalChristoffelPhiAt
            actualCriticalContinuedFractionData j :
            ZMod (2 ^ K)) +
        (2 : ZMod (2 ^ K)) ^ (criticalPowerQ j - 1) := by
      rw [hFirst, hLast]

/--
最初の Beatty 逆寄与は 3 倍すると 1 になる。

even branch の first-flat 補正項を簡約するために使う。
-/
private theorem three_mul_first_beattyContribution
    (K : ℕ) :
    3 * beattyInverseContribution K 1 = 1 := by
  rw [beattyInverseContribution_succ]
  change
    3 *
      (0 +
        (2 : ZMod (2 ^ K)) ^ beattyIndex 0 *
          invThreePow K 1) = 1
  rw [beattyIndex_zero, pow_zero, zero_add, one_mul]
  have h :=
    threePow_mul_invThreePow K 1
  simpa only [pow_one] using h

/--
precision `e = beattyIndex m` が strong window 内にあるなら、
候補 count `m` はその window の full critical height 以下である。
-/
private theorem candidate_count_le_full_height
    {j e m : ℕ}
    (hPrecision : e ≤ strongDenominatorWindowUpper criticalPowerQ j)
    (hem : e = beattyIndex m) :
    m ≤ criticalPrefixHeight
      (strongDenominatorWindowUpper criticalPowerQ j) := by
  have hm := criticalPrefixHeight_beattyIndex m
  rw [← hem] at hm
  have hmono := criticalPrefixHeight_mono_of_le hPrecision
  rw [hm] at hmono
  exact hmono

/--
odd branch の corrected finite Xi identity を内部算術だけで証明する。

strong overlap、Beatty shift、Christoffel `phi`、tail 消滅を接続し、
外部仮定なしで `ZMod (2^e)` 上の有限 Xi 恒等式を得る。
-/
theorem actual_odd_finiteXi_identity
    {j e m : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hPrecision : e ≤ strongDenominatorWindowUpper criticalPowerQ j)
    (hem : e = beattyIndex m) :
    (criticalChristoffelPhiAt actualCriticalContinuedFractionData j : ZMod (2 ^ e)) +
        criticalXiTruncationClass e m *
          (((3 : ℤ) ^ criticalPowerP j - (2 : ℤ) ^ criticalPowerQ j : ℤ) :
            ZMod (2 ^ e)) = 0 := by
  let q := criticalPowerQ j
  let p := criticalPowerP j
  let L :=
    criticalStrongOverlapLength actualCriticalContinuedFractionData j
  let E := strongDenominatorWindowUpper criticalPowerQ j
  let T := criticalPrefixHeight L
  let M := criticalPrefixHeight E
  have hE : E = q + L := by
    dsimp [E, q, L]
    unfold strongDenominatorWindowUpper
    change
      criticalPowerQ j + criticalPowerQ (j + 1) - 1 =
        criticalPowerQ j + (criticalPowerQ (j + 1) - 1)
    have hNextPos := criticalPowerQ_pos (j + 1)
    omega
  have hLPos : 0 < L := by
    simpa [L] using overlap_length_pos hj
  have hTPos : 0 < T := by
    simpa [T, L] using height_at_overlap_length_pos hj
  have hShift :=
    actualCriticalBeattyConvergentCorridor.odd_height_shift
      j L hj hjOdd le_rfl
  have hM : M = p + T := by
    change criticalPrefixHeight E = p + T
    rw [hE]
    simpa only [p, q, T, L, actualCriticalContinuedFractionData] using hShift
  have hmM : m ≤ M := by
    simpa [M, E] using
      candidate_count_le_full_height
        (j := j) (e := e) (m := m) hPrecision hem
  have hBm :
      beattyInverseContribution e M =
        beattyInverseContribution e m :=
    beattyContribution_eq_of_count_le hem hmM
  have hdecomp :
      beattyInverseContribution e M =
        beattyInverseContribution e p +
          beattyInverseTail e p T := by
    have hsum : p + T = M := by
      omega
    rw [← hsum]
    exact beattyInverseContribution_add_tail e p T
  have hscaleTail :
      (3 : ZMod (2 ^ e)) ^ p *
          beattyInverseTail e p T =
        (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e T := by
    simpa [p, q, T, L] using
      scaled_odd_shift_tail
        (j := j) (K := e) (N := T)
        hj hjOdd le_rfl
  have hbase :
      (3 : ZMod (2 ^ e)) ^ p *
          beattyInverseContribution e p =
        (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) := by
    simpa [p] using
      actual_scaled_prefix_eq_phi
        (j := j) (K := e) hj
  have hPrecisionQL : e ≤ q + L := by
    rw [← hE]
    simpa only [E] using hPrecision
  have hBTailZero :
      (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseTail e T p = 0 := by
    apply twoPow_mul_beattyTail_zero
        (q := q) (L := L) (a := T) (n := p)
    · exact hPrecisionQL
    · simpa only [T] using
        (beattyIndex_height_ge_length (L := L))
  have hBM_BT :
      (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e M =
        (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e T := by
    have hMT : M = T + p := by
      omega
    rw [hMT, beattyInverseContribution_add_tail]
    rw [mul_add, hBTailZero, add_zero]
  have hscaled :
      (3 : ZMod (2 ^ e)) ^ p *
          beattyInverseContribution e M =
        (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e M := by
    calc
      (3 : ZMod (2 ^ e)) ^ p *
            beattyInverseContribution e M
          =
        (3 : ZMod (2 ^ e)) ^ p *
          (beattyInverseContribution e p +
            beattyInverseTail e p T) := by
          rw [hdecomp]
      _ =
        (3 : ZMod (2 ^ e)) ^ p *
            beattyInverseContribution e p +
          (3 : ZMod (2 ^ e)) ^ p *
            beattyInverseTail e p T := by
          ring
      _ =
        (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e T := by
          rw [hbase, hscaleTail]
      _ =
        (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e M := by
          rw [hBM_BT]
  unfold criticalXiTruncationClass
  rw [← hBm]
  push_cast
  have hscaled' :
      (3 : ZMod (2 ^ e)) ^ criticalPowerP j *
          beattyInverseContribution e M =
        (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j *
          beattyInverseContribution e M := by
    simpa [p, q] using hscaled
  change
    (criticalChristoffelPhiAt
      actualCriticalContinuedFractionData j :
      ZMod (2 ^ e)) +
      (-beattyInverseContribution e M) *
        ((3 : ZMod (2 ^ e)) ^ criticalPowerP j -
          (2 : ZMod (2 ^ e)) ^ criticalPowerQ j) = 0
  calc
    (criticalChristoffelPhiAt
        actualCriticalContinuedFractionData j :
        ZMod (2 ^ e)) +
        (-beattyInverseContribution e M) *
          ((3 : ZMod (2 ^ e)) ^ criticalPowerP j -
            (2 : ZMod (2 ^ e)) ^ criticalPowerQ j)
        =
      (criticalChristoffelPhiAt
        actualCriticalContinuedFractionData j :
        ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j *
          beattyInverseContribution e M -
        (3 : ZMod (2 ^ e)) ^ criticalPowerP j *
          beattyInverseContribution e M := by
      ring
    _ = 0 := by
      rw [hscaled']
      ring

/--
even branch の corrected finite Xi identity を内部算術だけで証明する。

first-flat 補正に対応する `2^(q_j-1)` と係数 3 を保持したまま、
strong overlap の有限 tail を corrected Christoffel 式へ接続する。
-/
theorem actual_even_finiteXi_identity
    {j e m : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hPrecision : e ≤ strongDenominatorWindowUpper criticalPowerQ j)
    (hem : e = beattyIndex m) :
    (((2 : ℤ) ^ (criticalPowerQ j - 1) -
        3 * criticalChristoffelPhiAt actualCriticalContinuedFractionData j : ℤ) :
        ZMod (2 ^ e)) +
      criticalXiTruncationClass e m *
        ((3 * ((2 : ℤ) ^ criticalPowerQ j -
          (3 : ℤ) ^ criticalPowerP j) : ℤ) : ZMod (2 ^ e)) = 0 := by
  let q := criticalPowerQ j
  let p := criticalPowerP j
  let L :=
    criticalStrongOverlapLength actualCriticalContinuedFractionData j
  let E := strongDenominatorWindowUpper criticalPowerQ j
  let T := criticalPrefixHeight L
  let M := criticalPrefixHeight E
  have hE : E = q + L := by
    dsimp [E, q, L]
    unfold strongDenominatorWindowUpper
    change
      criticalPowerQ j + criticalPowerQ (j + 1) - 1 =
        criticalPowerQ j + (criticalPowerQ (j + 1) - 1)
    have hNextPos := criticalPowerQ_pos (j + 1)
    omega
  have hLPos : 0 < L := by
    simpa [L] using overlap_length_pos hj
  have hTPos : 0 < T := by
    simpa [T, L] using height_at_overlap_length_pos hj
  have hShift :=
    actualCriticalBeattyConvergentCorridor.even_height_shift_pos
      j L hj hjEven hLPos le_rfl
  have hM : M = p + T := by
    change criticalPrefixHeight E = p + T
    rw [hE]
    simpa only [p, q, T, L, actualCriticalContinuedFractionData] using hShift
  have hmM : m ≤ M := by
    simpa [M, E] using
      candidate_count_le_full_height
        (j := j) (e := e) (m := m) hPrecision hem
  have hBm :
      beattyInverseContribution e M =
        beattyInverseContribution e m :=
    beattyContribution_eq_of_count_le hem hmM
  have hTOne : 1 ≤ T := by
    omega
  have hdecomp :
      beattyInverseContribution e M =
        beattyInverseContribution e (p + 1) +
          beattyInverseTail e (p + 1) (T - 1) := by
    have hsum : (p + 1) + (T - 1) = M := by
      omega
    rw [← hsum]
    exact
      beattyInverseContribution_add_tail
        e (p + 1) (T - 1)
  have hTailLength :
      T - 1 + 1 ≤ T := by
    omega
  have hscaleTail :
      (3 : ZMod (2 ^ e)) ^ (p + 1) *
          beattyInverseTail e (p + 1) (T - 1) =
        (2 : ZMod (2 ^ e)) ^ q * 3 *
          beattyInverseTail e 1 (T - 1) := by
    simpa only [p, q, T, L] using
      scaled_even_shift_tail
        (j := j) (K := e) (N := T - 1)
        hj hjEven
        (by
          simpa only [T, L] using hTailLength)
  have hbase :
      (3 : ZMod (2 ^ e)) ^ (p + 1) *
          beattyInverseContribution e (p + 1) =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (q - 1) := by
    simpa only [p, q] using
      actual_even_scaled_base
        (j := j) (K := e) hj hjEven
  have hPrecisionQL : e ≤ q + L := by
    rw [← hE]
    simpa only [E] using hPrecision
  have hBTailZero :
      (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseTail e T p = 0 := by
    apply twoPow_mul_beattyTail_zero
        (q := q) (L := L) (a := T) (n := p)
    · exact hPrecisionQL
    · simpa only [T] using
        (beattyIndex_height_ge_length (L := L))
  have hBM_BT :
      (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e M =
        (2 : ZMod (2 ^ e)) ^ q *
          beattyInverseContribution e T := by
    have hMT : M = T + p := by
      omega
    rw [hMT, beattyInverseContribution_add_tail]
    rw [mul_add, hBTailZero, add_zero]
  have hTailOne :
      beattyInverseTail e 1 (T - 1) =
        beattyInverseContribution e T -
          beattyInverseContribution e 1 := by
    have hsum : 1 + (T - 1) = T := by
      omega
    have h :=
      beattyInverseContribution_add_tail
        e 1 (T - 1)
    rw [hsum] at h
    apply (eq_sub_iff_add_eq).2
    rw [h]
    ring
  have hfirst :
      3 * beattyInverseContribution e 1 = 1 :=
    three_mul_first_beattyContribution e
  have hscaled :
      (3 : ZMod (2 ^ e)) ^ (p + 1) *
          beattyInverseContribution e M =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (q - 1) +
        (2 : ZMod (2 ^ e)) ^ q *
          (3 * beattyInverseContribution e M - 1) := by
    calc
      (3 : ZMod (2 ^ e)) ^ (p + 1) *
            beattyInverseContribution e M
          =
        (3 : ZMod (2 ^ e)) ^ (p + 1) *
          (beattyInverseContribution e (p + 1) +
            beattyInverseTail e (p + 1) (T - 1)) := by
          rw [hdecomp]
      _ =
        (3 : ZMod (2 ^ e)) ^ (p + 1) *
            beattyInverseContribution e (p + 1) +
          (3 : ZMod (2 ^ e)) ^ (p + 1) *
            beattyInverseTail e (p + 1) (T - 1) := by
          ring
      _ =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (q - 1) +
        (2 : ZMod (2 ^ e)) ^ q * 3 *
          beattyInverseTail e 1 (T - 1) := by
          rw [hbase, hscaleTail]
      _ =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (q - 1) +
        (2 : ZMod (2 ^ e)) ^ q * 3 *
          (beattyInverseContribution e T -
            beattyInverseContribution e 1) := by
          rw [hTailOne]
      _ =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
          (2 : ZMod (2 ^ e)) ^ (q - 1) +
          3 * ((2 : ZMod (2 ^ e)) ^ q *
            beattyInverseContribution e T) -
          (2 : ZMod (2 ^ e)) ^ q *
            (3 * beattyInverseContribution e 1) := by
        ring
      _ =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
          (2 : ZMod (2 ^ e)) ^ (q - 1) +
          3 * ((2 : ZMod (2 ^ e)) ^ q *
            beattyInverseContribution e M) -
          (2 : ZMod (2 ^ e)) ^ q := by
        rw [← hBM_BT, hfirst]
        ring
      _ =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
          (2 : ZMod (2 ^ e)) ^ (q - 1) +
          (2 : ZMod (2 ^ e)) ^ q *
            (3 * beattyInverseContribution e M - 1) := by
        ring
  unfold criticalXiTruncationClass
  rw [← hBm]
  push_cast
  have hscaled' :
      (3 : ZMod (2 ^ e)) ^ (criticalPowerP j + 1) *
          beattyInverseContribution e M =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) +
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j *
          (3 * beattyInverseContribution e M - 1) := by
    simpa [p, q] using hscaled
  change
    ((2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) -
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e))) +
      (-beattyInverseContribution e M) *
        (3 * ((2 : ZMod (2 ^ e)) ^ criticalPowerQ j -
          (3 : ZMod (2 ^ e)) ^ criticalPowerP j)) = 0
  have hqPos : 0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have htwo :
      (2 : ZMod (2 ^ e)) ^ criticalPowerQ j =
        (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) * 2 := by
    have hqEq :
        criticalPowerQ j =
          (criticalPowerQ j - 1) + 1 := by
      omega
    rw [hqEq, pow_add, pow_one]
    simp
  have hs :
      3 * (3 : ZMod (2 ^ e)) ^ criticalPowerP j *
          beattyInverseContribution e M =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) +
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j *
          (3 * beattyInverseContribution e M - 1) := by
    calc
      3 * (3 : ZMod (2 ^ e)) ^ criticalPowerP j *
          beattyInverseContribution e M
          =
        (3 : ZMod (2 ^ e)) ^ (criticalPowerP j + 1) *
          beattyInverseContribution e M := by
        rw [pow_succ]
        ring
      _ =
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) +
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j *
          (3 * beattyInverseContribution e M - 1) :=
        hscaled'
  have hs0 :
      3 * (3 : ZMod (2 ^ e)) ^ criticalPowerP j *
          beattyInverseContribution e M -
        (3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) +
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j *
          (3 * beattyInverseContribution e M - 1)) = 0 := by
    rw [hs]
    ring
  have htwo0 :
      2 * (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) -
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j = 0 := by
    rw [htwo]
    ring
  calc
    ((2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) -
        3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e))) +
      (-beattyInverseContribution e M) *
        (3 * ((2 : ZMod (2 ^ e)) ^ criticalPowerQ j -
          (3 : ZMod (2 ^ e)) ^ criticalPowerP j))
        =
      (3 * (3 : ZMod (2 ^ e)) ^ criticalPowerP j *
          beattyInverseContribution e M -
        (3 * (criticalChristoffelPhiAt
          actualCriticalContinuedFractionData j :
          ZMod (2 ^ e)) +
        (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) +
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j *
          (3 * beattyInverseContribution e M - 1))) +
      (2 * (2 : ZMod (2 ^ e)) ^ (criticalPowerQ j - 1) -
        (2 : ZMod (2 ^ e)) ^ criticalPowerQ j) := by
      ring
    _ = 0 := by
      rw [hs0, htwo0]
      ring

/--
odd/even の finite Xi 恒等式をまとめ、
既存の `CriticalSturmianFiniteScanIdentity` packet を追加仮定なしで構成する。
-/
theorem actualCriticalSturmianFiniteScanIdentity :
    CriticalSturmianFiniteScanIdentity
      actualCriticalContinuedFractionData
      actualCriticalBeattyConvergentCorridor.toCriticalSturmianStrongOverlap := by
  refine {
    odd_identity := ?_
    even_identity := ?_
  }
  · intro j e m hj hjOdd he hem
    exact actual_odd_finiteXi_identity hj hjOdd he hem
  · intro j e m hj hjEven he hem
    exact actual_even_finiteXi_identity hj hjEven he hem

/--
ここまでで strong-match pipeline の Steps 1--5 を
actual critical data に対して内部的にすべて具体化する。
-/
theorem actualCriticalStrongMatchProof :
    CriticalStrongMatchProof actualOrientedCriticalContinuedFractionData := {
  corridor := actualCriticalBeattyConvergentCorridor
  finiteScan := actualCriticalSturmianFiniteScanIdentity
}

end ExternalArithmetic
end CSTMicro
end Collatz2
