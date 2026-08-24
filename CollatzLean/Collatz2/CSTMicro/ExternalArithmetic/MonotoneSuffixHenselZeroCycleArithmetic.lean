import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselRepeatArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Monotone suffix Hensel chain: zero-cycle arithmetic

zero scaled difference

  Q_j = 2^Delta Q_i

が repeated exponent block 上で起きた場合の純粋算術をまとめる。

ここでは Beatty / Collatz geometry は使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MonotoneSuffixHenselChain

/-- qOne recurrence を n 段展開したときの forcing numerator。 -/
def qOneBlockNumerator
    (C : MonotoneSuffixHenselChain)
    (i : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      3 * C.qOneBlockNumerator i n +
        (2 : ℤ) ^ n * (2 : ℤ) ^ C.delta (i + n)

@[simp] theorem qOneBlockNumerator_zero
    (C : MonotoneSuffixHenselChain)
    (i : ℕ) :
    C.qOneBlockNumerator i 0 = 0 := rfl

/-- qOne recurrence の exact n-step 展開。 -/
theorem qOne_iterate
    (C : MonotoneSuffixHenselChain)
    {i n : ℕ}
    (hEnd : i + n ≤ C.width) :
    (3 : ℤ) ^ n * C.qOne i =
      (2 : ℤ) ^ n * C.qOne (i + n) +
        C.qOneBlockNumerator i n := by
  revert hEnd
  induction n with
  | zero =>
      intro hEnd
      simp
  | succ n ih =>
      intro hEnd
      have hPrev : i + n ≤ C.width := by omega
      have hiN : i + n < C.width := by omega
      have hIH := ih hPrev
      have hRec := C.qOne_recurrence (i := i + n) hiN
      have hIdx : i + n + 1 = i + (n + 1) := by omega
      rw [hIdx] at hRec
      change
        (3 : ℤ) ^ (n + 1) * C.qOne i =
          (2 : ℤ) ^ (n + 1) * C.qOne (i + (n + 1)) +
            (3 * C.qOneBlockNumerator i n +
              (2 : ℤ) ^ n * (2 : ℤ) ^ C.delta (i + n))
      rw [pow_succ, pow_succ]
      calc
        (3 : ℤ) ^ n * 3 * C.qOne i
            = 3 * ((3 : ℤ) ^ n * C.qOne i) := by
                ring
        _ = 3 *
            ((2 : ℤ) ^ n * C.qOne (i + n) +
              C.qOneBlockNumerator i n) := by
                rw [hIH]
        _ =
            (2 : ℤ) ^ n * (3 * C.qOne (i + n)) +
              3 * C.qOneBlockNumerator i n := by
                ring
        _ =
            (2 : ℤ) ^ n *
                (2 * C.qOne (i + (n + 1)) +
                  (2 : ℤ) ^ C.delta (i + n)) +
              3 * C.qOneBlockNumerator i n := by
                rw [hRec]
        _ =
            (2 : ℤ) ^ n * 2 * C.qOne (i + (n + 1)) +
              (3 * C.qOneBlockNumerator i n +
                (2 : ℤ) ^ n *
                  (2 : ℤ) ^ C.delta (i + n)) := by
                ring

/--
zero scaled difference は repeated block の全 intermediate offsets に伝播する。
-/
theorem scaledDifference_eq_zero_of_zero_repeat
    (C : MonotoneSuffixHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hZero : C.scaledDifference i j Delta 0 = 0) :
    ∀ r : ℕ, r ≤ m →
      C.scaledDifference i j Delta r = 0 := by
  intro r
  induction r with
  | zero =>
      intro hr
      exact hZero
  | succ r ih =>
      intro hr
      have hrLt : r < m := by omega
      have hi : i + r < C.width := by omega
      have hj : j + r < C.width := by omega
      have hStep :=
        C.scaledDifference_step
          (i := i) (j := j) (Delta := Delta) (r := r)
          hi hj (hBlock r (by omega))
      have hPrev := ih (by omega)
      rw [hPrev] at hStep
      linarith

/-- zero repeat の各 offset は scaled state そのものになる。 -/
theorem scaledState_at_of_zero_repeat
    (C : MonotoneSuffixHenselChain)
    {i j m Delta r : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hZero : C.scaledDifference i j Delta 0 = 0)
    (hr : r ≤ m) :
    C.ScaledState (i + r) (j + r) Delta := by
  constructor
  · exact hBlock r hr
  · have hMr :=
      C.scaledDifference_eq_zero_of_zero_repeat
        hiEnd hjEnd hBlock hZero r hr
    have hEq :=
      (C.scaledDifference_zero_eq_zero_iff
        (i := i + r) (j := j + r) (Delta := Delta)).1
        (by simpa [scaledDifference, Nat.add_assoc] using hMr)
    exact hEq

/-- repeated block transport は scaled difference の正符号を保存する。 -/
theorem scaledDifference_pos_of_pos_zero
    (C : MonotoneSuffixHenselChain)
    {i j m Delta r : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hPos : 0 < C.scaledDifference i j Delta 0)
    (hr : r ≤ m) :
    0 < C.scaledDifference i j Delta r := by
  have hTransport :=
    C.scaledDifference_transport
      (i := i) (j := j) (m := r) (Delta := Delta)
      (by omega) (by omega)
      (fun t ht => hBlock t (le_trans ht hr))
  have hTwoPos : 0 < (2 : ℤ) ^ r := by positivity
  have hThreePos : 0 < (3 : ℤ) ^ r := by positivity
  nlinarith

/-- repeated block transport は scaled difference の負符号を保存する。 -/
theorem scaledDifference_neg_of_neg_zero
    (C : MonotoneSuffixHenselChain)
    {i j m Delta r : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hNeg : C.scaledDifference i j Delta 0 < 0)
    (hr : r ≤ m) :
    C.scaledDifference i j Delta r < 0 := by
  have hTransport :=
    C.scaledDifference_transport
      (i := i) (j := j) (m := r) (Delta := Delta)
      (by omega) (by omega)
      (fun t ht => hBlock t (le_trans ht hr))
  have hTwoPos : 0 < (2 : ℤ) ^ r := by positivity
  have hThreePos : 0 < (3 : ℤ) ^ r := by positivity
  nlinarith

/--
`p = g*d` の周期を `d` ごとの block に分けたとき、
最後の block より前の開始位置 `t*d` は `p-d` 以下にある。

可変量どうしの積を含むため `omega` / `nlinarith` に直接任せず、
`t+1 ≤ g` を `d` 倍してから Nat subtraction に戻す。
-/
private theorem repeatedBlock_offset_le
    {p d g t : ℕ}
    (hpEq : p = g * d)
    (ht : t < g) :
    t * d ≤ p - d := by
  have htSucc : t + 1 ≤ g := by
    omega
  have hMul :
      (t + 1) * d ≤ g * d := by
    gcongr
  have hExpand :
      (t + 1) * d = t * d + d := by
    ring
  rw [hExpand] at hMul
  rw [hpEq]
  omega


/--
上側評価

  x ≤ 2^(t*e) * y

をさらに `2^e` 倍し、

  2^e * x ≤ 2^((t+1)*e) * y

へ1 block 進める。
-/
private theorem twoPow_scale_upper_step
    {e t : ℕ}
    {x y : ℤ}
    (h :
      x ≤ (2 : ℤ) ^ (t * e) * y) :
    (2 : ℤ) ^ e * x ≤
      (2 : ℤ) ^ ((t + 1) * e) * y := by
  have hPowNonneg :
      0 ≤ (2 : ℤ) ^ e := by
    positivity
  have hMul :=
    mul_le_mul_of_nonneg_left h hPowNonneg
  have hPow :
      (2 : ℤ) ^ e * (2 : ℤ) ^ (t * e) =
        (2 : ℤ) ^ ((t + 1) * e) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    (2 : ℤ) ^ e * x
        ≤
      (2 : ℤ) ^ e *
        ((2 : ℤ) ^ (t * e) * y) := hMul
    _ =
      ((2 : ℤ) ^ e *
          (2 : ℤ) ^ (t * e)) * y := by
        ring
    _ =
      (2 : ℤ) ^ ((t + 1) * e) * y := by
        rw [hPow]


/--
下側評価

  2^(t*e) * x ≤ y

をさらに `2^e` 倍し、

  2^((t+1)*e) * x ≤ 2^e * y

へ1 block 進める。
-/
private theorem twoPow_scale_lower_step
    {e t : ℕ}
    {x y : ℤ}
    (h :
      (2 : ℤ) ^ (t * e) * x ≤ y) :
    (2 : ℤ) ^ ((t + 1) * e) * x ≤
      (2 : ℤ) ^ e * y := by
  have hPowNonneg :
      0 ≤ (2 : ℤ) ^ e := by
    positivity
  have hMul :=
    mul_le_mul_of_nonneg_left h hPowNonneg
  have hPow :
      (2 : ℤ) ^ e * (2 : ℤ) ^ (t * e) =
        (2 : ℤ) ^ ((t + 1) * e) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    (2 : ℤ) ^ ((t + 1) * e) * x
        =
      ((2 : ℤ) ^ e *
          (2 : ℤ) ^ (t * e)) * x := by
        rw [hPow]
    _ =
      (2 : ℤ) ^ e *
        ((2 : ℤ) ^ (t * e) * x) := by
        ring
    _ ≤
      (2 : ℤ) ^ e * y := hMul


/--
最初の `d`-block の scaled difference が負なら、
その符号は repeated divisor cycle 全体へ伝播する。

したがって各 `t ≤ g` について

  Q_(i+t*d) ≤ 2^(t*e) Q_i

となり、`t>0` なら strict inequality になる。

これは repeated cycle の負方向の単調伝播部分だけを切り出した補題。
-/
private theorem qOne_upper_of_negative_repeated_divisor
    (C : MonotoneSuffixHenselChain)
    {i p d g e : ℕ}
    (hpEq : p = g * d)
    (hdLeP : d ≤ p)
    (hEnd : i + p ≤ C.width)
    (hPeriod :
      C.SameDeltaOffsetBlock i (i + d) (p - d) e)
    (hNeg :
      C.scaledDifference i (i + d) e 0 < 0) :
    ∀ t : ℕ, t ≤ g →
      C.qOne (i + t * d) ≤
        (2 : ℤ) ^ (t * e) * C.qOne i ∧
      (0 < t →
        C.qOne (i + t * d) <
          (2 : ℤ) ^ (t * e) * C.qOne i) := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp
  | succ t ih =>
      intro ht
      have htLt : t < g := by
        omega
      have htd :
          t * d ≤ p - d :=
        repeatedBlock_offset_le hpEq htLt
      have hMr :
          C.scaledDifference
              i (i + d) e (t * d) < 0 := by
        apply C.scaledDifference_neg_of_neg_zero
          (m := p - d)
          (hiEnd := by omega)
          (hjEnd := by omega)
          hPeriod
        · exact hNeg
        · exact htd
      have hMExpr :
          C.scaledDifference
              i (i + d) e (t * d) =
            C.qOne (i + (t + 1) * d) -
              (2 : ℤ) ^ e *
                C.qOne (i + t * d) := by
        unfold MonotoneSuffixHenselChain.scaledDifference
        have hIdx :
            i + d + t * d =
              i + (t + 1) * d := by
          ring
        rw [hIdx]
      rw [hMExpr] at hMr
      have hStep :
          C.qOne (i + (t + 1) * d) <
            (2 : ℤ) ^ e *
              C.qOne (i + t * d) := by
        linarith
      have hIH := ih (by omega)
      have hScaled :
          (2 : ℤ) ^ e *
              C.qOne (i + t * d) ≤
            (2 : ℤ) ^ ((t + 1) * e) *
              C.qOne i :=
        twoPow_scale_upper_step hIH.1
      constructor
      · exact le_trans (le_of_lt hStep) hScaled
      · intro htPos
        exact lt_of_lt_of_le hStep hScaled


/--
最初の `d`-block の scaled difference が正なら、
その符号は repeated divisor cycle 全体へ伝播する。

したがって各 `t ≤ g` について

  2^(t*e) Q_i ≤ Q_(i+t*d)

となり、`t>0` なら strict inequality になる。

上の negative lemma とちょうど逆向きの単調伝播を与える。
-/
private theorem qOne_lower_of_positive_repeated_divisor
    (C : MonotoneSuffixHenselChain)
    {i p d g e : ℕ}
    (hpEq : p = g * d)
    (hdLeP : d ≤ p)
    (hEnd : i + p ≤ C.width)
    (hPeriod :
      C.SameDeltaOffsetBlock i (i + d) (p - d) e)
    (hPos :
      0 < C.scaledDifference i (i + d) e 0) :
    ∀ t : ℕ, t ≤ g →
      (2 : ℤ) ^ (t * e) * C.qOne i ≤
        C.qOne (i + t * d) ∧
      (0 < t →
        (2 : ℤ) ^ (t * e) * C.qOne i <
          C.qOne (i + t * d)) := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp
  | succ t ih =>
      intro ht
      have htLt : t < g := by
        omega
      have htd :
          t * d ≤ p - d :=
        repeatedBlock_offset_le hpEq htLt
      have hMr :
          0 <
            C.scaledDifference
              i (i + d) e (t * d) := by
        apply C.scaledDifference_pos_of_pos_zero
          (m := p - d)
          (hiEnd := by omega)
          (hjEnd := by omega)
          hPeriod
        · exact hPos
        · exact htd
      have hMExpr :
          C.scaledDifference
              i (i + d) e (t * d) =
            C.qOne (i + (t + 1) * d) -
              (2 : ℤ) ^ e *
                C.qOne (i + t * d) := by
        unfold MonotoneSuffixHenselChain.scaledDifference
        have hIdx :
            i + d + t * d =
              i + (t + 1) * d := by
          ring
        rw [hIdx]
      rw [hMExpr] at hMr
      have hStep :
          (2 : ℤ) ^ e *
              C.qOne (i + t * d) <
            C.qOne (i + (t + 1) * d) := by
        linarith
      have hIH := ih (by omega)
      have hScaled :
          (2 : ℤ) ^ ((t + 1) * e) *
              C.qOne i ≤
            (2 : ℤ) ^ e *
              C.qOne (i + t * d) :=
        twoPow_scale_lower_step hIH.1
      constructor
      · exact le_trans hScaled (le_of_lt hStep)
      · intro htPos
        exact lt_of_le_of_lt hScaled hStep

/--
`p = g*d`, `Delta = g*e` で、外側の `p`-cycle が scaled zero state
になっているとする。

さらに `d` ごとの各 block が同じ offset pattern を持つなら、
最初の `d`-block の scaled difference は zero でなければならない。

zero でないと仮定すると、その符号は全 `g` block に strict に伝播し、
最後には outer zero state と矛盾して `x < x` を生じる。
-/
private theorem scaledDifference_zero_of_repeated_divisor_cycle
    (C : MonotoneSuffixHenselChain)
    {i p d g Delta e : ℕ}
    (hg : 0 < g)
    (hpEq : p = g * d)
    (hDeltaEq : Delta = g * e)
    (hEnd : i + p ≤ C.width)
    (hPeriod :
      C.SameDeltaOffsetBlock i (i + d) (p - d) e)
    (hOuter : C.ScaledState i (i + p) Delta) :
    C.scaledDifference i (i + d) e 0 = 0 := by
  have hdLeP : d ≤ p := by
    rw [hpEq]
    calc
      d = 1 * d := by simp
      _ ≤ g * d := by
        gcongr
        omega
  by_cases hZero :
      C.scaledDifference i (i + d) e 0 = 0
  · exact hZero
  have hSigns :
      C.scaledDifference i (i + d) e 0 < 0 ∨
        0 < C.scaledDifference i (i + d) e 0 :=
    lt_or_gt_of_ne hZero
  rcases hSigns with hNeg | hPos
  · have hInd :=
      qOne_upper_of_negative_repeated_divisor
        C hpEq hdLeP hEnd hPeriod hNeg
    have hFinal := hInd g le_rfl
    have hStrict := hFinal.2 hg
    have hIdx :
        i + g * d = i + p := by
      rw [hpEq]
    have hPow :
        g * e = Delta :=
      hDeltaEq.symm
    rw [hIdx, hPow, hOuter.2] at hStrict
    exact (lt_irrefl _ hStrict).elim
  · have hInd :=
      qOne_lower_of_positive_repeated_divisor
        C hpEq hdLeP hEnd hPeriod hPos
    have hFinal := hInd g le_rfl
    have hStrict := hFinal.2 hg
    have hIdx :
        i + g * d = i + p := by
      rw [hpEq]
    have hPow :
        g * e = Delta :=
      hDeltaEq.symm
    rw [hIdx, hPow, hOuter.2] at hStrict
    exact (lt_irrefl _ hStrict).elim

/--
外側の zero cycle が `g` 個の同型な `d`-block からなるなら、
最初の `d`-block 自身も scaled zero state になる。

第一成分の delta relation は repeated block 条件の offset `0` から直接得る。
第二成分は、最初の scaled difference が非零だと仮定すると
その符号が全 block に strict に伝播し、外側の zero state と矛盾することから得る。

これは gcd descent によって carry rank から短い周期 `d` を得た後に使う
純粋な repeated-cycle descent。
-/
theorem scaledState_of_repeated_divisor_cycle
    (C : MonotoneSuffixHenselChain)
    {i p d g Delta e : ℕ}
    (hg : 0 < g)
    (hpEq : p = g * d)
    (hDeltaEq : Delta = g * e)
    (hEnd : i + p ≤ C.width)
    (hPeriod :
      C.SameDeltaOffsetBlock i (i + d) (p - d) e)
    (hOuter : C.ScaledState i (i + p) Delta) :
    C.ScaledState i (i + d) e := by
  have hdLeP : d ≤ p := by
    rw [hpEq]
    calc
      d = 1 * d := by simp
      _ ≤ g * d := by
        gcongr
        omega
  have hPeriodZero :=
    hPeriod 0 (by omega)
  simp only [Nat.add_zero] at hPeriodZero
  constructor
  · exact hPeriodZero
  · have hZero :
        C.scaledDifference i (i + d) e 0 = 0 :=
      scaledDifference_zero_of_repeated_divisor_cycle
        C hg hpEq hDeltaEq hEnd hPeriod hOuter
    exact
      (C.scaledDifference_zero_eq_zero_iff
        (i := i)
        (j := i + d)
        (Delta := e)).1 hZero

/--
一周期内にある divisor block

  delta_(i+d+r) = delta_(i+r) + e

を `d` ごとに繰り返す。

`p = g*d` で、基準 offset `t` が `0 ≤ t < d` にあるなら、
`k ≤ g-1` に対して

  delta_(i+t+k*d) = delta_(i+t) + k*e

となる。

これは divisor period を一つの outer period 内で反復するための
基本的な telescoping 補題。
-/
private theorem delta_iterate_divisor_blocks
    (C : MonotoneSuffixHenselChain)
    {i p d g e t k : ℕ}
    (hpEq : p = g * d)
    (hShort :
      C.SameDeltaOffsetBlock i (i + d) (p - d) e)
    (htLt : t < d)
    (hk : k ≤ g - 1) :
    C.delta (i + t + k * d) =
      C.delta (i + t) + k * e := by
  have hpMinus :
      p - d = (g - 1) * d := by
    rw [hpEq]
    calc
      g * d - d = g * d - 1 * d := by simp
      _ = (g - 1) * d := by
        simpa using (Nat.sub_mul g 1 d).symm
  revert hk
  induction k with
  | zero =>
      intro hk
      simp
  | succ k ih =>
      intro hk
      have hkLt : k < g - 1 := by
        omega
      have hOffset :
          t + k * d ≤ p - d := by
        rw [hpMinus]
        have hLt :
            t + k * d < d + k * d :=
          Nat.add_lt_add_right htLt (k * d)
        have hEqMul :
            d + k * d = (k + 1) * d := by
          ring
        rw [hEqMul] at hLt
        have hMul :
            (k + 1) * d ≤ (g - 1) * d :=
          Nat.mul_le_mul_right d (by omega)
        exact le_trans (Nat.le_of_lt hLt) hMul
      have hStep :=
        hShort (t + k * d) hOffset
      have hPrev :=
        ih (by omega)
      have hIdx0 :
          i + (t + k * d) =
            i + t + k * d := by
        omega
      have hIdx1 :
          i + d + (t + k * d) =
            i + t + (k + 1) * d := by
        ring
      rw [hIdx0, hIdx1] at hStep
      rw [hPrev] at hStep
      calc
        C.delta (i + t + (k + 1) * d)
            =
          C.delta (i + t) + k * e + e := hStep
        _ =
          C.delta (i + t) + (k + 1) * e := by
            ring

/--
`p = g*d`, `Delta = g*e` で `g ≥ 2` とする。

最初の outer period `0,...,p-1` について、

* `r ≤ p-d` の部分は既知の divisor block `hShort` をそのまま使う。
* 最後の `d-1` 個の tail は、`d`-block を `g-1` 回積み上げた値と
  outer period の関係を比較する。

これにより、一周期全体で divisor period `d/e` が成立する。
-/
private theorem sameDeltaOffsetBlock_divisor_one_outer_period
    (C : MonotoneSuffixHenselChain)
    {i p d g Delta e m : ℕ}
    (hd : 0 < d)
    (hgTwo : 2 ≤ g)
    (hpEq : p = g * d)
    (hDeltaEq : Delta = g * e)
    (hpPred : p - 1 ≤ m)
    (hOuter :
      C.SameDeltaOffsetBlock i (i + p) m Delta)
    (hShort :
      C.SameDeltaOffsetBlock i (i + d) (p - d) e) :
    C.SameDeltaOffsetBlock i (i + d) (p - 1) e := by
  have hdLeP : d ≤ p := by
    rw [hpEq]
    simpa using
      Nat.mul_le_mul_right d
        (show 1 ≤ g by omega)
  have hpPos : 0 < p := by
    omega
  have hpMinus :
      p - d = (g - 1) * d := by
    rw [hpEq]
    calc
      g * d - d = g * d - 1 * d := by simp
      _ = (g - 1) * d := by
        simpa using (Nat.sub_mul g 1 d).symm
  intro r hr
  have hrP : r < p := by
    omega
  by_cases hrShort : r ≤ p - d
  · exact hShort r hrShort
  · have hrLow : p - d < r := by
      omega
    let t := r - (p - d)
    have htLt : t < d := by
      dsimp [t]
      omega
    have hrEq :
        r = (p - d) + t := by
      dsimp [t]
      omega
    have hBefore :=
      delta_iterate_divisor_blocks
        C
        hpEq
        hShort
        htLt
        (k := g - 1)
        le_rfl
    have htLePred :
        t ≤ p - 1 := by
      omega
    have hOuterT :=
      hOuter t (le_trans htLePred hpPred)
    have hIdxBefore :
        i + t + (g - 1) * d =
          i + r := by
      rw [hpMinus] at hrEq
      omega
    rw [hIdxBefore] at hBefore
    have hIdxOuter :
        i + p + t =
          i + r + d := by
      omega
    rw [hIdxOuter] at hOuterT
    have hOuterT' :
        C.delta (i + r + d) =
          C.delta (i + t) + Delta := by
      simpa [Nat.add_assoc] using hOuterT
    have hgOne : 1 ≤ g := by
      omega
    have hSplitE :
        g * e = (g - 1) * e + e := by
      calc
        g * e =
            ((g - 1) + 1) * e := by
              rw [Nat.sub_add_cancel hgOne]
        _ = (g - 1) * e + e := by
              ring
    have hGoalIdx :
        i + d + r = i + r + d := by
      omega
    rw [hGoalIdx]
    calc
      C.delta (i + r + d)
          =
        C.delta (i + t) + Delta := hOuterT'
      _ =
        C.delta (i + t) + g * e := by
          rw [hDeltaEq]
      _ =
        C.delta (i + t) + ((g - 1) * e + e) := by
          rw [hSplitE]
      _ =
        (C.delta (i + t) + (g - 1) * e) + e := by
          omega
      _ =
        C.delta (i + r) + e := by
          rw [← hBefore]

/--
ある offset `r` で divisor relation

  delta_(i+d+r) = delta_(i+r) + e

が成立しているとする。

さらに `r` と `r+d` の両方で outer period `p/Delta` が使えるなら、
同じ divisor relation は `p` だけ右へ移した offset `r+p` でも成立する。

outer offset `Delta` は左右に共通して現れるため、ここではその具体的な値は不要。
-/
private theorem sameDeltaOffset_at_shift_outer_period
    (C : MonotoneSuffixHenselChain)
    {i p d Delta e m r : ℕ}
    (hOuter :
      C.SameDeltaOffsetBlock i (i + p) m Delta)
    (hr : r ≤ m)
    (hrd : r + d ≤ m)
    (hDiv :
      C.delta (i + d + r) =
        C.delta (i + r) + e) :
    C.delta (i + d + (r + p)) =
      C.delta (i + (r + p)) + e := by
  have hOuter0 :=
    hOuter r hr
  have hOuterD :=
    hOuter (r + d) hrd
  have hIdxDiv :
      i + d + r = i + (r + d) := by
    omega
  rw [hIdxDiv] at hDiv
  have hIdxLeft :
      i + d + (r + p) =
        i + p + (r + d) := by
    omega
  have hIdxRight :
      i + (r + p) =
        i + p + r := by
    omega
  rw [hIdxLeft, hIdxRight]
  rw [hOuterD, hOuter0, hDiv]
  omega

/--
outer period が

  p = g*d,
  Delta = g*e

と divisor period `d/e` の整数倍になっているとする。

さらに、

* outer period `p/Delta` が長さ `m` 全体で成立し、
* 最初の一周期内では divisor period `d/e` が確認できている

なら、divisor period `d/e` は同じ長さ `m` 全体へ延長できる。

証明は二段階。

1. 最初の outer period `0,...,p-1` を divisor period で埋める。
2. `r ≥ p` では `r-p` に対する帰納仮定を、
   outer period を一回使って `r` まで運ぶ。

`g = 1` の場合は `p=d`, `Delta=e` なので outer period 自身が
そのまま divisor period である。
-/
theorem sameDeltaOffsetBlock_extend_divisor
    (C : MonotoneSuffixHenselChain)
    {i p d g Delta e m : ℕ}
    (hd : 0 < d)
    (hg : 0 < g)
    (hpEq : p = g * d)
    (hDeltaEq : Delta = g * e)
    (hpPred : p - 1 ≤ m)
    (hOuter :
      C.SameDeltaOffsetBlock i (i + p) m Delta)
    (hShort :
      C.SameDeltaOffsetBlock i (i + d) (p - d) e) :
    C.SameDeltaOffsetBlock i (i + d) m e := by
  by_cases hgOne : g = 1
  · have hpD : p = d := by
      rw [hpEq, hgOne]
      simp
    have hDe : Delta = e := by
      rw [hDeltaEq, hgOne]
      simp
    rw [hpD, hDe] at hOuter
    exact hOuter
  · have hgTwo : 2 ≤ g := by
      omega
    have hdLeP : d ≤ p := by
      rw [hpEq]
      simpa using
        Nat.mul_le_mul_right d
          (show 1 ≤ g by omega)
    have hpPos : 0 < p := by
      omega
    have hFirstPeriod :=
      sameDeltaOffsetBlock_divisor_one_outer_period
        C
        hd
        hgTwo
        hpEq
        hDeltaEq
        hpPred
        hOuter
        hShort
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro hr
        by_cases hrP : r < p
        · have hrPred :
              r ≤ p - 1 := by
            omega
          exact hFirstPeriod r hrPred
        · have hpLe : p ≤ r := by
            omega
          let r0 := r - p
          have hr0Lt : r0 < r := by
            dsimp [r0]
            omega
          have hr0Eq :
              r0 + p = r := by
            dsimp [r0]
            omega
          have hr0m :
              r0 ≤ m := by
            dsimp [r0]
            omega
          have hr0d :
              r0 + d ≤ m := by
            dsimp [r0]
            omega
          have hIH :=
            ih r0 hr0Lt hr0m
          have hShift :=
            sameDeltaOffset_at_shift_outer_period
              C
              hOuter
              hr0m
              hr0d
              hIH
          rw [hr0Eq] at hShift
          exact hShift

end MonotoneSuffixHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
