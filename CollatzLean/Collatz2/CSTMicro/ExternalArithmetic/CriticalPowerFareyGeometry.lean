import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerFarey
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyConvergentCorridor
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelHeightFour

set_option linter.style.nativeDecide false

/-!
# Power-Farey geometry -> Beatty corridor and Christoffel height geometry

ここでは transcendence theory を使わない。
consecutive critical power-Farey neighbors の間に denominator
`< q_j+q_{j+1}` の rational が入れないことだけから

* critical-height shift corridor,
* Christoffel summand `<= 2^q`,

を導く。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open CriticalPowerFraction

private def mkCriticalFraction
    (p q : ℕ)
    (hq : 0 < q) : CriticalPowerFraction :=
  ⟨p, q, hq⟩

theorem criticalHeight_eq_of_pred_below_and_above
    {k m : ℕ}
    (hm : 0 < m)
    (hBelow : 3 ^ (m - 1) < 2 ^ k)
    (hAbove : 2 ^ k < 3 ^ m) :
    criticalHeight k = m := by
  have hle : criticalHeight k ≤ m :=
    criticalHeight_le_of_expanding hAbove
  have hge : m ≤ criticalHeight k := by
    by_contra hnot
    have hcrit : criticalHeight k ≤ m - 1 := by omega
    have hp :
        3 ^ criticalHeight k ≤ 3 ^ (m - 1) :=
      Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hcrit
    have hexp := criticalHeight_expanding k
    omega
  omega

private theorem critical_pred_below
    {r : ℕ}
    (hr : 0 < r) :
    3 ^ (criticalHeight r - 1) < 2 ^ r := by
  have hmPos : 0 < criticalHeight r := by
    by_contra h
    have h0 : criticalHeight r = 0 := by omega
    have hexp := criticalHeight_expanding r
    rw [h0] at hexp
    simp at hexp
  have hnot :=
    not_expanding_below_criticalHeight
      r (criticalHeight r - 1) (by omega)
  by_cases hz : criticalHeight r - 1 = 0
  · rw [hz]
    simp only [pow_zero, Nat.one_lt_two_pow_iff, ne_eq]
    have : 1 < 2 ^ r := by
      cases r with
      | zero => omega
      | succ n =>
          rw [pow_succ]
          have hp : 0 < 2 ^ n := Nat.pow_pos (by omega)
          omega
    exact Nat.ne_of_gt hr
  · have hpPos : 0 < criticalHeight r - 1 := Nat.pos_of_ne_zero hz
    have hne' :=
      CriticalPowerFraction.twoPow_ne_threePow_of_pos
        (p := criticalHeight r - 1)
        (q := r)
        hr
    omega

private theorem critical_height_above
    {r : ℕ} :
    2 ^ r < 3 ^ criticalHeight r :=
  criticalHeight_expanding r

private theorem no_small_between_current_next
    {j : ℕ}
    (hj : 9 ≤ j)
    (x : CriticalPowerFraction)
    (hBetween :
      ((criticalPowerConvergent j).p * x.q <
          x.p * (criticalPowerConvergent j).q ∧
        x.p * (criticalPowerConvergent (j + 1)).q <
          (criticalPowerConvergent (j + 1)).p * x.q) ∨
      ((criticalPowerConvergent (j + 1)).p * x.q <
          x.p * (criticalPowerConvergent (j + 1)).q ∧
        x.p * (criticalPowerConvergent j).q <
          (criticalPowerConvergent j).p * x.q)) :
    criticalPowerQ j + criticalPowerQ (j + 1) ≤ x.q := by
  exact
    CriticalPowerFraction.denominator_ge_sum_of_strict_between
      (criticalPower_adjacent_next hj)
      hBetween

/--
奇数 index `j` では、current numerator を 1 だけ下げた power pair

  `(criticalPowerP j - 1, criticalPowerQ j)`

は critical slope の下側にある。

もし上側にあるなら、この pair は
`j + 1` 番目と `j` 番目の consecutive Farey neighbors の間に入る。
しかし denominator は `criticalPowerQ j` のままなので、
Farey adjacency が要求する denominator 下界に反する。
-/
private theorem odd_base_pred_below
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1) :
    3 ^ (criticalPowerP j - 1) <
      2 ^ criticalPowerQ j := by
  have hq : 0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hp : 0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  by_contra hnot
  have hneq :=
    CriticalPowerFraction.twoPow_ne_threePow_of_pos
      (p := criticalPowerP j - 1)
      (q := criticalPowerQ j)
      hq
  have hPredAbove :
      2 ^ criticalPowerQ j <
        3 ^ (criticalPowerP j - 1) := by
    omega
  let x :=
    mkCriticalFraction
      (criticalPowerP j - 1)
      (criticalPowerQ j)
      hq
  have hNextBelow :
      (criticalPowerConvergent (j + 1)).Below := by
    have hEven : (j + 1) % 2 = 0 := by
      omega
    exact
      (criticalPower_orientation (j + 1)).1 hEven
  have hNextX :
      (criticalPowerConvergent (j + 1)).p * x.q <
        x.p * (criticalPowerConvergent (j + 1)).q := by
    exact
      CriticalPowerFraction.cross_lt_of_below_above
        hNextBelow
        hPredAbove
  have hXCurrent :
      x.p * (criticalPowerConvergent j).q <
        (criticalPowerConvergent j).p * x.q := by
    have hp1 :
        criticalPowerP j - 1 <
          criticalPowerP j := by
      omega
    have hmul :
        (criticalPowerP j - 1) * criticalPowerQ j <
          criticalPowerP j * criticalPowerQ j :=
      mul_lt_mul_of_pos_right hp1 hq
    simpa [
      x,
      mkCriticalFraction,
      criticalPowerP,
      criticalPowerQ
    ] using hmul
  have hden :=
    no_small_between_current_next
      hj
      x
      (Or.inr ⟨hNextX, hXCurrent⟩)
  have hden' :
      criticalPowerQ j + criticalPowerQ (j + 1) ≤
        criticalPowerQ j := by
    simpa [x, mkCriticalFraction] using hden
  have hNextQPos :
      0 < criticalPowerQ (j + 1) :=
    criticalPowerQ_pos (j + 1)
  omega

/--
奇数 index `j` の actual convergent では、

  `3^(P_j - 1) < 2^Q_j < 3^P_j`

が成立するため、`Q_j` に対する critical height は
ちょうど `P_j` になる。

左側は `odd_base_pred_below`、
右側は actual convergent の parity orientation から得る。
-/
private theorem odd_base_criticalHeight
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1) :
    criticalHeight (criticalPowerQ j) =
      criticalPowerP j := by
  have hp : 0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  have hPredBelow :
      3 ^ (criticalPowerP j - 1) <
        2 ^ criticalPowerQ j :=
    odd_base_pred_below hj hjOdd
  have hAbove :
      2 ^ criticalPowerQ j <
        3 ^ criticalPowerP j :=
    (criticalPower_orientation j).2 hjOdd
  exact
    criticalHeight_eq_of_pred_below_and_above
      hp
      hPredBelow
      hAbove


/--
奇数 index `j` の actual convergent denominator `Q_j` における
`criticalPrefixHeight` は、その numerator `P_j` に一致する。

`Q_j > 0` なので `criticalPrefixHeight Q_j` は
通常の `criticalHeight Q_j` と一致し、
`odd_base_criticalHeight` の結果をそのまま移せる。
-/
private theorem odd_base_height
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1) :
    criticalPrefixHeight (criticalPowerQ j) =
      criticalPowerP j := by
  have hq : 0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have h :
      criticalHeight (criticalPowerQ j) =
        criticalPowerP j :=
    odd_base_criticalHeight hj hjOdd
  obtain ⟨q, hqEq⟩ :=
    Nat.exists_eq_succ_of_ne_zero hq.ne'
  rw [hqEq] at h ⊢
  change criticalHeight (q + 1) = criticalPowerP j
  exact h

/--
正の index では `criticalPrefixHeight` は通常の
`criticalHeight` に一致する。

`r > 0` なら `r` は successor なので、
`criticalPrefixHeight` の successor branch がそのまま開く。
-/
private theorem criticalPrefixHeight_eq_criticalHeight_of_pos
    {r : ℕ}
    (hr : 0 < r) :
    criticalPrefixHeight r = criticalHeight r := by
  obtain ⟨n, hn⟩ :=
    Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [hn]
  rfl


/--
奇数 index `j` の actual convergent は critical slope の上側にある。

そこへ shift `r` の critical height を加えると、

  2^(Q_j + r) < 3^(P_j + criticalHeight r)

が成り立つ。

これは current convergent の upper inequality と
`criticalHeight r` の expanding inequalityを順に掛け合わせたもの。
-/
private theorem odd_shift_target_above
    {j r : ℕ}
    (hjOdd : j % 2 = 1) :
    2 ^ (criticalPowerQ j + r) <
      3 ^ (criticalPowerP j + criticalHeight r) := by
  have hCurrentAbove :
      2 ^ criticalPowerQ j <
        3 ^ criticalPowerP j :=
    (criticalPower_orientation j).2 hjOdd
  have hShiftAbove :
      2 ^ r <
        3 ^ criticalHeight r :=
    criticalHeight_expanding r
  rw [pow_add, pow_add]
  have h₁ :
      2 ^ criticalPowerQ j * 2 ^ r <
        3 ^ criticalPowerP j * 2 ^ r :=
    mul_lt_mul_of_pos_right
      hCurrentAbove
      (by positivity)
  have h₂ :
      3 ^ criticalPowerP j * 2 ^ r <
        3 ^ criticalPowerP j * 3 ^ criticalHeight r :=
    mul_lt_mul_of_pos_left
      hShiftAbove
      (by positivity)
  exact lt_trans h₁ h₂


/--
奇数 index `j` から、次の convergent denominator に到達する前の
positive shift `r` を取る。

このとき target height の一つ手前

  P_j + criticalHeight r - 1

はまだ critical slope の下側にあり、

  3^(P_j + criticalHeight r - 1)
    < 2^(Q_j + r)

が成り立つ。

反対を仮定すると、この predecessor fraction は
current convergent と next convergent の間に入る。
一方、その denominator は `Q_j + r` であり、
`r < Q_(j+1)` なので Farey adjacency の denominator 下界
`Q_j + Q_(j+1)` に届かず矛盾する。
-/
private theorem odd_shift_target_pred_below
    {j r : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hr : 0 < r)
    (hrUpper : r ≤ criticalPowerQ (j + 1) - 1) :
    3 ^ (criticalPowerP j + criticalHeight r - 1) <
      2 ^ (criticalPowerQ j + r) := by
  let m := criticalHeight r
  have hq :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hNextQ :
      0 < criticalPowerQ (j + 1) :=
    criticalPowerQ_pos (j + 1)
  have hmPos : 0 < m := by
    by_contra hnot
    have hmZero : m = 0 := by
      omega
    have hAbove :
        2 ^ r < 3 ^ criticalHeight r :=
      criticalHeight_expanding r
    rw [show criticalHeight r = m by rfl, hmZero] at hAbove
    simp at hAbove
  have hPredRBelow :
      3 ^ (m - 1) < 2 ^ r := by
    simpa [m] using critical_pred_below hr
  by_contra hnot
  have hnot' :
      ¬ 3 ^ (criticalPowerP j + m - 1) <
          2 ^ (criticalPowerQ j + r) := by
    simpa [m] using hnot
  have hSumQPos :
      0 < criticalPowerQ j + r := by
    omega
  have hneq :=
    CriticalPowerFraction.twoPow_ne_threePow_of_pos
      (p := criticalPowerP j + m - 1)
      (q := criticalPowerQ j + r)
      hSumQPos
  have hPredAbove :
      2 ^ (criticalPowerQ j + r) <
        3 ^ (criticalPowerP j + m - 1) := by
    omega
  let x :=
    mkCriticalFraction
      (criticalPowerP j + m - 1)
      (criticalPowerQ j + r)
      hSumQPos
  have hNextBelow :
      (criticalPowerConvergent (j + 1)).Below := by
    have hEven : (j + 1) % 2 = 0 := by
      omega
    exact
      (criticalPower_orientation (j + 1)).1 hEven
  have hNextX :
      (criticalPowerConvergent (j + 1)).p * x.q <
        x.p * (criticalPowerConvergent (j + 1)).q := by
    exact
      CriticalPowerFraction.cross_lt_of_below_above
        hNextBelow
        hPredAbove
  have hPredFracBelow :
      (mkCriticalFraction (m - 1) r hr).Below := by
    exact hPredRBelow
  have hCurrentFracAbove :
      (criticalPowerConvergent j).Above :=
    (criticalPower_orientation j).2 hjOdd
  have hCrossSmall :=
    CriticalPowerFraction.cross_lt_of_below_above
      hPredFracBelow
      hCurrentFracAbove
  have hCrossSmall' :
      (m - 1) * criticalPowerQ j <
        criticalPowerP j * r := by
    simpa [
      mkCriticalFraction,
      criticalPowerP,
      criticalPowerQ
    ] using hCrossSmall
  have hXCurrent :
      x.p * (criticalPowerConvergent j).q <
        (criticalPowerConvergent j).p * x.q := by
    dsimp [x, mkCriticalFraction]
    change
      (criticalPowerP j + m - 1) * criticalPowerQ j <
        criticalPowerP j * (criticalPowerQ j + r)
    have hPredAdd :
        criticalPowerP j + m - 1 =
          criticalPowerP j + (m - 1) := by
      omega
    rw [hPredAdd, Nat.add_mul, Nat.mul_add]
    exact
      Nat.add_lt_add_left
        hCrossSmall'
        (criticalPowerP j * criticalPowerQ j)
  have hden :=
    no_small_between_current_next
      hj
      x
      (Or.inr ⟨hNextX, hXCurrent⟩)
  have hden' :
      criticalPowerQ j + criticalPowerQ (j + 1) ≤
        criticalPowerQ j + r := by
    simpa [x, mkCriticalFraction] using hden
  have hrLt :
      r < criticalPowerQ (j + 1) := by
    omega
  omega


/--
奇数 index `j` の actual convergent から、
次の convergent denominator に達する前の positive shift `r` では、

  criticalPrefixHeight (Q_j + r)
    = P_j + criticalPrefixHeight r

が成り立つ。

`odd_shift_target_pred_below` と `odd_shift_target_above` により
target exponent の直前は below、target 自身は above なので、
critical height はちょうど `P_j + criticalHeight r` に確定する。
最後に positive index 上で `criticalPrefixHeight` に戻す。
-/
private theorem odd_height_shift_pos
    {j r : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hr : 0 < r)
    (hrUpper : r ≤ criticalPowerQ (j + 1) - 1) :
    criticalPrefixHeight (criticalPowerQ j + r) =
      criticalPowerP j + criticalPrefixHeight r := by
  have hPredBelow :
      3 ^ (criticalPowerP j + criticalHeight r - 1) <
        2 ^ (criticalPowerQ j + r) :=
    odd_shift_target_pred_below
      hj hjOdd hr hrUpper
  have hAbove :
      2 ^ (criticalPowerQ j + r) <
        3 ^ (criticalPowerP j + criticalHeight r) :=
    odd_shift_target_above hjOdd
  have hp :
      0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  have hHeight :
      criticalHeight (criticalPowerQ j + r) =
        criticalPowerP j + criticalHeight r := by
    exact
      criticalHeight_eq_of_pred_below_and_above
        (by omega)
        hPredBelow
        hAbove
  have hTargetPrefix :
      criticalPrefixHeight (criticalPowerQ j + r) =
        criticalHeight (criticalPowerQ j + r) := by
    apply criticalPrefixHeight_eq_criticalHeight_of_pos
    have hq :
        0 < criticalPowerQ j :=
      criticalPowerQ_pos j
    omega
  have hShiftPrefix :
      criticalPrefixHeight r =
        criticalHeight r :=
    criticalPrefixHeight_eq_criticalHeight_of_pos hr
  rw [hTargetPrefix, hShiftPrefix]
  exact hHeight

/--
even index `j` の current convergent は critical slope の下側にある。

shift `r` の critical height の一つ手前も下側なので、
二つの不等式を掛け合わせることにより、

  3^(P_j + criticalHeight r - 1)
    < 2^(Q_j + r)

を得る。

even 側では target predecessor の below 性は
Farey geometry を使わず、純粋な積の不等式から従う。
-/
private theorem even_shift_target_pred_below
    {j r : ℕ}
    (hjEven : j % 2 = 0)
    (hr : 0 < r) :
    3 ^ (criticalPowerP j + criticalHeight r - 1) <
      2 ^ (criticalPowerQ j + r) := by
  have hmPos : 0 < criticalHeight r := by
    by_contra hnot
    have hmZero : criticalHeight r = 0 := by
      omega
    have hAbove := criticalHeight_expanding r
    rw [hmZero] at hAbove
    simp at hAbove
  have hCurrentBelow :
      3 ^ criticalPowerP j <
        2 ^ criticalPowerQ j :=
    (criticalPower_orientation j).1 hjEven
  have hPredRBelow :
      3 ^ (criticalHeight r - 1) <
        2 ^ r :=
    critical_pred_below hr
  have hExpEq :
      criticalPowerP j + criticalHeight r - 1 =
        criticalPowerP j + (criticalHeight r - 1) := by
    omega
  rw [hExpEq, pow_add, pow_add]
  have h₁ :
      3 ^ criticalPowerP j *
          3 ^ (criticalHeight r - 1) <
        2 ^ criticalPowerQ j *
          3 ^ (criticalHeight r - 1) :=
    mul_lt_mul_of_pos_right
      hCurrentBelow
      (by positivity)
  have h₂ :
      2 ^ criticalPowerQ j *
          3 ^ (criticalHeight r - 1) <
        2 ^ criticalPowerQ j * 2 ^ r :=
    mul_lt_mul_of_pos_left
      hPredRBelow
      (by positivity)
  exact lt_trans h₁ h₂


/--
even index `j` の current convergent に、
shift `r` の critical-height vector を加えた target は、
current convergent より slope の大きい側に移る。

これは

  current : below
  shift   : above

という二つの vector の cross inequality を加法的に移したもの。

後続の Farey 排除で、
target が current と next の間にあることを示すために使う。
-/
private theorem even_shift_current_lt_target_cross
    {j r : ℕ}
    (hjEven : j % 2 = 0)
    (hr : 0 < r) :
    (criticalPowerConvergent j).p *
        (criticalPowerQ j + r) <
      (criticalPowerP j + criticalHeight r) *
        (criticalPowerConvergent j).q := by
  have hCurrentBelow :
      (criticalPowerConvergent j).Below :=
    (criticalPower_orientation j).1 hjEven
  have hShiftAbove :
      (mkCriticalFraction
        (criticalHeight r)
        r
        hr).Above := by
    exact criticalHeight_expanding r
  have hCross :=
    CriticalPowerFraction.cross_lt_of_below_above
      hCurrentBelow
      hShiftAbove
  have hCross' :
      criticalPowerP j * r <
        criticalHeight r * criticalPowerQ j := by
    simpa [
      mkCriticalFraction,
      criticalPowerP,
      criticalPowerQ
    ] using hCross
  change
    criticalPowerP j * (criticalPowerQ j + r) <
      (criticalPowerP j + criticalHeight r) *
        criticalPowerQ j
  rw [Nat.mul_add, Nat.add_mul]
  exact
    Nat.add_lt_add_left
      hCross'
      (criticalPowerP j * criticalPowerQ j)


/--
even index `j` から next convergent に達する前の positive shift `r`
を取ると、shift 後の target 自身は critical slope の上側にある。

もし target まで下側に残るなら、

  current < target < next

という strict Farey interval ができる。

しかし target denominator は `Q_j + r` であり、
`r < Q_(j+1)` なので、consecutive Farey neighbors の間に入るために
必要な denominator `Q_j + Q_(j+1)` より小さい。
これは denominator lower bound に反する。
-/
private theorem even_shift_target_above_actual
    {j r : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hr : 0 < r)
    (hrUpper : r ≤ criticalPowerQ (j + 1) - 1) :
    2 ^ (criticalPowerQ j + r) <
      3 ^ (criticalPowerP j + criticalHeight r) := by
  have hq :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hNextQ :
      0 < criticalPowerQ (j + 1) :=
    criticalPowerQ_pos (j + 1)
  have hSumQPos :
      0 < criticalPowerQ j + r := by
    omega
  by_contra hnot
  have hneq :=
    CriticalPowerFraction.twoPow_ne_threePow_of_pos
      (p := criticalPowerP j + criticalHeight r)
      (q := criticalPowerQ j + r)
      hSumQPos
  have hTargetBelow :
      3 ^ (criticalPowerP j + criticalHeight r) <
        2 ^ (criticalPowerQ j + r) := by
    omega
  let x :=
    mkCriticalFraction
      (criticalPowerP j + criticalHeight r)
      (criticalPowerQ j + r)
      hSumQPos
  have hCurrentX :
      (criticalPowerConvergent j).p * x.q <
        x.p * (criticalPowerConvergent j).q := by
    have hCross :=
      even_shift_current_lt_target_cross
        hjEven
        hr
    simpa [x, mkCriticalFraction] using hCross
  have hNextAbove :
      (criticalPowerConvergent (j + 1)).Above := by
    have hOdd :
        (j + 1) % 2 = 1 := by
      omega
    exact
      (criticalPower_orientation (j + 1)).2 hOdd
  have hXNext :
      x.p * (criticalPowerConvergent (j + 1)).q <
        (criticalPowerConvergent (j + 1)).p * x.q := by
    exact
      CriticalPowerFraction.cross_lt_of_below_above
        hTargetBelow
        hNextAbove
  have hden :=
    no_small_between_current_next
      hj
      x
      (Or.inl ⟨hCurrentX, hXNext⟩)
  have hden' :
      criticalPowerQ j + criticalPowerQ (j + 1) ≤
        criticalPowerQ j + r := by
    simpa [x, mkCriticalFraction] using hden
  have hrLt :
      r < criticalPowerQ (j + 1) := by
    omega
  omega


/--
even index `j` から next convergent の直前まで shift したとき、
target の exact critical height は

  P_j + criticalHeight r

になる。

一つ手前の exponent は `even_shift_target_pred_below` により below、
target 自身は `even_shift_target_above_actual` により above なので、
critical height の定義境界がこの exponent に一意に固定される。
-/
private theorem even_shift_criticalHeight_actual
    {j r : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hr : 0 < r)
    (hrUpper : r ≤ criticalPowerQ (j + 1) - 1) :
    criticalHeight (criticalPowerQ j + r) =
      criticalPowerP j + criticalHeight r := by
  have hp :
      0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  have hPredBelow :
      3 ^ (criticalPowerP j + criticalHeight r - 1) <
        2 ^ (criticalPowerQ j + r) :=
    even_shift_target_pred_below
      hjEven
      hr
  have hAbove :
      2 ^ (criticalPowerQ j + r) <
        3 ^ (criticalPowerP j + criticalHeight r) :=
    even_shift_target_above_actual
      hj
      hjEven
      hr
      hrUpper
  exact
    criticalHeight_eq_of_pred_below_and_above
      (by omega)
      hPredBelow
      hAbove


/--
even index `j` から next convergent の直前までの positive shift では、

  criticalPrefixHeight (Q_j + r)
    = P_j + criticalPrefixHeight r

が成り立つ。

本体は `even_shift_criticalHeight_actual` であり、
ここでは positive index 上で `criticalHeight` と
`criticalPrefixHeight` を相互に移すだけである。
-/
private theorem even_height_shift_pos_actual
    {j r : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hr : 0 < r)
    (hrUpper : r ≤ criticalPowerQ (j + 1) - 1) :
    criticalPrefixHeight (criticalPowerQ j + r) =
      criticalPowerP j + criticalPrefixHeight r := by
  have hq :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hTargetPrefix :
      criticalPrefixHeight (criticalPowerQ j + r) =
        criticalHeight (criticalPowerQ j + r) :=
    criticalPrefixHeight_eq_criticalHeight_of_pos
      (by omega)
  have hShiftPrefix :
      criticalPrefixHeight r =
        criticalHeight r :=
    criticalPrefixHeight_eq_criticalHeight_of_pos hr
  rw [hTargetPrefix, hShiftPrefix]
  exact
    even_shift_criticalHeight_actual
      hj
      hjEven
      hr
      hrUpper

/--
even index `j` では actual convergent の numerator は
denominator より真に小さい。

`P_j ≤ Q_j` は既存の bound から得られる。
もし `P_j = Q_j` なら even orientation から

  3^Q_j < 2^Q_j

を得るが、`Q_j > 0` なので逆に

  2^Q_j < 3^Q_j

でもあり矛盾する。
-/
private theorem even_base_p_lt_q_actual
    {j : ℕ}
    (hjEven : j % 2 = 0) :
    criticalPowerP j < criticalPowerQ j := by
  have hq :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hle :
      criticalPowerP j ≤ criticalPowerQ j :=
    criticalPowerP_le_Q j
  by_contra hnot
  have heq :
      criticalPowerP j = criticalPowerQ j := by
    omega
  have hBelowP :
      3 ^ criticalPowerP j <
        2 ^ criticalPowerQ j := by
    have h :=
      (criticalPower_orientation j).1 hjEven
    unfold CriticalPowerFraction.Below at h
    change
      3 ^ criticalPowerP j <
        2 ^ criticalPowerQ j at h
    exact h
  have hBelow :
      3 ^ criticalPowerQ j <
        2 ^ criticalPowerQ j := by
    rw [heq] at hBelowP
    exact hBelowP
  have hPow :
      2 ^ criticalPowerQ j <
        3 ^ criticalPowerQ j := by
    exact
      Nat.pow_lt_pow_left
        (by omega : (2 : ℕ) < 3)
        (Nat.ne_of_gt hq)
  omega


/--
even index `j` の denominator `Q_j` では、
current numerator を一つ増やした exponent `P_j + 1` は
すでに critical slope の上側にある。

もしまだ下側なら、

  current < (P_j + 1)/Q_j < next

という strict Farey interval ができる。
しかし middle fraction の denominator は current と同じ `Q_j`
なので、consecutive neighbors の間に必要な denominator 下界に反する。
-/
private theorem even_base_plus_one_above_actual
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    2 ^ criticalPowerQ j <
      3 ^ (criticalPowerP j + 1) := by
  have hq :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  by_contra hnot
  have hneq :=
    CriticalPowerFraction.twoPow_ne_threePow_of_pos
      (p := criticalPowerP j + 1)
      (q := criticalPowerQ j)
      hq
  have hP1Below :
      3 ^ (criticalPowerP j + 1) <
        2 ^ criticalPowerQ j := by
    omega
  let x :=
    mkCriticalFraction
      (criticalPowerP j + 1)
      (criticalPowerQ j)
      hq
  have hCurX :
      (criticalPowerConvergent j).p * x.q <
        x.p * (criticalPowerConvergent j).q := by
    have hpStep :
        criticalPowerP j <
          criticalPowerP j + 1 := by
      omega
    have hmul :
        criticalPowerP j * criticalPowerQ j <
          (criticalPowerP j + 1) * criticalPowerQ j :=
      mul_lt_mul_of_pos_right hpStep hq
    simpa [
      x,
      mkCriticalFraction,
      criticalPowerP,
      criticalPowerQ
    ] using hmul
  have hNextAbove :
      (criticalPowerConvergent (j + 1)).Above := by
    have hOdd :
        (j + 1) % 2 = 1 := by
      omega
    exact
      (criticalPower_orientation (j + 1)).2 hOdd
  have hXNext :
      x.p * (criticalPowerConvergent (j + 1)).q <
        (criticalPowerConvergent (j + 1)).p * x.q :=
    CriticalPowerFraction.cross_lt_of_below_above
      hP1Below
      hNextAbove
  have hden :=
    no_small_between_current_next
      hj
      x
      (Or.inl ⟨hCurX, hXNext⟩)
  have hden' :
      criticalPowerQ j + criticalPowerQ (j + 1) ≤
        criticalPowerQ j := by
    simpa [x, mkCriticalFraction] using hden
  have hNextQPos :
      0 < criticalPowerQ (j + 1) :=
    criticalPowerQ_pos (j + 1)
  omega


/--
even index `j` の current denominator `Q_j` における
exact critical height は `P_j + 1` である。

`P_j` 自身は even orientation により below、
`P_j + 1` は `even_base_plus_one_above_actual` により above なので、
critical threshold はちょうどその間にある。
-/
private theorem even_base_criticalHeight_actual
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    criticalHeight (criticalPowerQ j) =
      criticalPowerP j + 1 := by
  have hCurrentBelow :
      3 ^ criticalPowerP j <
        2 ^ criticalPowerQ j :=
    (criticalPower_orientation j).1 hjEven
  have hP1Above :
      2 ^ criticalPowerQ j <
        3 ^ (criticalPowerP j + 1) :=
    even_base_plus_one_above_actual
      hj
      hjEven
  exact
    criticalHeight_eq_of_pred_below_and_above
      (by omega)
      (by simpa using hCurrentBelow)
      hP1Above


/--
even index `j` では denominator を一つ進めても、
exponent `P_j + 1` は critical slope の上側にある。

もし

  (P_j + 1, Q_j + 1)

がまだ下側なら、この fraction は current と next の間に入る。

その denominator は `Q_j + 1` だが、
actual consecutive convergent では `Q_(j+1) > 1` なので、
Farey adjacency が要求する

  Q_j + Q_(j+1)

には届かず矛盾する。
-/
private theorem even_succ_plus_one_above_actual
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    2 ^ (criticalPowerQ j + 1) <
      3 ^ (criticalPowerP j + 1) := by
  have hq :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hpq :
      criticalPowerP j <
        criticalPowerQ j :=
    even_base_p_lt_q_actual hjEven
  have hSumQPos :
      0 < criticalPowerQ j + 1 := by
    omega
  by_contra hnot
  have hneq :=
    CriticalPowerFraction.twoPow_ne_threePow_of_pos
      (p := criticalPowerP j + 1)
      (q := criticalPowerQ j + 1)
      hSumQPos
  have hP1Below :
      3 ^ (criticalPowerP j + 1) <
        2 ^ (criticalPowerQ j + 1) := by
    omega
  let x :=
    mkCriticalFraction
      (criticalPowerP j + 1)
      (criticalPowerQ j + 1)
      hSumQPos
  have hCurX :
      (criticalPowerConvergent j).p * x.q <
        x.p * (criticalPowerConvergent j).q := by
    dsimp [x, mkCriticalFraction]
    change
      criticalPowerP j * (criticalPowerQ j + 1) <
        (criticalPowerP j + 1) * criticalPowerQ j
    rw [Nat.mul_add, Nat.add_mul]
    omega
  have hNextAbove :
      (criticalPowerConvergent (j + 1)).Above := by
    have hOdd :
        (j + 1) % 2 = 1 := by
      omega
    exact
      (criticalPower_orientation (j + 1)).2 hOdd
  have hXNext :
      x.p * (criticalPowerConvergent (j + 1)).q <
        (criticalPowerConvergent (j + 1)).p * x.q :=
    CriticalPowerFraction.cross_lt_of_below_above
      hP1Below
      hNextAbove
  have hden :=
    no_small_between_current_next
      hj
      x
      (Or.inl ⟨hCurX, hXNext⟩)
  have hden' :
      criticalPowerQ j + criticalPowerQ (j + 1) ≤
        criticalPowerQ j + 1 := by
    simpa [x, mkCriticalFraction] using hden
  have hNextQgt :
      1 < criticalPowerQ (j + 1) := by
    have hs :
        criticalPowerQ j <
          criticalPowerQ (j + 1) :=
      criticalPowerQ_lt_next hj
    omega
  omega


/--
even index `j` では、`Q_j + 1` における
exact critical height も `P_j + 1` のままである。

lower side は current even inequality
`3^P_j < 2^Q_j` から denominator を一つ増やして得る。
upper side は `even_succ_plus_one_above_actual` が与える。
-/
private theorem even_succ_criticalHeight_actual
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    criticalHeight (criticalPowerQ j + 1) =
      criticalPowerP j + 1 := by
  have hCurrentBelow :
      3 ^ criticalPowerP j <
        2 ^ criticalPowerQ j :=
    (criticalPower_orientation j).1 hjEven
  have hTwoStep :
      2 ^ criticalPowerQ j <
        2 ^ (criticalPowerQ j + 1) := by
    rw [pow_succ]
    have hpos :
        0 < 2 ^ criticalPowerQ j := by
      positivity
    omega
  have hBelowSucc :
      3 ^ criticalPowerP j <
        2 ^ (criticalPowerQ j + 1) :=
    lt_trans hCurrentBelow hTwoStep
  have hP1AboveSucc :
      2 ^ (criticalPowerQ j + 1) <
        3 ^ (criticalPowerP j + 1) :=
    even_succ_plus_one_above_actual
      hj
      hjEven
  exact
    criticalHeight_eq_of_pred_below_and_above
      (by omega)
      (by simpa using hBelowSucc)
      hP1AboveSucc


/--
even convergent の最初の Sturmian bit は flat である。

実際、

  criticalHeight Q_j       = P_j + 1
  criticalHeight (Q_j + 1) = P_j + 1

なので、`Q_j` から `Q_j + 1` へ進んでも
prefix height は増加しない。
したがって corresponding critical Sturmian bit は `false` になる。
-/
theorem even_first_flat_actual
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    criticalSturmianBit (criticalPowerQ j) = false := by
  have hq :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hHq :
      criticalHeight (criticalPowerQ j) =
        criticalPowerP j + 1 :=
    even_base_criticalHeight_actual
      hj
      hjEven
  have hHsucc :
      criticalHeight (criticalPowerQ j + 1) =
        criticalPowerP j + 1 :=
    even_succ_criticalHeight_actual
      hj
      hjEven
  have hqPrefix :
      criticalPrefixHeight (criticalPowerQ j) =
        criticalHeight (criticalPowerQ j) :=
    criticalPrefixHeight_eq_criticalHeight_of_pos hq
  apply
    (criticalSturmianBit_eq_false_iff
      (criticalPowerQ j)).2
  simp only [criticalPrefixHeight_succ]
  rw [hqPrefix, hHq, hHsucc]
  simp only [ne_eq, Nat.left_eq_add, one_ne_zero, not_false_eq_true]


/-- actual power-Farey data gives the entire strong Beatty corridor。 -/
theorem actualCriticalBeattyConvergentCorridor :
    CriticalBeattyConvergentCorridor actualCriticalContinuedFractionData := by
  refine {
    odd_height_shift := ?_
    even_first_flat := ?_
    even_height_shift_pos := ?_
  }
  · intro j r hj hjOdd hr
    change criticalPrefixHeight (criticalPowerQ j + r) =
      criticalPowerP j + criticalPrefixHeight r
    cases r with
    | zero =>
        simpa using odd_base_height hj hjOdd
    | succ r =>
        exact odd_height_shift_pos hj hjOdd (by omega) hr
  · intro j hj hjEven
    change criticalSturmianBit (criticalPowerQ j) = false
    exact even_first_flat_actual hj hjEven
  · intro j r hj hjEven hrPos hr
    change criticalPrefixHeight (criticalPowerQ j + r) =
      criticalPowerP j + criticalPrefixHeight r
    exact even_height_shift_pos_actual hj hjEven hrPos hr

/--
Christoffel index `i < P_j` に対する floor quotient

  floor(i Q_j / P_j)

は `Q_j` より真に小さい。

`i < P_j` を正の `Q_j` 倍し、
division の基本不等式と組み合わせて示す。
-/
private theorem actualChristoffelQuotient_lt_Q
    {j i : ℕ}
    (hi : i < criticalPowerP j) :
    (i * criticalPowerQ j) / criticalPowerP j <
      criticalPowerQ j := by
  let k :=
    (i * criticalPowerQ j) / criticalPowerP j
  have hpPos :
      0 < criticalPowerP j :=
    lt_of_le_of_lt (Nat.zero_le i) hi
  have hqPos :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hkMul :
      k * criticalPowerP j ≤
        i * criticalPowerQ j := by
    dsimp [k]
    exact Nat.div_mul_le_self _ _
  have hiMul :
      i * criticalPowerQ j <
        criticalPowerP j * criticalPowerQ j :=
    (Nat.mul_lt_mul_right hqPos).2 hi
  have hkMulLt :
      k * criticalPowerP j <
        criticalPowerQ j * criticalPowerP j := by
    calc
      k * criticalPowerP j
          ≤ i * criticalPowerQ j := hkMul
      _ < criticalPowerP j * criticalPowerQ j := hiMul
      _ = criticalPowerQ j * criticalPowerP j := by
        rw [Nat.mul_comm]
  have hkLt :
      k < criticalPowerQ j :=
    (Nat.mul_lt_mul_right hpPos).1 hkMulLt
  simpa [k] using hkLt

/--
Christoffel summand の残差 pair は current convergent より
strict に小さい cross-product を持つ。
-/
private theorem actualChristoffelResidualCross
    {j i : ℕ}
    (hi : i < criticalPowerP j) :
    (criticalPowerP j - 1 - i) * criticalPowerQ j <
      criticalPowerP j *
        (criticalPowerQ j -
          (i * criticalPowerQ j) / criticalPowerP j) := by
  let k :=
    (i * criticalPowerQ j) / criticalPowerP j
  have hqPos :
      0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hkMul :
      k * criticalPowerP j ≤
        i * criticalPowerQ j := by
    dsimp [k]
    exact Nat.div_mul_le_self _ _
  have hiQlt :
      i * criticalPowerQ j <
        (i + 1) * criticalPowerQ j :=
    (Nat.mul_lt_mul_right hqPos).2
      (Nat.lt_succ_self i)
  have hCross :
      k * criticalPowerP j <
        (i + 1) * criticalPowerQ j :=
    lt_of_le_of_lt hkMul hiQlt
  have hkLt :
      k < criticalPowerQ j := by
    simpa [k] using
      actualChristoffelQuotient_lt_Q
        (j := j) (i := i) hi
  have hkLe :
      k ≤ criticalPowerQ j :=
    Nat.le_of_lt hkLt
  have hPDecomp :
      criticalPowerP j - 1 - i + (i + 1) =
        criticalPowerP j := by
    omega
  have hSumLt :
      (criticalPowerP j - 1 - i) * criticalPowerQ j +
          k * criticalPowerP j <
        criticalPowerP j * criticalPowerQ j := by
    calc
      (criticalPowerP j - 1 - i) * criticalPowerQ j +
            k * criticalPowerP j
          <
        (criticalPowerP j - 1 - i) * criticalPowerQ j +
            (i + 1) * criticalPowerQ j :=
        Nat.add_lt_add_left hCross _
      _ =
        (criticalPowerP j - 1 - i + (i + 1)) *
          criticalPowerQ j := by
        simp [Nat.add_mul]
      _ =
        criticalPowerP j * criticalPowerQ j := by
        rw [hPDecomp]
  have hQDecomp :
      criticalPowerQ j - k + k =
        criticalPowerQ j :=
    Nat.sub_add_cancel hkLe
  have hProdDecomp :
      criticalPowerP j * (criticalPowerQ j - k) +
          k * criticalPowerP j =
        criticalPowerP j * criticalPowerQ j := by
    calc
      criticalPowerP j * (criticalPowerQ j - k) +
            k * criticalPowerP j
          =
        criticalPowerP j * (criticalPowerQ j - k) +
            criticalPowerP j * k := by
        rw [Nat.mul_comm k (criticalPowerP j)]
      _ =
        criticalPowerP j *
          (criticalPowerQ j - k + k) := by
        rw [Nat.mul_add]
      _ =
        criticalPowerP j * criticalPowerQ j := by
        rw [hQDecomp]
  change
    (criticalPowerP j - 1 - i) * criticalPowerQ j <
      criticalPowerP j * (criticalPowerQ j - k)
  omega

/--
floor quotient が `Q_j` より小さいので、
残差 denominator は正である。
-/
private theorem actualChristoffelResidualDenominatorPos
    {j i : ℕ}
    (hi : i < criticalPowerP j) :
    0 <
      criticalPowerQ j -
        (i * criticalPowerQ j) / criticalPowerP j := by
  exact
    Nat.sub_pos_of_lt
      (actualChristoffelQuotient_lt_Q
        (j := j) (i := i) hi)


/--
`j ≥ 9` では Christoffel summand の残差 pair は
critical slope の下側にある。

even current では current より小さいことから直ちに below。
odd current では、もし residual も above なら
next と current の strict Farey interval に入り、
denominator lower bound に反する。
-/
private theorem actualChristoffelResidualBelow
    {j i : ℕ}
    (hj : 9 ≤ j)
    (hi : i < criticalPowerP j) :
    3 ^ (criticalPowerP j - 1 - i) <
      2 ^
        (criticalPowerQ j -
          (i * criticalPowerQ j) / criticalPowerP j) := by
  let k :=
    (i * criticalPowerQ j) / criticalPowerP j
  have hAcurrent :
      (criticalPowerP j - 1 - i) * criticalPowerQ j <
        criticalPowerP j * (criticalPowerQ j - k) := by
    simpa [k] using
      actualChristoffelResidualCross
        (j := j) (i := i) hi
  have hAqPos :
      0 < criticalPowerQ j - k := by
    simpa [k] using
      actualChristoffelResidualDenominatorPos
        (j := j) (i := i) hi
  let x :=
    mkCriticalFraction
      (criticalPowerP j - 1 - i)
      (criticalPowerQ j - k)
      hAqPos
  have hCurrentCompare :
      x.p * (criticalPowerConvergent j).q <
        (criticalPowerConvergent j).p * x.q := by
    simpa [
      x,
      mkCriticalFraction,
      criticalPowerP,
      criticalPowerQ
    ] using hAcurrent
  rcases criticalPower_opposite_next (j := j) with
    hEven | hOdd
  · have hxBelow : x.Below :=
      CriticalPowerFraction.below_of_fraction_le_below
        (Nat.le_of_lt hCurrentCompare)
        hEven.2.1
    unfold CriticalPowerFraction.Below at hxBelow
    simpa [x, mkCriticalFraction, k] using hxBelow
  · rcases
        CriticalPowerFraction.below_or_above_of_pos x with
      hxBelow | hxAbove
    · unfold CriticalPowerFraction.Below at hxBelow
      simpa [x, mkCriticalFraction, k] using hxBelow
    · have hNextX :
          (criticalPowerConvergent (j + 1)).p * x.q <
            x.p * (criticalPowerConvergent (j + 1)).q :=
        CriticalPowerFraction.cross_lt_of_below_above
          hOdd.2.2
          hxAbove
      have hden :=
        no_small_between_current_next
          hj
          x
          (Or.inr ⟨hNextX, hCurrentCompare⟩)
      have hden' :
          criticalPowerQ j + criticalPowerQ (j + 1) ≤
            criticalPowerQ j - k := by
        simpa [x, mkCriticalFraction] using hden
      have hxqLe :
          criticalPowerQ j - k ≤ criticalPowerQ j :=
        Nat.sub_le _ _
      have hNextQPos :
          0 < criticalPowerQ (j + 1) :=
        criticalPowerQ_pos (j + 1)
      omega


/--
`j ≥ 9` では residual-Below inequality に `2^k` を掛け戻し、
Christoffel summand 全体を `2^Q_j` で抑える。
-/
private theorem actualChristoffelTermLeTwoPowOfNineLe
    {j i : ℕ}
    (hj : 9 ≤ j)
    (hi : i < criticalPowerP j) :
    (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
        (2 : ℤ) ^
          ((i * criticalPowerQ j) / criticalPowerP j) ≤
      (2 : ℤ) ^ criticalPowerQ j := by
  let k :=
    (i * criticalPowerQ j) / criticalPowerP j
  have hNat :
      3 ^ (criticalPowerP j - 1 - i) <
        2 ^ (criticalPowerQ j - k) := by
    simpa [k] using
      actualChristoffelResidualBelow
        (j := j) (i := i) hj hi
  have hcast :
      (3 : ℤ) ^ (criticalPowerP j - 1 - i) <
        (2 : ℤ) ^ (criticalPowerQ j - k) := by
    exact_mod_cast hNat
  have hkLt :
      k < criticalPowerQ j := by
    simpa [k] using
      actualChristoffelQuotient_lt_Q
        (j := j) (i := i) hi
  have hkLe :
      k ≤ criticalPowerQ j :=
    Nat.le_of_lt hkLt
  have htwo :
      (2 : ℤ) ^ k *
          (2 : ℤ) ^ (criticalPowerQ j - k) =
        (2 : ℤ) ^ criticalPowerQ j := by
    rw [← pow_add]
    congr 1
    omega
  have hmul :
      (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
          (2 : ℤ) ^ k <
        (2 : ℤ) ^ (criticalPowerQ j - k) *
          (2 : ℤ) ^ k :=
    mul_lt_mul_of_pos_right
      hcast
      (by positivity)
  have hmul' :
      (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
          (2 : ℤ) ^ k <
        (2 : ℤ) ^ criticalPowerQ j := by
    calc
      (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
            (2 : ℤ) ^ k
          <
        (2 : ℤ) ^ (criticalPowerQ j - k) *
            (2 : ℤ) ^ k := hmul
      _ =
        (2 : ℤ) ^ k *
          (2 : ℤ) ^ (criticalPowerQ j - k) := by
        rw [mul_comm]
      _ =
        (2 : ℤ) ^ criticalPowerQ j := htwo
  simpa [k] using le_of_lt hmul'


/--
最初の 9 convergents に対する Christoffel summand bound は
有限型上の完全計算で確認する。
-/
private theorem actualChristoffelInitialFiniteCheck :
    ∀ j : Fin 9,
      ∀ i : Fin (criticalPowerP j.1),
        (3 : ℤ) ^ (criticalPowerP j.1 - 1 - i.1) *
            (2 : ℤ) ^
              ((i.1 * criticalPowerQ j.1) /
                criticalPowerP j.1) ≤
          (2 : ℤ) ^ criticalPowerQ j.1 := by
  native_decide


/--
`j < 9` の初期部分は、
有限型上の verified computation から取り出す。
-/
private theorem actualChristoffelTermLeTwoPowBeforeNine
    {j i : ℕ}
    (hj : j < 9)
    (hi : i < criticalPowerP j) :
    (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
        (2 : ℤ) ^
          ((i * criticalPowerQ j) / criticalPowerP j) ≤
      (2 : ℤ) ^ criticalPowerQ j := by
  let jf : Fin 9 :=
    ⟨j, hj⟩
  let ifin : Fin (criticalPowerP jf.1) :=
    ⟨i, by simpa [jf] using hi⟩
  simpa [jf, ifin] using
    actualChristoffelInitialFiniteCheck jf ifin


/--
actual power-Farey family のすべての index `j` について、
各 Christoffel summand は `2^Q_j` 以下である。

`j ≥ 9` は Farey geometry、
`j < 9` は有限計算で処理する。
-/
private theorem actualChristoffelTermLeTwoPow
    {j i : ℕ}
    (hi : i < criticalPowerP j) :
    (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
        (2 : ℤ) ^
          ((i * criticalPowerQ j) / criticalPowerP j) ≤
      (2 : ℤ) ^ criticalPowerQ j := by
  by_cases hj : 9 ≤ j
  · exact
      actualChristoffelTermLeTwoPowOfNineLe
        hj
        hi
  · have hjlt :
        j < 9 := by
      omega
    exact
      actualChristoffelTermLeTwoPowBeforeNine
        hjlt
        hi


/--
actual power-Farey data は
`CriticalChristoffelHeightGeometry` が要求する二つの条件を満たす。

* `P_j ≤ Q_j`
* 各 explicit Christoffel summand が `2^Q_j` 以下

前者は既存の actual convergent bound、
後者は `actualChristoffelTermLeTwoPow` による。
-/
theorem actualCriticalChristoffelHeightGeometry :
    CriticalChristoffelHeightGeometry
      actualOrientedCriticalContinuedFractionData := by
  refine {
    p_le_q := criticalPowerP_le_Q
    term_le_twoPow := ?_
  }
  intro j i hi
  change
    (3 : ℤ) ^ (criticalPowerP j - 1 - i) *
        (2 : ℤ) ^
          ((i * criticalPowerQ j) / criticalPowerP j) ≤
      (2 : ℤ) ^ criticalPowerQ j
  exact
    actualChristoffelTermLeTwoPow hi
end ExternalArithmetic
end CSTMicro
end Collatz2
