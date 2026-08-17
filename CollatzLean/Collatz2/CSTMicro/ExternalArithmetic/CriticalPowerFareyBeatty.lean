import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerFareyGeometry
import CollatzLean.Collatz2.CSTMicro.BeattyPositions

/-!
# Farey convergents -> exact finite Beatty positions

start=9 以降の convergent `(p_j,q_j)` について

  beattyIndex i = floor(i q_j / p_j),  0 <= i < p_j

を Farey no-small-denominator lemma だけから証明する。
これが explicit Christoffel `phi_j` と critical Xi finite sum を同じ座標へ置く橋になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open CriticalPowerFraction

private def mkCriticalFraction
    (p q : ℕ)
    (hq : 0 < q) : CriticalPowerFraction :=
  ⟨p, q, hq⟩

private theorem no_scaled_current_equality
    {j i k : ℕ}
    (hj : 9 ≤ j)
    (hiPos : 0 < i)
    (hkPos : 0 < k)
    (hkLt : k < criticalPowerQ j)
    (hEq : k * criticalPowerP j = i * criticalPowerQ j) :
    False := by
  let prev := criticalPowerConvergent (j - 1)
  let cur := criticalPowerConvergent j
  have hadj : FareyAdjacent prev cur := by
    have hp : 8 ≤ j - 1 := by omega
    have h := criticalPower_adjacent_next_from_eight (j := j - 1) hp
    simpa [prev, cur, show (j - 1) + 1 = j by omega] using h
  have hqPos : (0 : ℤ) < criticalPowerQ j := by
    exact_mod_cast criticalPowerQ_pos j
  have hkPosZ : (0 : ℤ) < k := by exact_mod_cast hkPos
  rcases hadj with hadj | hadj
  · let z : ℤ :=
      (i : ℤ) * prev.q - (prev.p : ℤ) * k
    have hadjZ :
        (prev.p : ℤ) * (cur.q : ℤ) + 1 =
          (cur.p : ℤ) * (prev.q : ℤ) := by
      exact_mod_cast hadj
    have hEqZ :
        (k : ℤ) * (cur.p : ℤ) =
          (i : ℤ) * (cur.q : ℤ) := by
      simpa [cur, criticalPowerP, criticalPowerQ,
        Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) hEq
    have hkz : (k : ℤ) = (cur.q : ℤ) * z := by
      symm
      dsimp [z]
      calc
        (cur.q : ℤ) *
            ((i : ℤ) * prev.q - (prev.p : ℤ) * k)
            = ((i : ℤ) * (cur.q : ℤ)) * prev.q -
                ((prev.p : ℤ) * (cur.q : ℤ)) * k := by ring
        _ = ((k : ℤ) * (cur.p : ℤ)) * prev.q -
                ((prev.p : ℤ) * (cur.q : ℤ)) * k := by rw [← hEqZ]
        _ = (k : ℤ) *
              ((cur.p : ℤ) * prev.q -
                (prev.p : ℤ) * (cur.q : ℤ)) := by ring
        _ = (k : ℤ) := by
          have hdet :
              (cur.p : ℤ) * prev.q -
                (prev.p : ℤ) * (cur.q : ℤ) = 1 := by
            linarith
          rw [hdet]
          ring
    have hzPos : 0 < z := by nlinarith
    have hzOne : (1 : ℤ) ≤ z := by omega
    have hqLeK : (cur.q : ℤ) ≤ k := by
      rw [hkz]
      nlinarith
    have : criticalPowerQ j ≤ k := by
      exact_mod_cast hqLeK
    omega
  · let z : ℤ :=
      (prev.p : ℤ) * k - (i : ℤ) * prev.q
    have hadjZ :
        (cur.p : ℤ) * prev.q + 1 =
          (prev.p : ℤ) * (cur.q : ℤ) := by
      exact_mod_cast hadj
    have hEqZ :
        (k : ℤ) * (cur.p : ℤ) =
          (i : ℤ) * (cur.q : ℤ) := by
      simpa [cur, criticalPowerP, criticalPowerQ,
        Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) hEq
    have hkz : (k : ℤ) = (cur.q : ℤ) * z := by
      symm
      dsimp [z]
      calc
        (cur.q : ℤ) *
            ((prev.p : ℤ) * k - (i : ℤ) * prev.q)
            = ((prev.p : ℤ) * (cur.q : ℤ)) * k -
                ((i : ℤ) * (cur.q : ℤ)) * prev.q := by ring
        _ = ((prev.p : ℤ) * (cur.q : ℤ)) * k -
                ((k : ℤ) * (cur.p : ℤ)) * prev.q := by rw [← hEqZ]
        _ = (k : ℤ) *
              ((prev.p : ℤ) * (cur.q : ℤ) -
                (cur.p : ℤ) * prev.q) := by ring
        _ = (k : ℤ) := by
          have hdet :
              (prev.p : ℤ) * (cur.q : ℤ) -
                (cur.p : ℤ) * prev.q = 1 := by
            linarith
          rw [hdet]
          ring
    have hzPos : 0 < z := by nlinarith
    have hqLeK : (cur.q : ℤ) ≤ k := by
      rw [hkz]
      have hzOne : (1 : ℤ) ≤ z := by omega
      nlinarith
    have : criticalPowerQ j ≤ k := by exact_mod_cast hqLeK
    omega

private theorem floor_cross_data
    {j i : ℕ}
    (hj : 9 ≤ j)
    (hi : i < criticalPowerP j)
    (hiPos : 0 < i) :
    let k := (i * criticalPowerQ j) / criticalPowerP j
    0 < k ∧
      k < criticalPowerQ j ∧
      k * criticalPowerP j < i * criticalPowerQ j ∧
      i * criticalPowerQ j < (k + 1) * criticalPowerP j := by
  let k := (i * criticalPowerQ j) / criticalPowerP j
  have hpPos : 0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  have hqPos : 0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hkLe :
      k * criticalPowerP j ≤
        i * criticalPowerQ j := by
    dsimp [k]
    exact Nat.div_mul_le_self _ _
  have hrem :
      (i * criticalPowerQ j) % criticalPowerP j <
        criticalPowerP j :=
    Nat.mod_lt _ hpPos
  have hdecomp :=
    Nat.mod_add_div
      (i * criticalPowerQ j)
      (criticalPowerP j)
  have hdecompK :
      (i * criticalPowerQ j) % criticalPowerP j +
          k * criticalPowerP j =
        i * criticalPowerQ j := by
    simpa [k, Nat.mul_comm] using hdecomp
  have hstrictUpper :
      i * criticalPowerQ j <
        (k + 1) * criticalPowerP j := by
    calc
      i * criticalPowerQ j
          =
        (i * criticalPowerQ j) % criticalPowerP j +
          k * criticalPowerP j := hdecompK.symm
      _ <
        criticalPowerP j +
          k * criticalPowerP j :=
        Nat.add_lt_add_right
          hrem
          (k * criticalPowerP j)
      _ =
        k * criticalPowerP j +
          criticalPowerP j := by
        rw [Nat.add_comm]
      _ =
        (k + 1) * criticalPowerP j := by
        simp [Nat.add_mul]
  have hkLtQ : k < criticalPowerQ j := by
    have hiMul :
        i * criticalPowerQ j <
          criticalPowerP j * criticalPowerQ j :=
      (Nat.mul_lt_mul_right hqPos).2 hi
    have hkMulLt :
        k * criticalPowerP j <
          criticalPowerQ j * criticalPowerP j := by
      calc
        k * criticalPowerP j
            ≤ i * criticalPowerQ j := hkLe
        _ < criticalPowerP j * criticalPowerQ j := hiMul
        _ = criticalPowerQ j * criticalPowerP j := by
          rw [Nat.mul_comm]
    exact
      (Nat.mul_lt_mul_right hpPos).1 hkMulLt
  have hkPos : 0 < k := by
    have hiOne : 1 ≤ i := by
      omega
    have hP_le_iQ :
        criticalPowerP j ≤
          i * criticalPowerQ j := by
      calc
        criticalPowerP j
            ≤ criticalPowerQ j :=
          criticalPowerP_le_Q j
        _ = 1 * criticalPowerQ j := by
          simp
        _ ≤ i * criticalPowerQ j :=
          Nat.mul_le_mul_right
            (criticalPowerQ j)
            hiOne
    by_contra h0
    have hk0 : k = 0 :=
      Nat.eq_zero_of_not_pos h0
    have hstrictUpper0 := hstrictUpper
    rw [hk0] at hstrictUpper0
    simp at hstrictUpper0
    omega
  have hkStrict :
      k * criticalPowerP j <
        i * criticalPowerQ j := by
    by_contra hnot
    have heq :
        k * criticalPowerP j =
          i * criticalPowerQ j := by
      omega
    exact
      no_scaled_current_equality
        hj hiPos hkPos hkLtQ heq
  exact
    ⟨hkPos, hkLtQ, hkStrict, hstrictUpper⟩

/--
actual convergent `(P_j,Q_j)` に対し、

  k P_j < r Q_j

を満たす positive denominator `k < Q_j` の fraction `(r,k)` は、
critical slope の上側にある。

even current の場合、もし `(r,k)` も below なら
current と next の strict Farey interval に入り、
denominator lower bound に反する。

odd current の場合、もし `(r,k)` が below なら、
current が above であることとの cross-product の向きが
`k P_j < r Q_j` に直接反する。
-/
private theorem actual_floor_lower_above
    {j r k : ℕ}
    (hj : 9 ≤ j)
    (hkPos : 0 < k)
    (hkLtQ : k < criticalPowerQ j)
    (hlowCross :
      k * criticalPowerP j <
        r * criticalPowerQ j) :
    (mkCriticalFraction r k hkPos).Above := by
  let xLow :=
    mkCriticalFraction r k hkPos
  have hxAbove : xLow.Above := by
    rcases criticalPower_opposite_next (j := j) with
      hEven | hOdd
    · have hNextAbove :=
        hEven.2.2
      rcases
          CriticalPowerFraction.below_or_above_of_pos xLow with
        hxBelow | hxAbove
      · have hCurX :
            (criticalPowerConvergent j).p * xLow.q <
              xLow.p * (criticalPowerConvergent j).q := by
          simpa [
            xLow,
            mkCriticalFraction,
            criticalPowerP,
            criticalPowerQ,
            Nat.mul_comm
          ] using hlowCross
        have hXNext :=
          CriticalPowerFraction.cross_lt_of_below_above
            hxBelow
            hNextAbove
        have hden :=
          CriticalPowerFraction.denominator_ge_sum_of_strict_between
            (criticalPower_adjacent_next hj)
            (Or.inl ⟨hCurX, hXNext⟩)
        have hden' :
            criticalPowerQ j +
                criticalPowerQ (j + 1) ≤
              k := by
          simpa [
            criticalPowerQ,
            xLow,
            mkCriticalFraction
          ] using hden
        have hNextQPos :
            0 < criticalPowerQ (j + 1) :=
          criticalPowerQ_pos (j + 1)
        omega
      · exact hxAbove
    · have hCurAbove :=
        hOdd.2.1
      rcases
          CriticalPowerFraction.below_or_above_of_pos xLow with
        hxBelow | hxAbove
      · have hXCur :=
          CriticalPowerFraction.cross_lt_of_below_above
            hxBelow
            hCurAbove
        have hXCur' :
            r * criticalPowerQ j <
              criticalPowerP j * k := by
          simpa [
            xLow,
            mkCriticalFraction,
            criticalPowerP,
            criticalPowerQ
          ] using hXCur
        have hlowCross' :
            criticalPowerP j * k <
              r * criticalPowerQ j := by
          simpa [Nat.mul_comm] using hlowCross
        omega
      · exact hxAbove
  simpa [xLow] using hxAbove

/--
actual convergent `(P_j,Q_j)` に対し、

  r Q_j < (k+1) P_j

を満たし、さらに `k < Q_j` なら、
fraction `(r,k+1)` は critical slope の下側にある。

even current では above を仮定すると
current-below との cross-product が直接逆転する。

odd current では above を仮定すると
next と current の間の strict Farey interval に入り、
`k+1 ≤ Q_j` と denominator lower bound が矛盾する。
-/
private theorem actual_floor_upper_below
    {j r k : ℕ}
    (hj : 9 ≤ j)
    (hkLtQ : k < criticalPowerQ j)
    (huppCross :
      r * criticalPowerQ j <
        (k + 1) * criticalPowerP j) :
    (mkCriticalFraction r (k + 1) (by omega)).Below := by
  let xUp :=
    mkCriticalFraction r (k + 1) (by omega)
  have hxBelow : xUp.Below := by
    rcases criticalPower_opposite_next (j := j) with
      hEven | hOdd
    · have hCurBelow :=
        hEven.2.1
      rcases
          CriticalPowerFraction.below_or_above_of_pos xUp with
        hxBelow | hxAbove
      · exact hxBelow
      · have hCurUp :=
          CriticalPowerFraction.cross_lt_of_below_above
            hCurBelow
            hxAbove
        have hCurUp' :
            criticalPowerP j * (k + 1) <
              r * criticalPowerQ j := by
          simpa [
            xUp,
            mkCriticalFraction,
            criticalPowerP,
            criticalPowerQ
          ] using hCurUp
        have huppCross' :
            r * criticalPowerQ j <
              criticalPowerP j * (k + 1) := by
          simpa [Nat.mul_comm] using huppCross
        omega
    · have hNextBelow :=
        hOdd.2.2
      rcases
          CriticalPowerFraction.below_or_above_of_pos xUp with
        hxBelow | hxAbove
      · exact hxBelow
      · have hNextUp :=
          CriticalPowerFraction.cross_lt_of_below_above
            hNextBelow
            hxAbove
        have hUpCur :
            xUp.p * (criticalPowerConvergent j).q <
              (criticalPowerConvergent j).p * xUp.q := by
          simpa [
            xUp,
            mkCriticalFraction,
            criticalPowerP,
            criticalPowerQ,
            Nat.mul_comm
          ] using huppCross
        have hden :=
          CriticalPowerFraction.denominator_ge_sum_of_strict_between
            (criticalPower_adjacent_next hj)
            (Or.inr ⟨hNextUp, hUpCur⟩)
        have hden' :
            criticalPowerQ j +
                criticalPowerQ (j + 1) ≤
              k + 1 := by
          simpa [
            criticalPowerQ,
            xUp,
            mkCriticalFraction
          ] using hden
        have hkSuccLe :
            k + 1 ≤ criticalPowerQ j := by
          omega
        have hNextQPos :
            0 < criticalPowerQ (j + 1) :=
          criticalPowerQ_pos (j + 1)
        omega
  simpa [xUp] using hxBelow

/--
floor cross inequalities

  k P_j < r Q_j < (k+1) P_j

と `0 < k < Q_j` から、

  2^k < 3^r ≤ 2^(k+1)

という exact Beatty power window を得る。

Farey geometry の詳細は
`actual_floor_lower_above` と
`actual_floor_upper_below` に隔離されている。
-/
private theorem actual_floor_power_window
    {j r k : ℕ}
    (hj : 9 ≤ j)
    (hkPos : 0 < k)
    (hkLtQ : k < criticalPowerQ j)
    (hlowCross :
      k * criticalPowerP j <
        r * criticalPowerQ j)
    (huppCross :
      r * criticalPowerQ j <
        (k + 1) * criticalPowerP j) :
    2 ^ k < 3 ^ r ∧
      3 ^ r ≤ 2 ^ (k + 1) := by
  have hLower :=
    actual_floor_lower_above
      hj
      hkPos
      hkLtQ
      hlowCross
  have hUpper :=
    actual_floor_upper_below
      hj
      hkLtQ
      huppCross
  have hLowerPow :
      2 ^ k < 3 ^ r := by
    unfold CriticalPowerFraction.Above at hLower
    simpa [mkCriticalFraction] using hLower
  have hUpperPow :
      3 ^ r < 2 ^ (k + 1) := by
    unfold CriticalPowerFraction.Below at hUpper
    simpa [mkCriticalFraction] using hUpper
  exact
    ⟨hLowerPow, le_of_lt hUpperPow⟩

/--
power window

  2^k < 3^r ≤ 2^(k+1)

が与えられれば、`beattyIndex r` はちょうど `k` である。

upper inequality から `beattyIndex r ≤ k`。
逆に `beattyIndex r < k` なら、
Beatty index 自身の upper inequality と 2 冪の単調性により

  3^r ≤ 2^k

となり、strict lower inequality に反する。
-/
private theorem beattyIndex_eq_of_power_window
    {r k : ℕ}
    (hLower :
      2 ^ k < 3 ^ r)
    (hUpper :
      3 ^ r ≤ 2 ^ (k + 1)) :
    beattyIndex r = k := by
  apply Nat.le_antisymm
  · exact
      beattyIndex_le_of_upper hUpper
  · by_contra hnot
    have hb :
        beattyIndex r < k := by
      omega
    have hBeattyUpper :=
      beattyIndex_upper r
    have hPowMono :
        2 ^ (beattyIndex r + 1) ≤
          2 ^ k :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        (by omega)
    omega

/--
actual power-Farey convergent `(P_j,Q_j)` の内部では、
Beatty index は exact floor formula

  beattyIndex i = floor(i Q_j / P_j)

で与えられる。

`i=0` は自明。
`i>0` では `floor_cross_data` が与える二つの strict cross inequalityを
`actual_floor_power_window` へ渡し、
最後は `beattyIndex_eq_of_power_window` で一意性を確定する。
-/
theorem actual_beattyIndex_eq_div
    {j i : ℕ}
    (hj : 9 ≤ j)
    (hi : i < criticalPowerP j) :
    beattyIndex i =
      (i * criticalPowerQ j) / criticalPowerP j := by
  cases i with
  | zero =>
      simp
  | succ i =>
      let r := i + 1
      let k :=
        (r * criticalPowerQ j) /
          criticalPowerP j
      have hr :
          0 < r := by
        simp [r]
      have hir :
          r < criticalPowerP j := by
        simpa [r] using hi
      have hd :=
        floor_cross_data
          (j := j)
          (i := r)
          hj
          hir
          hr
      have hkPos :
          0 < k := by
        simpa [k] using hd.1
      have hkLtQ :
          k < criticalPowerQ j := by
        simpa [k] using hd.2.1
      have hlowCross :
          k * criticalPowerP j <
            r * criticalPowerQ j := by
        simpa [k] using hd.2.2.1
      have huppCross :
          r * criticalPowerQ j <
            (k + 1) * criticalPowerP j := by
        simpa [k] using hd.2.2.2
      have hWindow :=
        actual_floor_power_window
          hj
          hkPos
          hkLtQ
          hlowCross
          huppCross
      change beattyIndex r = k
      exact
        beattyIndex_eq_of_power_window
          hWindow.1
          hWindow.2


end ExternalArithmetic
end CSTMicro
end Collatz2
