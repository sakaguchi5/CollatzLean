import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RestrictedOstrowskiIntervals

/-!
# Stage 8B.1: current convergent の exact Beatty corridor

existing theorem `actual_beattyIndex_eq_div` は `x < P_j` で

  beattyIndex x = floor(x Q_j / P_j)

を与える。本ファイルでは consecutive Farey determinant `±1` を使い、current scale `j`
の式を next numerator `P_(j+1)` の直前まで延長する。

odd j:
  x < P_(j+1)      => beta(x) = floor(x Q_j / P_j)

even j:
  0 < x < P_(j+1) => beta(x) = floor((x Q_j - 1) / P_j)

この ±1 correction が even first-flat geometry の正確な源である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- positive divisor に対し、上下の倍数で挟めば quotient は一意。 -/
private theorem nat_div_eq_of_mul_bounds
    {n d k : ℕ}
    (hd : 0 < d)
    (hLower : k * d ≤ n)
    (hUpper : n < (k + 1) * d) :
    n / d = k := by
  apply Nat.le_antisymm
  · have hlt : n / d < k + 1 :=
      (Nat.div_lt_iff_lt_mul hd).2 hUpper
    omega
  · exact (Nat.le_div_iff_mul_le hd).2 hLower

/-- `k*d` を numerator に足すと floor quotient は `k` だけ増える。 -/
private theorem add_multiple_div
    (n d k : ℕ)
    (hd : 0 < d) :
    (k * d + n) / d = k + n / d := by
  let q := n / d
  have hLower0 : q * d ≤ n :=
    Nat.div_mul_le_self n d
  have hUpper0 : n < (q + 1) * d := by
    have hq : n / d < n / d + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hd).1 hq
  apply nat_div_eq_of_mul_bounds hd
  · calc
      (k + n / d) * d = k * d + (n / d) * d := by ring
      _ ≤ k * d + n := Nat.add_le_add_left hLower0 _
  · calc
      k * d + n < k * d + (n / d + 1) * d :=
        Nat.add_lt_add_left hUpper0 _
      _ = (k + n / d + 1) * d := by ring

/-- odd determinant orientation では current / next floor が next numerator まで一致。 -/
private theorem next_div_eq_current_div_of_odd_determinant
    {P Q Pn Qn x : ℕ}
    (hP : 0 < P)
    (hPn : 0 < Pn)
    (hx : x < Pn)
    (hDet : Pn * Q + 1 = P * Qn) :
    (x * Qn) / Pn = (x * Q) / P := by
  let k := (x * Q) / P
  let r := (x * Q) % P
  have hr : r < P := by
    dsimp [r]
    exact Nat.mod_lt _ hP
  have hDecomp : r + k * P = x * Q := by
    dsimp [r, k]
    simpa [Nat.mul_comm] using Nat.mod_add_div (x * Q) P
  have hCross :
      P * (x * Qn) = Pn * (x * Q) + x := by
    calc
      P * (x * Qn) = x * (P * Qn) := by ring
      _ = x * (Pn * Q + 1) := by rw [← hDet]
      _ = Pn * (x * Q) + x := by ring
  have hCross' :
      P * (x * Qn) =
        P * (k * Pn) + (r * Pn + x) := by
    rw [hCross, ← hDecomp]
    ring
  have hRemLt : r * Pn + x < P * Pn := by
    have h1 : r * Pn + x < r * Pn + Pn :=
      Nat.add_lt_add_left hx (r * Pn)
    have hrSucc : r + 1 ≤ P := by omega
    have h2 : (r + 1) * Pn ≤ P * Pn :=
      Nat.mul_le_mul_right Pn hrSucc
    calc
      r * Pn + x < r * Pn + Pn := h1
      _ = (r + 1) * Pn := by ring
      _ ≤ P * Pn := h2
  have hLowerMul :
      P * (k * Pn) ≤ P * (x * Qn) := by
    rw [hCross']
    omega
  have hUpperMul :
      P * (x * Qn) < P * ((k + 1) * Pn) := by
    calc
      P * (x * Qn)
          = P * (k * Pn) + (r * Pn + x) := hCross'
      _ < P * (k * Pn) + P * Pn :=
        Nat.add_lt_add_left hRemLt _
      _ = P * ((k + 1) * Pn) := by ring
  have hLower : k * Pn ≤ x * Qn := by
    by_contra hnot
    have hlt : x * Qn < k * Pn := by omega
    have hmul := (Nat.mul_lt_mul_left hP).2 hlt
    omega
  have hUpper : x * Qn < (k + 1) * Pn :=
    (Nat.mul_lt_mul_left hP).1 hUpperMul
  exact nat_div_eq_of_mul_bounds hPn hLower hUpper

/-- even determinant orientation gives the exact `-1` floor correction. -/
private theorem next_div_eq_current_pred_div_of_even_determinant
    {P Q Pn Qn x : ℕ}
    (hP : 0 < P)
    (hQ : 0 < Q)
    (hPn : 0 < Pn)
    (hxPos : 0 < x)
    (hx : x < Pn)
    (hDet : P * Qn + 1 = Pn * Q) :
    (x * Qn) / Pn = (x * Q - 1) / P := by
  let n := x * Q - 1
  let k := n / P
  let r := n % P
  have hxQPos : 0 < x * Q := Nat.mul_pos hxPos hQ
  have hnSucc : n + 1 = x * Q := by
    dsimp [n]
    omega
  have hr : r < P := by
    dsimp [r]
    exact Nat.mod_lt _ hP
  have hDecomp : r + k * P = n := by
    dsimp [r, k]
    simpa [Nat.mul_comm] using Nat.mod_add_div n P
  have hCross :
      P * (x * Qn) + x = Pn * (x * Q) := by
    calc
      P * (x * Qn) + x = x * (P * Qn + 1) := by ring
      _ = x * (Pn * Q) := by rw [hDet]
      _ = Pn * (x * Q) := by ring
  have hCross' :
      P * (x * Qn) + x =
        P * (k * Pn) + (r * Pn + Pn) := by
    rw [hCross, ← hnSucc, ← hDecomp]
    ring
  have hRemLe : r * Pn + Pn ≤ P * Pn := by
    have hrSucc : r + 1 ≤ P := by omega
    calc
      r * Pn + Pn = (r + 1) * Pn := by ring
      _ ≤ P * Pn := Nat.mul_le_mul_right Pn hrSucc
  have hLowerMul :
      P * (k * Pn) ≤ P * (x * Qn) := by
    omega
  have hUpperMul :
      P * (x * Qn) < P * ((k + 1) * Pn) := by
    have hLe :
        P * (x * Qn) + x ≤
          P * (k * Pn) + P * Pn := by
      calc
        P * (x * Qn) + x
            = P * (k * Pn) + (r * Pn + Pn) := hCross'
        _ ≤ P * (k * Pn) + P * Pn :=
          Nat.add_le_add_left hRemLe _
    have hLt :
        P * (x * Qn) <
          P * (k * Pn) + P * Pn := by omega
    calc
      P * (x * Qn) < P * (k * Pn) + P * Pn := hLt
      _ = P * ((k + 1) * Pn) := by ring
  have hLower : k * Pn ≤ x * Qn := by
    by_contra hnot
    have hlt : x * Qn < k * Pn := by omega
    have hmul := (Nat.mul_lt_mul_left hP).2 hlt
    omega
  have hUpper : x * Qn < (k + 1) * Pn :=
    (Nat.mul_lt_mul_left hP).1 hUpperMul
  exact nat_div_eq_of_mul_bounds hPn hLower hUpper

/-- odd current convergent の floor formula は next numerator の直前まで有効。 -/
theorem actual_beattyIndex_eq_current_div_of_odd
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex x =
      (x * criticalPowerQ j) / criticalPowerP j := by
  have hNext :=
    actual_beattyIndex_eq_div
      (j := j + 1) (i := x) (by omega) hx
  have hTransfer :=
    next_div_eq_current_div_of_odd_determinant
      (P := criticalPowerP j)
      (Q := criticalPowerQ j)
      (Pn := criticalPowerP (j + 1))
      (Qn := criticalPowerQ (j + 1))
      (x := x)
      (criticalPowerP_pos (by omega))
      (criticalPowerP_pos (by omega))
      hx
      (actualCriticalFareyDeterminant_odd hj hjOdd)
  rw [hNext, hTransfer]

/-- even current convergent では positive range に exact `-1` correction が入る。 -/
theorem actual_beattyIndex_eq_current_pred_div_of_even
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hxPos : 0 < x)
    (hx : x < criticalPowerP (j + 1)) :
    beattyIndex x =
      (x * criticalPowerQ j - 1) / criticalPowerP j := by
  have hNext :=
    actual_beattyIndex_eq_div
      (j := j + 1) (i := x) (by omega) hx
  have hTransfer :=
    next_div_eq_current_pred_div_of_even_determinant
      (P := criticalPowerP j)
      (Q := criticalPowerQ j)
      (Pn := criticalPowerP (j + 1))
      (Qn := criticalPowerQ (j + 1))
      (x := x)
      (criticalPowerP_pos (by omega))
      (criticalPowerQ_pos j)
      (criticalPowerP_pos (by omega))
      hxPos hx
      (actualCriticalFareyDeterminant_even hj hjEven)
  rw [hNext, hTransfer]

/-- `beattyIndex 1 = 1` の local explicit wrapper。 -/
theorem actual_beattyIndex_one_eq_one :
    beattyIndex 1 = 1 := by
  have hPos : 0 < beattyIndex 1 := by
    have h := beattyIndex_strictMono (a := 0) (b := 1) (by omega)
    simpa using h
  have hLe : beattyIndex 1 ≤ 1 := by
    apply beattyIndex_le_of_upper
    norm_num
  omega

/-- odd current numerator endpoint では `beta(P_j)=Q_j`。 -/
theorem actual_beattyIndex_currentP_eq_Q_of_odd
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1) :
    beattyIndex (criticalPowerP j) = criticalPowerQ j := by
  have hPLt : criticalPowerP j < criticalPowerP (j + 1) :=
    criticalPowerP_strict_succ (r := j) (by omega)
  rw [actual_beattyIndex_eq_current_div_of_odd hj hjOdd hPLt]
  have hP : 0 < criticalPowerP j := criticalPowerP_pos (by omega)
  have h := add_multiple_div 0 (criticalPowerP j) (criticalPowerQ j) hP
  simpa [Nat.mul_comm] using h

/-- even current numerator endpoint では first-flat correction `beta(P_j)=Q_j-1`。 -/
theorem actual_beattyIndex_currentP_eq_Q_pred_of_even
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0) :
    beattyIndex (criticalPowerP j) = criticalPowerQ j - 1 := by
  have hPLt : criticalPowerP j < criticalPowerP (j + 1) :=
    criticalPowerP_strict_succ (r := j) (by omega)
  rw [actual_beattyIndex_eq_current_pred_div_of_even
    hj hjEven (criticalPowerP_pos (by omega)) hPLt]
  let P := criticalPowerP j
  let Q := criticalPowerQ j
  have hP : 0 < P := by dsimp [P]; exact criticalPowerP_pos (by omega)
  have hQ : 0 < Q := by dsimp [Q]; exact criticalPowerQ_pos j
  have hQSplit : Q = (Q - 1) + 1 := by omega
  have hMul : P * Q = (Q - 1) * P + P := by
    rw [hQSplit]
    ring_nf
    simp
  have hN : P * Q - 1 = (Q - 1) * P + (P - 1) := by omega
  apply nat_div_eq_of_mul_bounds hP
  · rw [hN]
    exact Nat.le_add_right _ _
  · rw [hN]
    have hPred : P - 1 < P := by omega
    nlinarith

/-- odd corridor の exact P-periodicity。 -/
theorem actual_beattyIndex_add_currentP_eq_add_Q_of_odd
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hRange : criticalPowerP j + x < criticalPowerP (j + 1)) :
    beattyIndex (criticalPowerP j + x) =
      criticalPowerQ j + beattyIndex x := by
  have hx : x < criticalPowerP (j + 1) := by omega
  rw [actual_beattyIndex_eq_current_div_of_odd hj hjOdd hRange]
  rw [actual_beattyIndex_eq_current_div_of_odd hj hjOdd hx]
  let P := criticalPowerP j
  let Q := criticalPowerQ j
  have hP : 0 < P := by dsimp [P]; exact criticalPowerP_pos (by omega)
  have hEq : (P + x) * Q = Q * P + x * Q := by ring
  rw [hEq]
  exact add_multiple_div (x * Q) P Q hP

/-- even corridor の positive-domain exact P-periodicity。 -/
theorem actual_beattyIndex_add_currentP_eq_add_Q_of_even
    {j x : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hxPos : 0 < x)
    (hRange : criticalPowerP j + x < criticalPowerP (j + 1)) :
    beattyIndex (criticalPowerP j + x) =
      criticalPowerQ j + beattyIndex x := by
  have hx : x < criticalPowerP (j + 1) := by omega
  rw [actual_beattyIndex_eq_current_pred_div_of_even
    hj hjEven (by omega) hRange]
  rw [actual_beattyIndex_eq_current_pred_div_of_even
    hj hjEven hxPos hx]
  let P := criticalPowerP j
  let Q := criticalPowerQ j
  have hP : 0 < P := by dsimp [P]; exact criticalPowerP_pos (by omega)
  have hxQPos : 0 < x * Q := by
    dsimp [Q]
    exact Nat.mul_pos hxPos (criticalPowerQ_pos j)
  have hEq :
      (P + x) * Q - 1 = Q * P + (x * Q - 1) := by
    have : (P + x) * Q = Q * P + x * Q := by ring
    omega
  rw [hEq]
  exact add_multiple_div (x * Q - 1) P Q hP

end ExternalArithmetic
end CSTMicro
end Collatz2
