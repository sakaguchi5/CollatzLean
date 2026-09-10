import CollatzLean.Collatz3.Experimental2.MechanicalRoofDerived
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: mechanical slope の exact convergent corridor

旧 `CriticalBeattyCurrentCorridor` で使っていた算術のうち、
`2`, `3`, `beattyIndex`, `criticalPowerP/Q` に依存しない部分だけを抽出する。

本質は consecutive Farey/convergent pair の determinant `±1` である。

lower orientation:

`Q/P < σ < Qn/Pn`,  `Pn*Q + 1 = P*Qn`

upper orientation:

`Qn/Pn < σ < Q/P`,  `P*Qn + 1 = Pn*Q`

この局所 bracket があれば、global irrationality を theorem の field に重ねて保存する必要はない。
continued fraction 側の specialization が irrationality から strict bracket を供給すれば十分である。

結果として next denominator `Pn` の直前まで

lower: `floor(xσ) = (xQ)/P`
upper: `floor(xσ) = (xQ-1)/P`

が exact に成立し、current denominator `P` に沿う局所周期性も従う。
-/

namespace Collatz3
namespace Experimental2

/-- current fraction が下、next fraction が上にある consecutive Farey bracket。 -/
def IsLowerFareyBracket
    (σ : ℝ)
    (P Q Pn Qn : ℕ) : Prop :=
  0 < P ∧
    0 < Pn ∧
    (Q : ℝ) / (P : ℝ) < σ ∧
    σ < (Qn : ℝ) / (Pn : ℝ) ∧
    Pn * Q + 1 = P * Qn

/-- current fraction が上、next fraction が下にある consecutive Farey bracket。 -/
def IsUpperFareyBracket
    (σ : ℝ)
    (P Q Pn Qn : ℕ) : Prop :=
  0 < P ∧
    0 < Pn ∧
    (Qn : ℝ) / (Pn : ℝ) < σ ∧
    σ < (Q : ℝ) / (P : ℝ) ∧
    P * Qn + 1 = Pn * Q

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

/-- numerator に `k*d` を足すと quotient は `k` だけ増える。 -/
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

/-- lower determinant orientation では current / next floor quotient が `Pn` 直前まで一致。 -/
private theorem next_div_eq_current_div_of_lower_determinant
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

/-- upper determinant orientation では exact `-1` floor correction が現れる。 -/
private theorem next_div_eq_current_pred_div_of_upper_determinant
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

/-- lower Farey bracket の current quotient が real floor と exact に一致する。 -/
theorem natFloor_eq_current_div_of_lowerFarey
    {σ : ℝ}
    {P Q Pn Qn x : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hx : x < Pn) :
    ⌊(x : ℝ) * σ⌋₊ = (x * Q) / P := by
  rcases B with ⟨hP, hPn, hCurrent, hNext, hDet⟩
  by_cases hx0 : x = 0
  · subst x
    simp
  · have hxPos : 0 < x := Nat.pos_of_ne_zero hx0
    let k := (x * Q) / P
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    have hPnR : (0 : ℝ) < (Pn : ℝ) := by exact_mod_cast hPn
    have hRhoPos : 0 < σ := by
      have hNonneg : 0 ≤ (Q : ℝ) / (P : ℝ) := by positivity
      exact lt_of_le_of_lt hNonneg hCurrent
    have hNonnegXRho : 0 ≤ (x : ℝ) * σ := by positivity
    have hTransfer :=
      next_div_eq_current_div_of_lower_determinant
        hP hPn hx hDet
    apply (Nat.floor_eq_iff hNonnegXRho).2
    constructor
    · have hDivLower : k * P ≤ x * Q := by
        dsimp [k]
        exact Nat.div_mul_le_self (x * Q) P
      have hDivLowerR :
          (k : ℝ) * (P : ℝ) ≤ (x : ℝ) * (Q : ℝ) := by
        exact_mod_cast hDivLower
      have hkCurrent' :
          (k : ℝ) ≤ ((x : ℝ) * (Q : ℝ)) / (P : ℝ) :=
        (le_div_iff₀ hPR).2 hDivLowerR
      have hCurrentFrac :
          ((x : ℝ) * (Q : ℝ)) / (P : ℝ) =
            (x : ℝ) * ((Q : ℝ) / (P : ℝ)) := by
        ring
      have hkCurrent :
          (k : ℝ) ≤ (x : ℝ) * ((Q : ℝ) / (P : ℝ)) := by
        rw [← hCurrentFrac]
        exact hkCurrent'
      have hCurrentX :
          (x : ℝ) * ((Q : ℝ) / (P : ℝ)) < (x : ℝ) * σ :=
        mul_lt_mul_of_pos_left hCurrent
          (show (0 : ℝ) < (x : ℝ) by exact_mod_cast hxPos)
      exact le_trans hkCurrent (le_of_lt hCurrentX)
    · have hDivLt :
          (x * Qn) / Pn < k + 1 := by
        rw [hTransfer]
        dsimp [k]
        omega
      have hNumLt : x * Qn < (k + 1) * Pn :=
        (Nat.div_lt_iff_lt_mul hPn).1 hDivLt
      have hNumLtR :
          (x : ℝ) * (Qn : ℝ) <
            ((k + 1 : ℕ) : ℝ) * (Pn : ℝ) := by
        exact_mod_cast hNumLt
      have hNextBound' :
          ((x : ℝ) * (Qn : ℝ)) / (Pn : ℝ) < ((k : ℝ) + 1) := by
        apply (div_lt_iff₀ hPnR).2
        simpa using hNumLtR
      have hNextFrac :
          ((x : ℝ) * (Qn : ℝ)) / (Pn : ℝ) =
            (x : ℝ) * ((Qn : ℝ) / (Pn : ℝ)) := by
        ring
      have hNextBound :
          (x : ℝ) * ((Qn : ℝ) / (Pn : ℝ)) < ((k : ℝ) + 1) := by
        rw [← hNextFrac]
        exact hNextBound'
      have hRhoX :
          (x : ℝ) * σ < (x : ℝ) * ((Qn : ℝ) / (Pn : ℝ)) :=
        mul_lt_mul_of_pos_left hNext
          (show (0 : ℝ) < (x : ℝ) by exact_mod_cast hxPos)
      exact lt_trans hRhoX hNextBound

/-- upper Farey bracket では current quotient に exact `-1` correction が入る。 -/
theorem natFloor_eq_current_pred_div_of_upperFarey
    {σ : ℝ}
    {P Q Pn Qn x : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hx : x < Pn) :
    ⌊(x : ℝ) * σ⌋₊ = (x * Q - 1) / P := by
  rcases B with ⟨hP, hPn, hNext, hCurrent, hDet⟩
  by_cases hx0 : x = 0
  · subst x
    simp
  · have hxPos : 0 < x := Nat.pos_of_ne_zero hx0
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    have hPnR : (0 : ℝ) < (Pn : ℝ) := by exact_mod_cast hPn
    have hRhoPos : 0 < σ := by
      have hNonneg : 0 ≤ (Qn : ℝ) / (Pn : ℝ) := by positivity
      exact lt_of_le_of_lt hNonneg hNext
    have hQPos : 0 < Q := by
      by_contra hnot
      have hQZero : Q = 0 := Nat.eq_zero_of_not_pos hnot
      subst Q
      norm_num at hCurrent
      linarith
    have hNonnegXRho : 0 ≤ (x : ℝ) * σ := by positivity
    let k := (x * Q - 1) / P
    have hTransfer :=
      next_div_eq_current_pred_div_of_upper_determinant
        hP hQPos hPn hxPos hx hDet
    apply (Nat.floor_eq_iff hNonnegXRho).2
    constructor
    · have hDivLower : k * Pn ≤ x * Qn := by
        apply (Nat.le_div_iff_mul_le hPn).1
        rw [hTransfer]
      have hDivLowerR :
          (k : ℝ) * (Pn : ℝ) ≤ (x : ℝ) * (Qn : ℝ) := by
        exact_mod_cast hDivLower
      have hkNext' :
          (k : ℝ) ≤ ((x : ℝ) * (Qn : ℝ)) / (Pn : ℝ) :=
        (le_div_iff₀ hPnR).2 hDivLowerR
      have hNextFrac :
          ((x : ℝ) * (Qn : ℝ)) / (Pn : ℝ) =
            (x : ℝ) * ((Qn : ℝ) / (Pn : ℝ)) := by
        ring
      have hkNext :
          (k : ℝ) ≤ (x : ℝ) * ((Qn : ℝ) / (Pn : ℝ)) := by
        rw [← hNextFrac]
        exact hkNext'
      have hNextX :
          (x : ℝ) * ((Qn : ℝ) / (Pn : ℝ)) < (x : ℝ) * σ :=
        mul_lt_mul_of_pos_left hNext
        (show (0 : ℝ) < (x : ℝ) by exact_mod_cast hxPos)
      exact le_trans (by simpa [k] using hkNext) (le_of_lt hNextX)
    · have hxQPos : 0 < x * Q := Nat.mul_pos hxPos hQPos
      have hDivLt :
          (x * Q - 1) / P < k + 1 := by
        dsimp [k]
        omega
      have hPredLt : x * Q - 1 < (k + 1) * P :=
        (Nat.div_lt_iff_lt_mul hP).1 hDivLt
      have hNumLe : x * Q ≤ (k + 1) * P := by omega
      have hNumLeR :
          (x : ℝ) * (Q : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) * (P : ℝ) := by
        exact_mod_cast hNumLe
      have hCurrentBound' :
          ((x : ℝ) * (Q : ℝ)) / (P : ℝ) ≤ ((k : ℝ) + 1) := by
        apply (div_le_iff₀ hPR).2
        simpa using hNumLeR
      have hCurrentFrac :
          ((x : ℝ) * (Q : ℝ)) / (P : ℝ) =
            (x : ℝ) * ((Q : ℝ) / (P : ℝ)) := by
        ring
      have hCurrentBound :
          (x : ℝ) * ((Q : ℝ) / (P : ℝ)) ≤ ((k : ℝ) + 1) := by
        rw [← hCurrentFrac]
        exact hCurrentBound'
      have hRhoX :
          (x : ℝ) * σ < (x : ℝ) * ((Q : ℝ) / (P : ℝ)) :=
          mul_lt_mul_of_pos_left hCurrent
          (show (0 : ℝ) < (x : ℝ) by exact_mod_cast hxPos)
      exact lt_of_lt_of_le hRhoX hCurrentBound

/-- lower corridor の current denominator endpoint。 -/
theorem natFloor_currentP_eq_Q_of_lowerFarey
    {σ : ℝ}
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn) :
    ⌊(P : ℝ) * σ⌋₊ = Q := by
  have hFloor := natFloor_eq_current_div_of_lowerFarey B hPLt
  rw [hFloor]
  rcases B with ⟨hP, _⟩
  have h := add_multiple_div 0 P Q hP
  simpa [Nat.mul_comm] using h

/-- upper corridor の current denominator endpoint。 -/
theorem natFloor_currentP_eq_Q_sub_one_of_upperFarey
    {σ : ℝ}
    {P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hPLt : P < Pn) :
    ⌊(P : ℝ) * σ⌋₊ = Q - 1 := by
  have hFloor := natFloor_eq_current_pred_div_of_upperFarey B hPLt
  rw [hFloor]
  rcases B with ⟨hP, _hPn, hNext, hCurrent, _hDet⟩
  have hRhoPos : 0 < σ := by
    have hNonneg : 0 ≤ (Qn : ℝ) / (Pn : ℝ) := by positivity
    exact lt_of_le_of_lt hNonneg hNext
  have hQPos : 0 < Q := by
    by_contra hnot
    have hQZero : Q = 0 := Nat.eq_zero_of_not_pos hnot
    subst Q
    norm_num at hCurrent
    linarith
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

/-- lower corridor の exact `P`-periodicity。 -/
theorem natFloor_add_currentP_eq_add_Q_of_lowerFarey
    {σ : ℝ}
    {P Q Pn Qn x : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hRange : P + x < Pn) :
    ⌊((P + x : ℕ) : ℝ) * σ⌋₊ =
      Q + ⌊(x : ℝ) * σ⌋₊ := by
  have hx : x < Pn := by omega
  rw [natFloor_eq_current_div_of_lowerFarey B hRange]
  rw [natFloor_eq_current_div_of_lowerFarey B hx]
  rcases B with ⟨hP, _⟩
  have hEq : (P + x) * Q = Q * P + x * Q := by ring
  rw [hEq]
  exact add_multiple_div (x * Q) P Q hP

/-- upper corridor の positive-domain exact `P`-periodicity。 -/
theorem natFloor_add_currentP_eq_add_Q_of_upperFarey
    {σ : ℝ}
    {P Q Pn Qn x : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hxPos : 0 < x)
    (hRange : P + x < Pn) :
    ⌊((P + x : ℕ) : ℝ) * σ⌋₊ =
      Q + ⌊(x : ℝ) * σ⌋₊ := by
  have hx : x < Pn := by omega
  rw [natFloor_eq_current_pred_div_of_upperFarey B hRange]
  rw [natFloor_eq_current_pred_div_of_upperFarey B hx]
  rcases B with ⟨hP, _hPn, hNext, hCurrent, _hDet⟩
  have hRhoPos : 0 < σ := by
    have hNonneg : 0 ≤ (Qn : ℝ) / (Pn : ℝ) := by positivity
    exact lt_of_le_of_lt hNonneg hNext
  have hQPos : 0 < Q := by
    by_contra hnot
    have hQZero : Q = 0 := Nat.eq_zero_of_not_pos hnot
    subst Q
    norm_num at hCurrent
    linarith
  have hxQPos : 0 < x * Q := Nat.mul_pos hxPos hQPos
  have hEq :
      (P + x) * Q - 1 = Q * P + (x * Q - 1) := by
    have hRaw : (P + x) * Q = Q * P + x * Q := by ring
    omega
  rw [hEq]
  exact add_multiple_div (x * Q - 1) P Q hP

namespace IsLowerMechanicalRoof

/-- lower Farey corridor を full-slope lower mechanical roof 本体へ持ち上げる。 -/
theorem eq_current_div_of_lowerFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn x : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hx : x < Pn) :
    β x = (x * Q) / P := by
  rw [M.eq_natFloor']
  exact natFloor_eq_current_div_of_lowerFarey B hx

/-- upper Farey corridor の exact `-1` correction を lower mechanical roof 本体へ持ち上げる。 -/
theorem eq_current_pred_div_of_upperFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn x : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hx : x < Pn) :
    β x = (x * Q - 1) / P := by
  rw [M.eq_natFloor']
  exact natFloor_eq_current_pred_div_of_upperFarey B hx

/-- lower corridor の exact `P`-periodicity を roof 本体へ持ち上げる。 -/
theorem add_currentP_eq_add_Q_of_lowerFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn x : ℕ}
    (B : IsLowerFareyBracket σ P Q Pn Qn)
    (hRange : P + x < Pn) :
    β (P + x) = Q + β x := by
  rw [M.eq_natFloor' (P + x)]
  rw [M.eq_natFloor' x]
  exact natFloor_add_currentP_eq_add_Q_of_lowerFarey B hRange

/-- upper corridor の positive-domain exact `P`-periodicity を roof 本体へ持ち上げる。 -/
theorem add_currentP_eq_add_Q_of_upperFarey
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {P Q Pn Qn x : ℕ}
    (B : IsUpperFareyBracket σ P Q Pn Qn)
    (hxPos : 0 < x)
    (hRange : P + x < Pn) :
    β (P + x) = Q + β x := by
  rw [M.eq_natFloor' (P + x)]
  rw [M.eq_natFloor' x]
  exact natFloor_add_currentP_eq_add_Q_of_upperFarey B hxPos hRange

end IsLowerMechanicalRoof

end Experimental2
end Collatz3
