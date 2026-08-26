import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalNearRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselZeroCycleBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalFareyComparison



/-!
# Attached Hensel: right-end smallness target

repeated-block transport は

  2^m M_m = 3^m M_0

である。従って entrance smallness

  |M_0| < 2^m

を直接示す代わりに、right-end smallness

  |M_m| < 3^m

を示せば十分である。

この版では terminal-near smallness の interface を二点修正する。

* `m = 0` は除外し、repeat length は `0 < m` とする。
* forced terminal-near theorem が供給する

    j <= width - (2*m+2) + (m+1)

  を obligation まで保持する。

さらに actual straight suffix 上の fused state

  S_i = 2^(delta_i) Z_i + Q_i

を一つの整数列として包み、terminal predecessor までの exact transport

  3^(d+1) S_i = 2^d E

を証明する。ここで

  d = width - 1 - i,
  E = terminalCarryRhs.

最後に、terminal-near repeat の右端 `u=i+m`, `v=j+m` に対し
二本の terminal-anchor budget

  2^d_v E <= 3^(m+d_v+1),
  2^(Delta+d_u) E <= 3^(m+d_u+1)

から exact に

  -3^m < M_m < 3^m

を導く。従って今後の未解決部分は `M_m` 自体の直接評価ではなく、
この二本の anchor budget の証明へ分離される。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/--
right-end open bound `(-3^m,3^m)` は transport を通して entrance open bound
`(-2^m,2^m)` を与える。
-/
theorem scaledDifference_zero_small_of_end_small
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hLower :
      -((3 : ℤ) ^ m) < C.scaledDifference i j Delta m)
    (hUpper :
      C.scaledDifference i j Delta m < (3 : ℤ) ^ m) :
    -((2 : ℤ) ^ m) < C.scaledDifference i j Delta 0 ∧
      C.scaledDifference i j Delta 0 < (2 : ℤ) ^ m := by
  have hTransport := C.scaledDifference_transport hiEnd hjEnd hBlock
  have hTwoPos : 0 < (2 : ℤ) ^ m := by positivity
  have hThreePos : 0 < (3 : ℤ) ^ m := by positivity
  have hLowerScaled :
      (2 : ℤ) ^ m * (-((3 : ℤ) ^ m)) <
        (2 : ℤ) ^ m * C.scaledDifference i j Delta m :=
    (Int.mul_lt_mul_left hTwoPos).2 hLower
  have hLowerTransport :
      (3 : ℤ) ^ m * (-((2 : ℤ) ^ m)) <
        (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 := by
    calc
      (3 : ℤ) ^ m * (-((2 : ℤ) ^ m))
          = (2 : ℤ) ^ m * (-((3 : ℤ) ^ m)) := by ring
      _ < (2 : ℤ) ^ m * C.scaledDifference i j Delta m :=
        hLowerScaled
      _ = (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 :=
        hTransport
  have hLower0 :
      -((2 : ℤ) ^ m) < C.scaledDifference i j Delta 0 :=
    (Int.mul_lt_mul_left hThreePos).1 hLowerTransport
  have hUpperScaled :
      (2 : ℤ) ^ m * C.scaledDifference i j Delta m <
        (2 : ℤ) ^ m * (3 : ℤ) ^ m :=
    (Int.mul_lt_mul_left hTwoPos).2 hUpper
  have hUpperTransport :
      (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 <
        (3 : ℤ) ^ m * (2 : ℤ) ^ m := by
    calc
      (3 : ℤ) ^ m * C.scaledDifference i j Delta 0
          = (2 : ℤ) ^ m * C.scaledDifference i j Delta m :=
        hTransport.symm
      _ < (2 : ℤ) ^ m * (3 : ℤ) ^ m := hUpperScaled
      _ = (3 : ℤ) ^ m * (2 : ℤ) ^ m := by ring
  have hUpper0 :
      C.scaledDifference i j Delta 0 < (2 : ℤ) ^ m :=
    (Int.mul_lt_mul_left hThreePos).1 hUpperTransport
  exact ⟨hLower0, hUpper0⟩

/-- `3^m` の倍数が open interval `(-3^m,3^m)` に入るなら zero。 -/
theorem eq_zero_of_threePow_dvd_of_strict_between
    {m : ℕ}
    {z : ℤ}
    (hDvd : (3 : ℤ) ^ m ∣ z)
    (hLower : -((3 : ℤ) ^ m) < z)
    (hUpper : z < (3 : ℤ) ^ m) :
    z = 0 := by
  rcases hDvd with ⟨k, hk⟩
  have hPowPos : 0 < (3 : ℤ) ^ m := by positivity
  by_contra hz
  have hkNe : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    exact hz hk
  rcases lt_or_gt_of_ne hkNe with hkNeg | hkPos
  · have hkLe : k ≤ -1 := by omega
    have hMulLe :
        (3 : ℤ) ^ m * k ≤ -((3 : ℤ) ^ m) := by
      calc
        (3 : ℤ) ^ m * k
            ≤ (3 : ℤ) ^ m * (-1) :=
          mul_le_mul_of_nonneg_left hkLe (le_of_lt hPowPos)
        _ = -((3 : ℤ) ^ m) := by ring
    rw [← hk] at hMulLe
    linarith
  · have hkGe : 1 ≤ k := by omega
    have hMulGe :
        (3 : ℤ) ^ m ≤ (3 : ℤ) ^ m * k := by
      calc
        (3 : ℤ) ^ m = (3 : ℤ) ^ m * 1 := by ring
        _ ≤ (3 : ℤ) ^ m * k :=
          mul_le_mul_of_nonneg_left hkGe (le_of_lt hPowPos)
    rw [← hk] at hMulGe
    linarith

end FreeBaseMonotoneHenselChain

namespace AttachedTwoCornerPacket

/-! ## 1. actual straight fused state -/

/--
attached straight suffix の index `i` における actual fused state。
有効範囲外では `0` とする。後段で使う theorem はすべて `i < width` を仮定する。

この wrapper により `integralCriticalTailStateInt` の proof arguments を後段から隠す。
-/
noncomputable def straightCriticalFusedState
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (i : ℕ) : ℤ :=
  if hi : i < A.straightHenselWidth then
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let I := P.criticalizationStart_spec
    let k := A.straightHenselStart + i
    let hkCrit : P.criticalizationStart ≤ k := by
      have hCrit := A.criticalization_le_previous
      dsimp [k]
      unfold straightHenselStart
      omega
    let hkM : k ≤ P.m := by
      have hEnd := A.straightHenselStart_add_width
      have hcM := P.terminalCriticalStart_spec.1
      dsimp [k]
      omega
    attachedCriticalFusedValue
      (C.delta i)
      (P.integralCriticalTailStateInt I k hkCrit hkM)
      (C.qOne i)
  else
    0

/-- actual straight fused state は一段で exact に `3 S_i = 2 S_(i+1)`。 -/
theorem straightCriticalFusedState_step
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hiNext : i + 1 < A.straightHenselWidth) :
    3 * A.straightCriticalFusedState hStart i =
      2 * A.straightCriticalFusedState hStart (i + 1) := by
  have hi : i < A.straightHenselWidth := by omega
  have h := A.straight_criticalFusedValue_transport hStart hiNext
  simpa [straightCriticalFusedState, hi, hiNext, Nat.add_assoc] using h

/--
一段 transport を `d` 回反復する。

  3^d S_i = 2^d S_(i+d).
-/
theorem straightCriticalFusedState_transport
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i d : ℕ}
    (hEnd : i + d < A.straightHenselWidth) :
    (3 : ℤ) ^ d * A.straightCriticalFusedState hStart i =
      (2 : ℤ) ^ d * A.straightCriticalFusedState hStart (i + d) := by
  revert hEnd
  induction d with
  | zero =>
      intro hEnd
      simp
  | succ d ih =>
      intro hEnd
      have hPrevEnd : i + d < A.straightHenselWidth := by omega
      have hIH := ih hPrevEnd
      have hStep :=
        A.straightCriticalFusedState_step
          hStart
          (i := i + d)
          (by omega)
      have hIdx : i + d + 1 = i + (d + 1) := by omega
      rw [hIdx] at hStep
      rw [pow_succ, pow_succ]
      calc
        (3 : ℤ) ^ d * 3 * A.straightCriticalFusedState hStart i
            = 3 *
                ((3 : ℤ) ^ d * A.straightCriticalFusedState hStart i) := by
              ring
        _ = 3 *
              ((2 : ℤ) ^ d *
                A.straightCriticalFusedState hStart (i + d)) := by
              rw [hIH]
        _ = (2 : ℤ) ^ d *
              (3 * A.straightCriticalFusedState hStart (i + d)) := by
              ring
        _ = (2 : ℤ) ^ d *
              (2 * A.straightCriticalFusedState hStart (i + (d + 1))) := by
              rw [hStep]
        _ = (2 : ℤ) ^ d * 2 *
              A.straightCriticalFusedState hStart (i + (d + 1)) := by
              ring

/--
straight suffix の最後の occupied index は actual terminal predecessor。
その fused state は `terminalCarryRhs` に exact に anchor される。
-/
theorem straightCriticalFusedState_terminalPred_anchor
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) :
    3 * A.straightCriticalFusedState
        hStart (A.straightHenselWidth - 1) =
      A.terminalCarryRhs := by
  have hWidthPos := A.straightHenselWidth_pos
  have hi : A.straightHenselWidth - 1 < A.straightHenselWidth := by
    omega
  have hPredIdx :
      A.straightHenselStart + (A.straightHenselWidth - 1) =
        A.normalForm.terminal := by
    have hEnd := A.straightHenselStart_add_width
    have hSucc := A.terminal_succ_eq_terminalCriticalStart
    omega
  have hPred := A.terminalPred_criticalFusedValue_eq_carry hStart
  have hRhs := A.terminalPred_carry_rhs_eq_terminalCarryRhs
  dsimp at hPred hRhs
  rw [hRhs] at hPred
  unfold straightCriticalFusedState
  rw [dite_eq_left hi]
  dsimp [toFreeBaseMonotoneHenselChain, FreeBaseMonotoneHenselChain.qOne]
  simpa only [hPredIdx] using hPred

/--
任意の occupied straight index から terminal carry RHS までの exact transport。

  d = width - 1 - i

とすると

  3^(d+1) S_i = 2^d E.
-/
theorem straightCriticalFusedState_to_terminalCarryRhs
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let d := A.straightHenselWidth - 1 - i
    (3 : ℤ) ^ (d + 1) * A.straightCriticalFusedState hStart i =
      (2 : ℤ) ^ d * A.terminalCarryRhs := by
  dsimp
  let d := A.straightHenselWidth - 1 - i
  have hWidthPos := A.straightHenselWidth_pos
  have hIdx : i + d = A.straightHenselWidth - 1 := by
    dsimp [d]
    omega
  have hEnd : i + d < A.straightHenselWidth := by
    rw [hIdx]
    omega
  have hTransport :=
    A.straightCriticalFusedState_transport hStart hEnd
  rw [hIdx] at hTransport
  have hAnchor := A.straightCriticalFusedState_terminalPred_anchor hStart
  calc
    (3 : ℤ) ^ (d + 1) * A.straightCriticalFusedState hStart i
        = 3 *
            ((3 : ℤ) ^ d * A.straightCriticalFusedState hStart i) := by
          rw [pow_succ]
          ring
    _ = 3 *
          ((2 : ℤ) ^ d *
            A.straightCriticalFusedState
              hStart (A.straightHenselWidth - 1)) := by
          rw [hTransport]
    _ = (2 : ℤ) ^ d *
          (3 * A.straightCriticalFusedState
            hStart (A.straightHenselWidth - 1)) := by
          ring
    _ = (2 : ℤ) ^ d * A.terminalCarryRhs := by
          rw [hAnchor]

/-! ## 2. qOne と fused state の positivity/dominance -/

/--
`y >= 0` の下では actual critical state は非負であり、
`Q_i=q_i+1` は正なので

  0 < Q_i <= S_i

となる。
-/
theorem straight_qOne_pos_and_le_fused
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hy : 0 ≤ P.y)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    0 < C.qOne i ∧
      C.qOne i ≤ A.straightCriticalFusedState hStart i := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let I := P.criticalizationStart_spec
  let k := A.straightHenselStart + i
  have hkCrit : P.criticalizationStart ≤ k := by
    dsimp [k]
    have hCrit := A.criticalization_le_previous
    unfold straightHenselStart
    omega
  have hkC : k ≤ P.terminalCriticalStart := by
    dsimp [k]
    have hEnd := A.straightHenselStart_add_width
    omega
  have hkM : k ≤ P.m :=
    le_trans hkC P.terminalCriticalStart_spec.1
  have hQNonneg : 0 ≤ C.q i := by
    dsimp [C, k, toFreeBaseMonotoneHenselChain]
    exact terminalCarryTailQuotient_nonneg P hStart hkCrit hkC
  have hQPos : 0 < C.qOne i := by
    unfold FreeBaseMonotoneHenselChain.qOne
    linarith
  have hZNonneg :
      0 ≤ P.integralCriticalTailStateInt I k hkCrit hkM :=
    P.integralCriticalTailStateInt_nonneg I hy hkCrit hkM
  have hPowNonneg : 0 ≤ (2 : ℤ) ^ C.delta i := by positivity
  have hTermNonneg :
      0 ≤ (2 : ℤ) ^ C.delta i *
        P.integralCriticalTailStateInt I k hkCrit hkM :=
    mul_nonneg hPowNonneg hZNonneg
  have hState :
      A.straightCriticalFusedState hStart i =
        (2 : ℤ) ^ C.delta i *
            P.integralCriticalTailStateInt I k hkCrit hkM +
          C.qOne i := by
    simp [
      straightCriticalFusedState,
      hi,
      C,
      k,
      attachedCriticalFusedValue
    ]
  constructor
  · exact hQPos
  · rw [hState]
    linarith

/-! ## 3. selected repeat smallness reduction -/

/--
terminal-near repeat の右端 `u=i+m`, `v=j+m` を考える。
terminal までの距離を

  d_u = width - 1 - u,
  d_v = width - 1 - v

とする。

二本の anchor budget

  2^d_v E <= 3^(m+d_v+1),
  2^(Delta+d_u) E <= 3^(m+d_u+1)

があれば、fused transport と `0 < Q <= S` だけから

  -3^m < M_m < 3^m

が従う。
-/
theorem selectedRepeat_end_small_of_terminalCarryRhs_budgets
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hy : 0 ≤ P.y)
    {m i j Delta : ℕ}
    (hij : i < j)
    (hjEnd :
      j + m <
        (A.toFreeBaseMonotoneHenselChain hStart).width)
    (hBudgetV :
      let dV :=
        A.straightHenselWidth - 1 - (j + m)
      (2 : ℤ) ^ dV * A.terminalCarryRhs ≤
        (3 : ℤ) ^ (m + dV + 1))
    (hBudgetU :
      let dU :=
        A.straightHenselWidth - 1 - (i + m)
      (2 : ℤ) ^ (Delta + dU) * A.terminalCarryRhs ≤
        (3 : ℤ) ^ (m + dU + 1)) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    (
      -((3 : ℤ) ^ m) <
          C.scaledDifference i j Delta m ∧
        C.scaledDifference i j Delta m <
          (3 : ℤ) ^ m
    ) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let u := i + m
  let v := j + m
  let dU := A.straightHenselWidth - 1 - u
  let dV := A.straightHenselWidth - 1 - v
  have hWidthC : C.width = A.straightHenselWidth := by
    rfl
  have hv : v < A.straightHenselWidth := by
    dsimp [v]
    rw [← hWidthC]
    exact hjEnd
  have hu : u < A.straightHenselWidth := by
    dsimp [u, v] at hv ⊢
    omega
  have hAnchorU :
      (3 : ℤ) ^ (dU + 1) *
          A.straightCriticalFusedState hStart u =
        (2 : ℤ) ^ dU * A.terminalCarryRhs := by
    simpa [dU] using
      (A.straightCriticalFusedState_to_terminalCarryRhs
        hStart hu)
  have hAnchorV :
      (3 : ℤ) ^ (dV + 1) *
          A.straightCriticalFusedState hStart v =
        (2 : ℤ) ^ dV * A.terminalCarryRhs := by
    simpa [dV] using
      (A.straightCriticalFusedState_to_terminalCarryRhs
        hStart hv)
  have hBudgetU' :
      (2 : ℤ) ^ (Delta + dU) * A.terminalCarryRhs ≤
        (3 : ℤ) ^ (m + dU + 1) := by
    simpa [dU, u] using hBudgetU
  have hBudgetV' :
      (2 : ℤ) ^ dV * A.terminalCarryRhs ≤
        (3 : ℤ) ^ (m + dV + 1) := by
    simpa [dV, v] using hBudgetV
  have hQU := A.straight_qOne_pos_and_le_fused hStart hy hu
  have hQV := A.straight_qOne_pos_and_le_fused hStart hy hv
  have hExpV : m + dV + 1 = (dV + 1) + m := by omega
  have hVScaled :
      (3 : ℤ) ^ (dV + 1) *
          A.straightCriticalFusedState hStart v ≤
        (3 : ℤ) ^ (dV + 1) * (3 : ℤ) ^ m := by
    calc
      (3 : ℤ) ^ (dV + 1) *
          A.straightCriticalFusedState hStart v
          = (2 : ℤ) ^ dV * A.terminalCarryRhs := hAnchorV
      _ ≤ (3 : ℤ) ^ (m + dV + 1) := hBudgetV'
      _ = (3 : ℤ) ^ (dV + 1) * (3 : ℤ) ^ m := by
            rw [hExpV, pow_add]
  have hThreeVPos : 0 < (3 : ℤ) ^ (dV + 1) := by positivity
  have hSV :
      A.straightCriticalFusedState hStart v ≤ (3 : ℤ) ^ m :=
    (Int.mul_le_mul_left hThreeVPos).1 hVScaled
  have hAnchorUScaled :
      (3 : ℤ) ^ (dU + 1) *
          ((2 : ℤ) ^ Delta *
            A.straightCriticalFusedState hStart u) =
        (2 : ℤ) ^ (Delta + dU) * A.terminalCarryRhs := by
    calc
      (3 : ℤ) ^ (dU + 1) *
          ((2 : ℤ) ^ Delta *
            A.straightCriticalFusedState hStart u)
          = (2 : ℤ) ^ Delta *
              ((3 : ℤ) ^ (dU + 1) *
                A.straightCriticalFusedState hStart u) := by
              ring
      _ = (2 : ℤ) ^ Delta *
            ((2 : ℤ) ^ dU * A.terminalCarryRhs) := by
              rw [hAnchorU]
      _ = (2 : ℤ) ^ (Delta + dU) * A.terminalCarryRhs := by
              rw [pow_add]
              ring
  have hExpU : m + dU + 1 = (dU + 1) + m := by omega
  have hUScaled :
      (3 : ℤ) ^ (dU + 1) *
          ((2 : ℤ) ^ Delta *
            A.straightCriticalFusedState hStart u) ≤
        (3 : ℤ) ^ (dU + 1) * (3 : ℤ) ^ m := by
    calc
      (3 : ℤ) ^ (dU + 1) *
          ((2 : ℤ) ^ Delta *
            A.straightCriticalFusedState hStart u)
          = (2 : ℤ) ^ (Delta + dU) * A.terminalCarryRhs :=
            hAnchorUScaled
      _ ≤ (3 : ℤ) ^ (m + dU + 1) := hBudgetU'
      _ = (3 : ℤ) ^ (dU + 1) * (3 : ℤ) ^ m := by
            rw [hExpU, pow_add]
  have hThreeUPos : 0 < (3 : ℤ) ^ (dU + 1) := by positivity
  have hSU :
      (2 : ℤ) ^ Delta * A.straightCriticalFusedState hStart u ≤
        (3 : ℤ) ^ m :=
    (Int.mul_le_mul_left hThreeUPos).1 hUScaled
  have hTwoDeltaNonneg : 0 ≤ (2 : ℤ) ^ Delta := by positivity
  have hTwoDeltaPos : 0 < (2 : ℤ) ^ Delta := by positivity
  have hQUScaledLe :
      (2 : ℤ) ^ Delta * C.qOne u ≤
        (2 : ℤ) ^ Delta * A.straightCriticalFusedState hStart u :=
    mul_le_mul_of_nonneg_left hQU.2 hTwoDeltaNonneg
  have hQUScaledPos : 0 < (2 : ℤ) ^ Delta * C.qOne u :=
    mul_pos hTwoDeltaPos hQU.1
  have hQUScaledPow :
      (2 : ℤ) ^ Delta * C.qOne u ≤ (3 : ℤ) ^ m :=
    le_trans hQUScaledLe hSU
  have hQVPow : C.qOne v ≤ (3 : ℤ) ^ m :=
    le_trans hQV.2 hSV
  unfold FreeBaseMonotoneHenselChain.scaledDifference
  constructor
  · linarith [hQV.1, hQUScaledPow]
  · linarith [hQVPow, hQUScaledPos]

/--
terminal-near repeat に必要な二本の terminal-anchor budget。

この Prop は smallness そのものではなく、今後 three-clearance から供給すべき
純粋な growth comparison だけを隔離する。
-/
def AttachedTerminalNearAnchorBudgetObligation
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) : Prop :=
  let C := A.toFreeBaseMonotoneHenselChain hStart
  ∀ (m i j Delta : ℕ),
    0 < m →
    2 * m + 2 ≤ C.width →
    C.width - (2 * m + 2) ≤ i →
    i < j →
    j ≤ C.width - (2 * m + 2) + (m + 1) →
    j + m < C.width →
    C.SameDeltaOffsetBlock i j m Delta →
      let dU := C.width - 1 - (i + m)
      let dV := C.width - 1 - (j + m)
      (2 : ℤ) ^ dV * A.terminalCarryRhs ≤
          (3 : ℤ) ^ (m + dV + 1) ∧
        (2 : ℤ) ^ (Delta + dU) * A.terminalCarryRhs ≤
          (3 : ℤ) ^ (m + dU + 1)

/--
修正版 terminal-near right-end smallness obligation。

`m=0` を除外し、forced theorem の `j`-band 条件を保持する。
-/
def AttachedTerminalNearEndSmallnessObligation
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) : Prop :=
  let C := A.toFreeBaseMonotoneHenselChain hStart
  ∀ (m i j Delta : ℕ),
    0 < m →
    2 * m + 2 ≤ C.width →
    C.width - (2 * m + 2) ≤ i →
    i < j →
    j ≤ C.width - (2 * m + 2) + (m + 1) →
    j + m < C.width →
    C.SameDeltaOffsetBlock i j m Delta →
    C.scaledDifference i j Delta 0 ≠ 0 →
      -((3 : ℤ) ^ m) < C.scaledDifference i j Delta m ∧
        C.scaledDifference i j Delta m < (3 : ℤ) ^ m

/--
二本の terminal-anchor budget があれば修正版 end-smallness obligation が従う。

これにより未解決部分は `AttachedTerminalNearAnchorBudgetObligation` にだけ残る。
-/
theorem terminalNearEndSmallness_of_anchorBudget
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hy : 0 ≤ P.y)
    (hBudget : A.AttachedTerminalNearAnchorBudgetObligation hStart) :
    A.AttachedTerminalNearEndSmallnessObligation hStart := by
  dsimp [AttachedTerminalNearEndSmallnessObligation]
  dsimp [AttachedTerminalNearAnchorBudgetObligation] at hBudget
  intro m i j Delta hm hWidth hiNear hij hjBand hjEnd hBlock hNonzero
  have hBudgets :=
    hBudget m i j Delta hm hWidth hiNear hij hjBand hjEnd hBlock
  apply A.selectedRepeat_end_small_of_terminalCarryRhs_budgets
    hStart hy hij hjEnd
  · exact hBudgets.1
  · exact hBudgets.2

/-! ## 4. corrected terminal-near zero reduction -/

/--
right-end smallness があれば positive-length terminal-near forced repeat は
zero difference を持つ。
-/
theorem exists_terminalNear_zero_scaledDifference_of_endSmallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedTerminalNearEndSmallnessObligation hStart)
    (m : ℕ)
    (hm : 0 < m)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      C.width - (2 * m + 2) ≤ i ∧
      i < j ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.scaledDifference i j Delta 0 = 0 := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_terminalNear_sameDeltaOffsetBlock
        hStart m hWidth with
    ⟨i, j, Delta, hiNear, hij, hjBand, hjEnd, hBlock⟩
  have hWidthC : 2 * m + 2 ≤ C.width := by
    change 2 * m + 2 ≤ A.straightHenselWidth
    exact hWidth
  by_cases hZero : C.scaledDifference i j Delta 0 = 0
  · exact ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hZero⟩
  · have hBounds :=
      hSmall m i j Delta hm hWidthC hiNear hij hjBand hjEnd hBlock hZero
    have hjEndC : j + m < C.width := by
      simpa [C, toFreeBaseMonotoneHenselChain] using hjEnd
    have hiEnd : i + m ≤ C.width := by
      omega
    have hjEndLe : j + m ≤ C.width :=
      Nat.le_of_lt hjEndC
    have hDvdEnd :=
      C.threePow_dvd_scaledDifference_end hiEnd hjEndLe hBlock
    have hEndZero : C.scaledDifference i j Delta m = 0 :=
      FreeBaseMonotoneHenselChain.eq_zero_of_threePow_dvd_of_strict_between
        hDvdEnd hBounds.1 hBounds.2
    have hTransport := C.scaledDifference_transport hiEnd hjEndLe hBlock
    rw [hEndZero, mul_zero] at hTransport
    have hThreeNe : (3 : ℤ) ^ m ≠ 0 := by positivity
    have hEntryZero : C.scaledDifference i j Delta 0 = 0 := by
      have hProd :
          (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 = 0 := by
        simpa using hTransport.symm
      exact (mul_eq_zero.mp hProd).resolve_left hThreeNe
    exact ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hEntryZero⟩

/--
修正版 right-end obligation から zero scaled state まで到達する。
-/
theorem exists_terminalNear_zero_scaledState_of_endSmallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedTerminalNearEndSmallnessObligation hStart)
    (m : ℕ)
    (hm : 0 < m)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      C.width - (2 * m + 2) ≤ i ∧
      i < j ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.ScaledState i j Delta := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_terminalNear_zero_scaledDifference_of_endSmallness
        hStart hSmall m hm hWidth with
    ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hZero⟩
  have hDelta := hBlock 0 (by omega)
  have hQ :=
    (C.scaledDifference_zero_eq_zero_iff
      (i := i) (j := j) (Delta := Delta)).1 hZero
  exact
    ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock,
      ⟨by simpa using hDelta, hQ⟩⟩

/--
修正版 right-end obligation でも従来と同じ pure Beatty zero-cycle equation まで到達する。
-/
theorem exists_terminalNear_zero_cycleEquation_of_endSmallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedTerminalNearEndSmallnessObligation hStart)
    (m : ℕ)
    (hm : 0 < m)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i p Delta : ℕ,
      C.width - (2 * m + 2) ≤ i ∧
      0 < p ∧
      i + p < C.width ∧
      ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) * C.qOne i =
        (2 : ℤ) ^ C.delta i *
          beattyCyclePhi (A.straightHenselStart + i) p := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_terminalNear_zero_scaledState_of_endSmallness
        hStart hSmall m hm hWidth with
    ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hState⟩
  let p := j - i
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hIp : i + p = j := by
    dsimp [p]
    omega
  have hjWidth : j < C.width := by
    dsimp [C, toFreeBaseMonotoneHenselChain]
    dsimp [toFreeBaseMonotoneHenselChain] at hjEnd
    omega
  have hEndA : i + p ≤ A.straightHenselWidth := by
    change i + p ≤ C.width
    rw [hIp]
    exact Nat.le_of_lt hjWidth
  have hStateP : C.ScaledState i (i + p) Delta := by
    rw [hIp]
    exact hState
  have hEq := A.zeroScaledState_cycleEquation hStart hEndA hStateP
  dsimp [C] at hEq
  refine ⟨i, p, Delta, hiNear, hp, ?_, ?_⟩
  · rw [hIp]
    exact hjWidth
  · exact hEq

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
