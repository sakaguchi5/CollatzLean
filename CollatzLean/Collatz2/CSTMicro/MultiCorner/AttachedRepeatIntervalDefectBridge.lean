import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCriticalTailFusion
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyCycleIntervalBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselZeroCycleBridge


/-!
# Attached repeat difference -> critical interval defect

attached straight suffix の二点 `i<j` に対して

  p = j-i,
  M_0 = Q_j - 2^Delta Q_i

と置く。`Q` の exact finite expansion と Beatty-cycle/interval bridge から

  2^p M_0
    = (3^p - 2^(p+Delta)) Q_i
      - 2^(delta_i) Phi[a,b]

を得る。

さらに parallel depth relation

  delta_j = delta_i + Delta

を使うと interval gap は

  Gamma[a,b] = 2^(p+Delta) - 3^p

なので、任意の integer `y` について

  2^p M_0
    = -2^(delta_i) F[a,b](y)
      - Gamma[a,b] * (Q_i + 2^(delta_i) y)

となる。

`y` に integral critical state を代入すれば、最後の括弧は
`AttachedCriticalTailFusion` の fused value そのものである。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/-- repeat start 二点の entrance difference を interval numerator へ exact に展開する。 -/
theorem scaledDifference_zero_eq_intervalPhi
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    (2 : ℤ) ^ p * C.scaledDifference i j Delta 0 =
      ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) * C.qOne i -
        (2 : ℤ) ^ C.delta i *
          criticalIntervalPhiZ
            (A.straightHenselStart + i)
            (A.straightHenselStart + j) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  have hIp : i + p = j := by
    dsimp [p]
    omega
  have hEndC : i + p ≤ C.width := by
    rw [hIp]
    change j ≤ A.straightHenselWidth
    exact Nat.le_of_lt hj
  have hEndA : i + p ≤ A.straightHenselWidth := by
    change i + p ≤ C.width
    exact hEndC
  have hIter := C.qOne_iterate hEndC
  have hNum := A.qOneBlockNumerator_eq_pow_mul_beattyCyclePhi hStart hEndA
  dsimp [C] at hNum
  rw [hNum] at hIter
  have hCycle :=
    beattyCyclePhi_eq_criticalIntervalPhiZ
      (A.straightHenselStart + i) p
  have hRight :
      A.straightHenselStart + i + p =
        A.straightHenselStart + j := by
    simpa [Nat.add_assoc] using
      congrArg
        (fun n : ℕ => A.straightHenselStart + n)
        hIp
  rw [hRight] at hCycle
  rw [hCycle] at hIter
  rw [hIp] at hIter
  unfold FreeBaseMonotoneHenselChain.scaledDifference
  simp only [Nat.add_zero]
  rw [pow_add]
  ring_nf at hIter ⊢
  linarith

/-- parallel depth relation から interval gap を repeat power gap に同定する。 -/
theorem criticalIntervalGapZ_eq_repeatGap
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let p := j - i
    criticalIntervalGapZ
        (A.straightHenselStart + i)
        (A.straightHenselStart + j) =
      (2 : ℤ) ^ (p + Delta) - (3 : ℤ) ^ p := by
  dsimp at hDelta ⊢
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  have hIp : i + p = j := by
    dsimp [p]
    omega
  have hi : i < A.straightHenselWidth := by omega
  have hj' : i + p < A.straightHenselWidth := by
    rw [hIp]
    exact hj
  have hRel :=
    A.straightHenselDelta_relative_exact
      hStart hi hj'
  have hRise :
      beattyIndex (A.straightHenselStart + j) -
          beattyIndex (A.straightHenselStart + i) =
        p + Delta := by
    have hDeltaP :
        C.delta (i + p) =
          C.delta i + Delta := by
      rw [hIp]
      exact hDelta
    dsimp at hRel
    change
      p + C.delta (i + p) =
        C.delta i +
          (beattyIndex (A.straightHenselStart + i + p) -
            beattyIndex (A.straightHenselStart + i))
      at hRel
    have hRiseP :
        beattyIndex (A.straightHenselStart + i + p) -
            beattyIndex (A.straightHenselStart + i) =
          p + Delta := by
      rw [hDeltaP] at hRel
      omega
    rw [← hIp]
    simpa [Nat.add_assoc] using hRiseP
  have hLen :
      (A.straightHenselStart + j) -
          (A.straightHenselStart + i) = p := by
    dsimp [p]
    omega
  unfold criticalIntervalGapZ
  rw [hRise, hLen]

/--
entrance difference を任意 base value `y` の critical interval defect と
fused linear termへ exact に書き換える。
-/
theorem scaledDifference_zero_eq_intervalDefect
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta)
    (y : ℤ) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    let b := A.straightHenselStart + j
    (2 : ℤ) ^ p * C.scaledDifference i j Delta 0 =
      -((2 : ℤ) ^ C.delta i) * criticalIntervalDefectZ a b y -
        criticalIntervalGapZ a b *
          (C.qOne i + (2 : ℤ) ^ C.delta i * y) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hPhi :=
    A.scaledDifference_zero_eq_intervalPhi
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
  have hGap :=
    A.criticalIntervalGapZ_eq_repeatGap
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [C, p, a, b] at hPhi hGap ⊢
  rw [hPhi]
  unfold criticalIntervalDefectZ
  rw [hGap]
  rw [pow_add]
  ring

/--
`y` に canonical integral critical state を代入した fused-state 版。
-/
theorem scaledDifference_zero_eq_integralDefect_fused
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    let b := A.straightHenselStart + j
    let I := P.criticalizationStart_spec
    let Z :=
      P.integralCriticalTailStateInt
        I a
        (by
          have hCrit := A.criticalization_le_previous
          dsimp [a]
          unfold straightHenselStart
          omega)
        (by
          have hEnd := A.straightHenselStart_add_width
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [a]
          omega)
    (2 : ℤ) ^ p * C.scaledDifference i j Delta 0 =
      -((2 : ℤ) ^ C.delta i) * criticalIntervalDefectZ a b Z -
        criticalIntervalGapZ a b *
          attachedCriticalFusedValue (C.delta i) Z (C.qOne i) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let a := A.straightHenselStart + i
  let I := P.criticalizationStart_spec
  have hi : i < A.straightHenselWidth := by omega
  have haCrit : P.criticalizationStart ≤ a := by
    dsimp [a]
    have hCrit := A.criticalization_le_previous
    unfold straightHenselStart
    omega
  have haLeM : a ≤ P.m := by
    dsimp [a]
    have hEnd := A.straightHenselStart_add_width
    have hcM := P.terminalCriticalStart_spec.1
    omega
  let Z := P.integralCriticalTailStateInt I a haCrit haLeM
  have h :=
    A.scaledDifference_zero_eq_intervalDefect
      hStart hij hj hDelta Z
  dsimp [C, a, I, Z] at h ⊢
  simpa [attachedCriticalFusedValue, add_comm, add_left_comm, add_assoc] using h

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
