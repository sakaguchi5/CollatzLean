import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedShiftedRepeatIntervalDefect
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.IntegralCriticalIntervalDefectStateDiff

/-!
# Attached shifted repeat: interval defect を state difference まで消去する

`AttachedShiftedRepeatIntervalDefect` は repeated block の右端 difference を

  2^p M_m = -2^delta * F[a,b](Z_a) - Gamma[a,b] * S_a

まで exact に落としている。

ここでは integral critical state に対する既存の

  F[a,b](Z_a) = 2^(beta(b)-beta(a)) * (Z_b - Z_a)

を差し込み、same-delta repeat が与える

  beta(b)-beta(a) = p + Delta,
  Gamma[a,b] = 2^(p+Delta) - 3^p

も同時に使う。結果として interval forcing は完全に消え、

  2^p M_m
    = (3^p - 2^(p+Delta)) S_a
      - 2^(p+delta+Delta) (Z_b-Z_a)

という二つの state の cancellation identity だけが残る。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
SameDeltaOffsetBlock の右端での depth relation。
repeat block の定義から `r = m` を取り出しただけの補題。
-/
private theorem sameDeltaOffsetBlock_end_delta_exact
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j m Delta : ℕ}
    (hBlock :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.SameDeltaOffsetBlock i j m Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    C.delta (j + m) = C.delta (i + m) + Delta := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  change C.SameDeltaOffsetBlock i j m Delta at hBlock
  change C.delta (j + m) = C.delta (i + m) + Delta
  have h := hBlock m le_rfl
  simpa [Nat.add_assoc] using h

/--
parallel depth relation と straight relative exactness から、
右端二点間の Beatty rise を exact に読む。

`jEnd` と `iEnd + p` を先に同一視してから arithmetic を行うため、
Beatty 値を別 atom として `omega` に渡さない。
-/
private theorem straight_end_beattyRise_eq_repeatRise
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {iEnd jEnd p Delta : ℕ}
    (hijEnd : iEnd < jEnd)
    (hjEnd : jEnd < A.straightHenselWidth)
    (hip : iEnd + p = jEnd)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta jEnd = C.delta iEnd + Delta) :
    beattyIndex (A.straightHenselStart + jEnd) -
        beattyIndex (A.straightHenselStart + iEnd) =
      p + Delta := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  have hiEnd :
      iEnd < A.straightHenselWidth := by
    omega
  have hipEnd :
      iEnd + p < A.straightHenselWidth := by
    rw [hip]
    exact hjEnd
  have hRel :=
    A.straightHenselDelta_relative_exact
      hStart
      (i := iEnd)
      (r := p)
      hiEnd
      hipEnd
  change
    C.delta jEnd = C.delta iEnd + Delta
    at hDelta
  dsimp at hRel
  change
    p + C.delta (iEnd + p) =
      C.delta iEnd +
        (beattyIndex (A.straightHenselStart + iEnd + p) -
          beattyIndex (A.straightHenselStart + iEnd))
    at hRel
  have hDeltaP :
      C.delta (iEnd + p) =
        C.delta iEnd + Delta := by
    rw [hip]
    exact hDelta
  have hRiseP :
      beattyIndex (A.straightHenselStart + iEnd + p) -
          beattyIndex (A.straightHenselStart + iEnd) =
        p + Delta := by
    rw [hDeltaP] at hRel
    omega
  simpa [Nat.add_assoc, hip] using hRiseP

/--
critical interval defect を、二端点の integral critical state 差へ exact に変換する。

`a + p = b` を dependent state の中へ `rw` せず、
`simp` に proof transport / proof irrelevance を処理させる。
-/
private theorem integralCriticalTail_intervalDefect_eq_repeatStateDifference
    (P : PureBProfileObstruction)
    {a b p Delta : ℕ}
    (I : IsIntegralCriticalTail P P.criticalizationStart)
    (haCrit : P.criticalizationStart ≤ a)
    (hbCrit : P.criticalizationStart ≤ b)
    (haM : a ≤ P.m)
    (hbM : b ≤ P.m)
    (hap : a + p = b)
    (hRise :
      beattyIndex b - beattyIndex a = p + Delta) :
    let Za :=
      P.integralCriticalTailStateInt I a haCrit haM
    let Zb :=
      P.integralCriticalTailStateInt I b hbCrit hbM
    criticalIntervalDefectZ a b Za =
      (2 : ℤ) ^ (p + Delta) * (Zb - Za) := by
  dsimp
  have hapM :
      a + p ≤ P.m := by
    rw [hap]
    exact hbM
  have hDefect :=
    P.integralCriticalTail_intervalDefect_eq_pow_mul_state_sub
      (a := P.criticalizationStart)
      (s := a)
      (r := p)
      I
      haCrit
      hapM
  simpa only [hap, hRise] using hDefect

/--
terminal-near repeated block の右端 scaled difference を、

fused state と integral critical state 差だけで表す exact cancellation identity。
-/
theorem scaledDifference_end_eq_integralStateDifference_fused
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j m Delta : ℕ}
    (hij : i < j)
    (hjEnd : j + m < A.straightHenselWidth)
    (hBlock :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.SameDeltaOffsetBlock i j m Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let iEnd := i + m
    let jEnd := j + m
    let p := jEnd - iEnd
    let a := A.straightHenselStart + iEnd
    let b := A.straightHenselStart + jEnd
    let I := P.criticalizationStart_spec
    let Za :=
      P.integralCriticalTailStateInt
        I a
        (by
          have hCrit := A.criticalization_le_previous
          dsimp [a, iEnd]
          unfold straightHenselStart
          omega)
        (by
          have hWidth := A.straightHenselStart_add_width
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [a, iEnd]
          omega)
    let Zb :=
      P.integralCriticalTailStateInt
        I b
        (by
          have hCrit := A.criticalization_le_previous
          dsimp [b, jEnd]
          unfold straightHenselStart
          omega)
        (by
          have hWidth := A.straightHenselStart_add_width
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [b, jEnd]
          omega)
    (2 : ℤ) ^ p * C.scaledDifference i j Delta m =
      ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) *
          attachedCriticalFusedValue
            (C.delta iEnd) Za (C.qOne iEnd) -
        (2 : ℤ) ^ (p + C.delta iEnd + Delta) * (Zb - Za) := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let iEnd := i + m
  let jEnd := j + m
  let p := jEnd - iEnd
  let a := A.straightHenselStart + iEnd
  let b := A.straightHenselStart + jEnd
  let I := P.criticalizationStart_spec
  have hijEnd :
      iEnd < jEnd := by
    dsimp [iEnd, jEnd]
    omega
  have hjEnd' :
      jEnd < A.straightHenselWidth := by
    simpa [jEnd] using hjEnd
  have hiEnd' :
      iEnd < A.straightHenselWidth := by
    omega
  have hip :
      iEnd + p = jEnd := by
    dsimp [p]
    omega
  /- repeat block の右端 depth relation。 -/
  have hDelta :
      C.delta jEnd =
        C.delta iEnd + Delta := by
    have h :=
      A.sameDeltaOffsetBlock_end_delta_exact
        hStart
        (i := i) (j := j)
        (m := m) (Delta := Delta)
        hBlock
    change
      C.delta (j + m) =
        C.delta (i + m) + Delta
      at h
    simpa [iEnd, jEnd] using h
  /- parallel depth relation から Beatty rise を読む。 -/
  have hRise :
      beattyIndex b - beattyIndex a =
        p + Delta := by
    have h :=
      A.straight_end_beattyRise_eq_repeatRise
        hStart
        (iEnd := iEnd)
        (jEnd := jEnd)
        (p := p)
        (Delta := Delta)
        hijEnd
        hjEnd'
        hip
        hDelta
    simpa [a, b] using h
  /- interval multiplicative gap。 -/
  have hGap :
      criticalIntervalGapZ a b =
        (2 : ℤ) ^ (p + Delta) - (3 : ℤ) ^ p := by
    have h :=
      A.criticalIntervalGapZ_eq_repeatGap
        hStart
        (i := iEnd)
        (j := jEnd)
        (Delta := Delta)
        hijEnd
        hjEnd'
        hDelta
    simpa [p, a, b] using h
  /- integral critical states の range certificates。 -/
  have haCrit :
      P.criticalizationStart ≤ a := by
    dsimp [a, iEnd]
    have hCrit := A.criticalization_le_previous
    unfold straightHenselStart
    omega
  have hbCrit :
      P.criticalizationStart ≤ b := by
    dsimp [b, jEnd]
    have hCrit := A.criticalization_le_previous
    unfold straightHenselStart
    omega
  have haM :
      a ≤ P.m := by
    dsimp [a, iEnd]
    have hWidth := A.straightHenselStart_add_width
    have hcM := P.terminalCriticalStart_spec.1
    omega
  have hbM :
      b ≤ P.m := by
    dsimp [b, jEnd]
    have hWidth := A.straightHenselStart_add_width
    have hcM := P.terminalCriticalStart_spec.1
    omega
  /-
  共通 prefix `straightHenselStart +` を hip に付ける。
  `rw [hip]` では `(start + iEnd) + p` に `iEnd + p`
  という部分式が存在しないので congrArg を使う。
  -/
  have hap :
      a + p = b := by
    dsimp [a, b]
    simpa [Nat.add_assoc] using
      congrArg
        (fun n : ℕ => A.straightHenselStart + n)
        hip
  let Za :=
    P.integralCriticalTailStateInt
      I a haCrit haM
  let Zb :=
    P.integralCriticalTailStateInt
      I b hbCrit hbM
  /- interval defect = scaled state difference。 -/
  have hDefect :
      criticalIntervalDefectZ a b Za =
        (2 : ℤ) ^ (p + Delta) * (Zb - Za) := by
    exact
      integralCriticalTail_intervalDefect_eq_repeatStateDifference
        P
        I
        haCrit
        hbCrit
        haM
        hbM
        hap
        hRise
  /- 既存 fused defect identity。 -/
  have hCore :=
    A.scaledDifference_end_eq_integralDefect_fused
      hStart
      (i := i)
      (j := j)
      (m := m)
      (Delta := Delta)
      hij
      hjEnd
      hBlock
  have hCore' :
      (2 : ℤ) ^ p * C.scaledDifference i j Delta m =
        -((2 : ℤ) ^ C.delta iEnd) *
            criticalIntervalDefectZ a b Za -
          criticalIntervalGapZ a b *
            attachedCriticalFusedValue
              (C.delta iEnd) Za (C.qOne iEnd) := by
    simpa [C, iEnd, jEnd, p, a, b, I, Za] using hCore
  /- 二つの 2-power を最終 exponent にまとめる。 -/
  have hPow :
      (2 : ℤ) ^ C.delta iEnd *
          (2 : ℤ) ^ (p + Delta) =
        (2 : ℤ) ^ (p + C.delta iEnd + Delta) := by
    rw [← pow_add]
    congr 1
    omega
  have hFinal :
      (2 : ℤ) ^ p * C.scaledDifference i j Delta m =
        ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) *
            attachedCriticalFusedValue
              (C.delta iEnd) Za (C.qOne iEnd) -
          (2 : ℤ) ^ (p + C.delta iEnd + Delta) *
            (Zb - Za) := by
    calc
      (2 : ℤ) ^ p * C.scaledDifference i j Delta m
          =
        -((2 : ℤ) ^ C.delta iEnd) *
            criticalIntervalDefectZ a b Za -
          criticalIntervalGapZ a b *
            attachedCriticalFusedValue
              (C.delta iEnd) Za (C.qOne iEnd) := hCore'
      _ =
        -((2 : ℤ) ^ C.delta iEnd) *
            ((2 : ℤ) ^ (p + Delta) * (Zb - Za)) -
          ((2 : ℤ) ^ (p + Delta) - (3 : ℤ) ^ p) *
            attachedCriticalFusedValue
              (C.delta iEnd) Za (C.qOne iEnd) := by
        rw [hDefect, hGap]
      _ =
        ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) *
            attachedCriticalFusedValue
              (C.delta iEnd) Za (C.qOne iEnd) -
          (2 : ℤ) ^ (p + C.delta iEnd + Delta) *
            (Zb - Za) := by
        rw [← hPow]
        ring
  simpa [C, iEnd, jEnd, p, a, b, I, Za, Zb] using hFinal

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
