import CollatzLean.Collatz3.CSTMicro.LiftClassification
import CollatzLean.Collatz3.CSTMicro.Capacity

/-!
# Collatz3 CSTMicro: path-wise CST criterion

一つの first coefficient crossing path `P` に対し、

  すべての exact realization が strict descent

であることを、最小 parity representative `R₀` と capacity の比較だけへ落とす。

  CSTHolds(P)
    ↔ B(P) < D(P) * R₀(P)
    ↔ capacity(P) < R₀(P)

旧 `MicroObject` のような realization witness field は使わない。
-/

namespace Collatz3
namespace CSTMicro
namespace FirstPassagePath

/-- この first-passage parity path 上で CST が成立する。 -/
def CSTHolds (P : FirstPassagePath) : Prop :=
  ∀ x y : ℕ,
    TraceRealizes P.word x y →
      y < x

/-- division-free separation criterion。 -/
def PureSeparation (P : FirstPassagePath) : Prop :=
  affineConst P.word <
    P.terminalGap * leastRepresentative P.word

/-- path-wise CST は最小 parity representative での pure separation と同値。 -/
theorem cstHolds_iff_pureSeparation
    (P : FirstPassagePath) :
    P.CSTHolds ↔ P.PureSeparation := by
  constructor
  · intro hCST
    unfold PureSeparation
    have hTrace := canonicalEndpoint_trace P.word
    have hDesc :
        canonicalEndpoint P.word < leastRepresentative P.word :=
      hCST _ _ hTrace
    have hNot : ¬ P.WithinCapacity (leastRepresentative P.word) := by
      intro hCap
      have hLe :
          leastRepresentative P.word ≤ canonicalEndpoint P.word :=
        (P.start_le_end_iff_withinCapacity_of_trace hTrace).2 hCap
      omega
    unfold WithinCapacity at hNot
    omega
  · intro hSep x y hTrace
    unfold PureSeparation at hSep
    have hRle : leastRepresentative P.word ≤ x :=
      hTrace.affine.leastRepresentative_le_start
    by_contra hNotDesc
    have hxy : x ≤ y := by omega
    have hCap : P.WithinCapacity x :=
      (P.start_le_end_iff_withinCapacity_of_trace hTrace).1 hxy
    unfold WithinCapacity at hCap
    have hMul :
        P.terminalGap * leastRepresentative P.word ≤
          P.terminalGap * x :=
      Nat.mul_le_mul_left P.terminalGap hRle
    omega

/-- pure separation は numerical capacity が最小代表より小さいことと同値。 -/
theorem pureSeparation_iff_capacity_lt_leastRepresentative
    (P : FirstPassagePath) :
    P.PureSeparation ↔
      P.capacity < leastRepresentative P.word := by
  unfold PureSeparation capacity
  have hD : 0 < P.terminalGap := P.terminalGap_pos
  constructor
  · intro h
    exact (Nat.div_lt_iff_lt_mul hD).2
      (by simpa [Nat.mul_comm] using h)
  · intro h
    have h' := (Nat.div_lt_iff_lt_mul hD).1 h
    simpa [Nat.mul_comm] using h'

/-- 最終形: path-wise CST は `R₀ > capacity` と exact に同値。 -/
theorem cstHolds_iff_leastRepresentative_gt_capacity
    (P : FirstPassagePath) :
    P.CSTHolds ↔
      leastRepresentative P.word > P.capacity := by
  rw [P.cstHolds_iff_pureSeparation]
  simpa only [gt_iff_lt] using
    P.pureSeparation_iff_capacity_lt_leastRepresentative

end FirstPassagePath
end CSTMicro
end Collatz3
