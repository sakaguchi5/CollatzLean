import CollatzLean.Collatz3.CSTMicro.RecordShapeEnvelope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTMicro Stage 7C: RecordFerrers survivor corridor

Stage 6 の odd-endpoint nondecreasing survivor は canonical `R,Y,Q` に一致し、`Q ≥ 0`。
Stage 7B では RecordFerrers canonical partition の形だけから `B ≤ B_shape` を得た。

ここでは両者を組み合わせ、

* `D * R ≤ B_shape`,
* `2^H * Q ≤ B_shape`,
* `D | (B - 2^H Q)`,

を得る。

最後の式は mod-`D` residue condition の division-free exact form である。
-/

namespace Collatz3
namespace CSTMicro
namespace FirstPassagePath

/-- terminal gap を整数へ cast すると signed scale gap `2^H - 3^p`。 -/
theorem terminalGap_cast_eq_signedScaleGap
    (P : FirstPassagePath) :
    (P.terminalGap : ℤ) =
      (2 : ℤ) ^ P.length - (3 : ℤ) ^ P.endpointOddCount := by
  have h := P.twoPow_eq_threePow_add_terminalGap
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hZ
  linarith

/--
Stage 6 の REQ identity を `D` で整理した exact residue equality。

  B - 2^H Q = D R
-/
theorem affineConst_sub_twoPow_gap_eq_terminalGap_mul_start
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    (affineConst P.word : ℤ) -
        (2 : ℤ) ^ P.length *
          Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) =
      (P.terminalGap : ℤ) *
        (Critical.profileCanonicalStart
          (P.endpointIndexedCriticalProfile hp) : ℤ) := by
  have h :=
    P.endpointIndexedProfile_affineConst_eq_gap_start_add_twoPow_gap hp
  have hD := P.terminalGap_cast_eq_signedScaleGap
  rw [← hD] at h
  linarith

/--
mod-`D` residue condition の divisibility form。

  D | (B - 2^H Q)
-/
theorem terminalGap_dvd_affineConst_sub_twoPow_gap
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    (P.terminalGap : ℤ) ∣
      (affineConst P.word : ℤ) -
        (2 : ℤ) ^ P.length *
          Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) := by
  refine ⟨
    (Critical.profileCanonicalStart
      (P.endpointIndexedCriticalProfile hp) : ℤ), ?_⟩
  exact P.affineConst_sub_twoPow_gap_eq_terminalGap_mul_start hp

/--
RecordFerrers survivor の canonical start は shape-sensitive start bound 以下。
-/
theorem endpointIndexedCanonicalStart_le_recordShapeStartBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    (hSingle : P.SingleLiftGapCondition)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    Critical.profileCanonicalStart (P.endpointIndexedCriticalProfile hp) ≤
      P.recordShapeStartBound hp hRecord := by
  have hStart :=
    P.start_le_recordShapeStartBound_of_nondecreasing_trace
      hp hRecord h hxy
  have hCanonical :=
    P.nondecreasing_oddEndpoint_eq_endpointIndexedProfileCanonical
      hp hSingle h hxy hy
  rw [hCanonical.1] at hStart
  exact hStart

/--
RecordFerrers survivor では canonical drift の scaled size も shape roof 以下。

  2^H Q ≤ B_shape

`Q` は整数のまま保持するので、符号情報を失わない。
-/
theorem twoPow_mul_endpointIndexedCanonicalGap_le_recordShapeAffineBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    (hSingle : P.SingleLiftGapCondition)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    (2 : ℤ) ^ P.length *
        Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) ≤
      (P.recordShapeAffineBound hp hRecord : ℤ) := by
  have hCanonical :=
    P.nondecreasing_oddEndpoint_eq_endpointIndexedProfileCanonical
      hp hSingle h hxy hy
  have hQ :
      0 ≤ Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) :=
    hCanonical.2.2
  have hReq :=
    P.affineConst_sub_twoPow_gap_eq_terminalGap_mul_start hp
  have hDR :
      0 ≤
        (P.terminalGap : ℤ) *
          (Critical.profileCanonicalStart
            (P.endpointIndexedCriticalProfile hp) : ℤ) := by
    positivity
  have hTwoQleB :
      (2 : ℤ) ^ P.length *
          Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) ≤
        (affineConst P.word : ℤ) := by
    linarith
  have hBshapeNat := P.affineConst_le_recordShapeAffineBound hp hRecord
  have hBshape :
      (affineConst P.word : ℤ) ≤
        (P.recordShapeAffineBound hp hRecord : ℤ) := by
    exact_mod_cast hBshapeNat
  exact le_trans hTwoQleB hBshape

/-- `Q ≥ 0` を natural size に戻した shape-sensitive gap bound。 -/
def recordShapeGapBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) : ℕ :=
  P.recordShapeAffineBound hp hRecord / 2 ^ P.length

/--
nonnegative canonical `Q` の natural size は `B_shape / 2^H` 以下。
-/
theorem endpointIndexedCanonicalGap_toNat_le_recordShapeGapBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    (hSingle : P.SingleLiftGapCondition)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    Int.toNat
        (Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp)) ≤
      P.recordShapeGapBound hp hRecord := by
  have hCanonical :=
    P.nondecreasing_oddEndpoint_eq_endpointIndexedProfileCanonical
      hp hSingle h hxy hy
  have hQ :
      0 ≤ Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) :=
    hCanonical.2.2
  have hScaled :=
    P.twoPow_mul_endpointIndexedCanonicalGap_le_recordShapeAffineBound
      hp hRecord hSingle h hxy hy
  have hQcast :
      ((Int.toNat
        (Critical.profileCanonicalGap
          (P.endpointIndexedCriticalProfile hp)) : ℕ) : ℤ) =
        Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) := by
    exact Int.toNat_of_nonneg hQ
  rw [← hQcast] at hScaled
  have hScaledNat :
      2 ^ P.length *
          Int.toNat
            (Critical.profileCanonicalGap
              (P.endpointIndexedCriticalProfile hp)) ≤
        P.recordShapeAffineBound hp hRecord := by
    exact_mod_cast hScaled
  unfold recordShapeGapBound
  apply (Nat.le_div_iff_mul_le (Arithmetic.twoPow_pos P.length)).2
  simpa [Nat.mul_comm] using hScaledNat

/--
Stage 4 の universal gap interface を使った RecordFerrers survivor corridor のまとめ。
-/
theorem recordSurvivorCorridor_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    (hGap : Arithmetic.CriticalGapLinearBound)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    Critical.profileCanonicalStart (P.endpointIndexedCriticalProfile hp) ≤
        P.recordShapeStartBound hp hRecord ∧
      0 ≤ Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) ∧
      Int.toNat
          (Critical.profileCanonicalGap
            (P.endpointIndexedCriticalProfile hp)) ≤
        P.recordShapeGapBound hp hRecord := by
  have hSingle :=
    P.singleLiftGapCondition_of_criticalGapLinearBound hGap
  refine ⟨
    P.endpointIndexedCanonicalStart_le_recordShapeStartBound
      hp hRecord hSingle h hxy hy,
    ?_,
    P.endpointIndexedCanonicalGap_toNat_le_recordShapeGapBound
      hp hRecord hSingle h hxy hy
  ⟩
  exact
    (P.nondecreasing_oddEndpoint_eq_endpointIndexedProfileCanonical
      hp hSingle h hxy hy).2.2

end FirstPassagePath
end CSTMicro
end Collatz3
