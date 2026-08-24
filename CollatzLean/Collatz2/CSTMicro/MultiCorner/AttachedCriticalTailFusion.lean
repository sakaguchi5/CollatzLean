import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselFactorRepeat
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBIntegralCriticalTail


/-!
# Attached critical-tail / Hensel fusion

attached straight suffix には二種類の canonical state がある。

* `integralCriticalTailStateInt`: critical Beatty recurrence を terminal `m` から戻す state
* `qOne = q + 1`: carry-normalized closed tail から得る Hensel state

straight part では checkpoint gap が exact に `1` なので、この二つを

  S = 2^h Z + Q

と合成すると forcing が完全に消え、

  3 S_i = 2 S_(i+1)

という homogeneous transport になる。

このファイルはその exact fusion を actual attached packet 上で固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- critical state `Z` と shifted Hensel state `Q=q+1` の fused value。 -/
def attachedCriticalFusedValue
    (h : ℕ)
    (Z Q : ℤ) : ℤ :=
  (2 : ℤ) ^ h * Z + Q

/--
一段の critical recurrence と straight Hensel recurrence が同じ Beatty/checkpoint
exponent relation を持てば fused value は exact に `3/2` transport する。
-/
theorem attachedCriticalFusedValue_step
    {h hNext betaGap : ℕ}
    {Z ZNext Q QNext : ℤ}
    (hCritical :
      (2 : ℤ) ^ betaGap * ZNext = 3 * Z + 1)
    (hHensel :
      3 * Q = 2 * QNext + (2 : ℤ) ^ h)
    (hExponent :
      h + betaGap = 1 + hNext) :
    3 * attachedCriticalFusedValue h Z Q =
      2 * attachedCriticalFusedValue hNext ZNext QNext := by
  have hCritical' :
      3 * Z = (2 : ℤ) ^ betaGap * ZNext - 1 := by
    linarith
  have hPow :
      (2 : ℤ) ^ h * (2 : ℤ) ^ betaGap =
        2 * (2 : ℤ) ^ hNext := by
    rw [← pow_add, hExponent]
    rw [Nat.add_comm 1 hNext, pow_succ]
    ring
  unfold attachedCriticalFusedValue
  calc
    3 * ((2 : ℤ) ^ h * Z + Q)
        = (2 : ℤ) ^ h * (3 * Z) + 3 * Q := by ring
    _ =
        (2 : ℤ) ^ h *
            ((2 : ℤ) ^ betaGap * ZNext - 1) +
          (2 * QNext + (2 : ℤ) ^ h) := by
            rw [hCritical', hHensel]
    _ =
        ((2 : ℤ) ^ h * (2 : ℤ) ^ betaGap) * ZNext +
          2 * QNext := by ring
    _ =
        (2 * (2 : ℤ) ^ hNext) * ZNext + 2 * QNext := by
          rw [hPow]
    _ = 2 * ((2 : ℤ) ^ hNext * ZNext + QNext) := by ring

namespace AttachedTwoCornerPacket

/--
actual attached straight suffix 上の fused transport。

`i+1 < width` として terminal endpoint の `delta_width = 0` は使わず、
両側が positive straight corridor にある一段だけを扱う。
-/
theorem straight_criticalFusedValue_transport
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hiNext : i + 1 < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let I := P.criticalizationStart_spec
    let k := A.straightHenselStart + i
    let Z :=
      P.integralCriticalTailStateInt
        I k
        (by
          have hCrit := A.criticalization_le_previous
          dsimp [k]
          unfold straightHenselStart
          omega)
        (by
          have hEnd := A.straightHenselStart_add_width
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [k]
          omega)
    let ZNext :=
      P.integralCriticalTailStateInt
        I (k + 1)
        (by
          have hCrit := A.criticalization_le_previous
          dsimp [k]
          unfold straightHenselStart
          omega)
        (by
          have hEnd := A.straightHenselStart_add_width
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [k]
          omega)
    3 * attachedCriticalFusedValue (C.delta i) Z (C.qOne i) =
      2 * attachedCriticalFusedValue
        (C.delta (i + 1)) ZNext (C.qOne (i + 1)) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let I := P.criticalizationStart_spec
  let k := A.straightHenselStart + i
  have hi : i < A.straightHenselWidth := by
    omega
  have hkCrit :
      P.criticalizationStart ≤ k := by
    dsimp [k]
    have hCrit := A.criticalization_le_previous
    unfold straightHenselStart
    omega
  have hkLtM :
      k < P.m := by
    dsimp [k]
    have hEnd := A.straightHenselStart_add_width
    have hcM := P.terminalCriticalStart_spec.1
    omega
  have hCritical :=
    P.integralCriticalTailStateInt_step
      I hkCrit hkLtM
  have hHensel :=
    C.qOne_recurrence (i := i) hi
  have hRelative :=
    A.straightHenselDelta_relative_exact
      hStart hi hiNext
  have hExponent :
      C.delta i +
          (beattyIndex (k + 1) - beattyIndex k) =
        1 + C.delta (i + 1) := by
    dsimp [C, k] at hRelative ⊢
    have hIdx :
        A.straightHenselStart + i + 1 =
          A.straightHenselStart + (i + 1) := by
      omega
    rw [hIdx] at hRelative ⊢
    omega
  have hHensel' :
      3 * C.qOne i =
        2 * C.qOne (i + 1) +
          (2 : ℤ) ^ C.delta i := by
    simpa using hHensel
  /-
  Z / ZNext はここで展開しない。
  ゴール中の actual integral states をそのまま
  attachedCriticalFusedValue_step に推論させる。
  -/
  apply attachedCriticalFusedValue_step
    (betaGap :=
      beattyIndex (k + 1) - beattyIndex k)
  · /-
    integralCriticalTailStateInt の proof arguments は
    Prop の証明なので、同じ bound に揃えば proof irrelevance で消える。
    straightHenselStart 自体は展開しない。
    -/
    simpa [k] using hCritical
  · simpa [C] using hHensel'
  · simpa [C, k] using hExponent

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
