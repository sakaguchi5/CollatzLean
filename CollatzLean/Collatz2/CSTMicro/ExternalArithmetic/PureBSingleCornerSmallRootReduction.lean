import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleExposedCornerRigidity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalPolylog

/-!
# Pure B single-corner: small-root reduction

`|E(B)| = 1` branch の small-root route の第1段。

single-corner packet の幾何を

  m = b + n + s

へ整理する。ここで

* `b` : 左 critical prefix の odd 長さ,
* `n = c-b` : 唯一の noncritical straight interval の幅,
* `s = m-c` : terminal critical suffix の長さ。

actual minimal B については既存 Rhin bound から

  R_B <= 16384 * (m+1)^15

を取り出し、さらに dyadic size に変換する。

中央 straight interval から `n = O(log m)` を得る最後の actual block identity は
現時点の repo にはまだ独立 theorem として無い。そのため本ファイルでは、その identity
から得るべき dyadic seed

  2^(n-1) <= 8*n^14*2^ell

だけを hypothesis に隔離し、既存 `dyadic_poly14_forces_linear` へ接続する。
`sorry` は使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-- single-corner の noncritical interval width `n = c-b`。 -/
noncomputable def width
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) : ℕ :=
  P.terminalCriticalStart - S.b

/-- single-corner の terminal critical suffix length `s = m-c`。 -/
noncomputable def rightLength
    {P : PureBProfileObstruction}
    (_S : P.SingleExposedCornerRigidityPacket) : ℕ :=
  P.m - P.terminalCriticalStart

/-- `b+n=c`。 -/
theorem b_add_width_eq_terminalStart
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    S.b + S.width = P.terminalCriticalStart := by
  unfold width
  exact Nat.add_sub_of_le (Nat.le_of_lt S.b_lt_c)

/-- single-corner width は正。 -/
theorem width_pos
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    0 < S.width := by
  unfold width
  exact Nat.sub_pos_iff_lt.mpr S.b_lt_c

/-- `b+n+s=m`。 -/
theorem b_add_width_add_rightLength_eq_m
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    S.b + S.width + S.rightLength = P.m := by
  have hbLe :
      S.b ≤ P.terminalCriticalStart :=
    Nat.le_of_lt S.b_lt_c
  have hcLe :
      P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  unfold width rightLength
  rw [Nat.add_sub_of_le hbLe]
  exact Nat.add_sub_of_le hcLe

/-- right length は既存 canonical terminal critical length と同じ。 -/
theorem rightLength_eq_terminalCriticalLength
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    S.rightLength = P.terminalCriticalLength := by
  rfl

/--
中央幅 `n<=W` と右 suffix `s<=T` から、左 critical prefix の下界

  m-(W+T) <= b

を読む。
-/
theorem leftStart_lower_of_width_right_bounds
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {W T : ℕ}
    (hWidth : S.width ≤ W)
    (hRight : S.rightLength ≤ T) :
    P.m - (W + T) ≤ S.b := by
  have hDecomp := S.b_add_width_add_rightLength_eq_m
  omega

/--
中央 block の dyadic seed を既存 elementary estimate に渡す。
この theorem の hypothesis が、次に actual consecutive-odd block から埋める唯一の seed。
-/
theorem width_le_linear_of_dyadicSeed
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hSeed :
      2 ^ (S.width - 1) ≤
        8 * S.width ^ 14 * 2 ^ ell) :
    S.width ≤ 65536 * (ell + 1) := by
  exact dyadic_poly14_forces_linear hSeed

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

namespace MinimalActualABObstructionPacket

/--
actual minimal B の least representative に相当する `upperR` は pure witness `y=R+q`
以下なので、既存 Rhin polynomial bound をそのまま継承する。
-/
theorem actualRepresentative_le_rhinPolynomial
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    M.actual.firstFailureEdge.step.edge.upperR ≤
      rhinGapK *
        ((M.toPureBProfileObstruction hL).m + 1) ^ 15 := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hyCast : (P.yNat : ℤ) = P.y := P.yNat_cast hy
  have hyEq := M.toPureBProfileObstruction_y_eq_upperR_add_q hL
  have hRZ :
      (M.actual.firstFailureEdge.step.edge.upperR : ℤ) ≤ P.y := by
    rw [hyEq]
    exact le_add_of_nonneg_right (by positivity)
  rw [← hyCast] at hRZ
  have hRNat :
      M.actual.firstFailureEdge.step.edge.upperR ≤ P.yNat := by
    exact_mod_cast hRZ
  have hyPoly :
      P.yNat ≤ rhinGapK * (P.m + 1) ^ 15 :=
    P.yNat_le_rhinPolynomial R hy
  simpa [P] using le_trans hRNat hyPoly

/--
`m+1 <= 2^ell` なら actual representative 自身も polynomial-size から
uniform dyadic size `2^(20+15*ell)` 以下へ入る。
-/
theorem actualRepresentative_succ_le_dyadic
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    M.actual.firstFailureEdge.step.edge.upperR + 1 ≤
      2 ^ (20 + 15 * ell) := by
  let P := M.toPureBProfileObstruction hL
  have hR := M.actualRepresentative_le_rhinPolynomial R hL
  have hPow :
      (P.m + 1) ^ 15 ≤ (2 ^ ell) ^ 15 := by
    apply Nat.pow_le_pow_left
    simpa [P] using hmSize
  have hCore :
      M.actual.firstFailureEdge.step.edge.upperR ≤
        rhinGapK * (2 ^ ell) ^ 15 := by
    calc
      M.actual.firstFailureEdge.step.edge.upperR
          ≤ rhinGapK * (P.m + 1) ^ 15 := by simpa [P] using hR
      _ ≤ rhinGapK * (2 ^ ell) ^ 15 :=
        Nat.mul_le_mul_left rhinGapK hPow
  have hPowerEq :
      rhinGapK * (2 ^ ell) ^ 15 =
        2 ^ (14 + 15 * ell) := by
    unfold rhinGapK
    rw [← pow_mul]
    have hMul : ell * 15 = 15 * ell := by omega
    rw [hMul, pow_add]
    ring
  rw [hPowerEq] at hCore
  have hPos : 0 < 2 ^ (14 + 15 * ell) := by positivity
  have hSucc :
      M.actual.firstFailureEdge.step.edge.upperR + 1 ≤
        2 * 2 ^ (14 + 15 * ell) := by
    omega
  calc
    M.actual.firstFailureEdge.step.edge.upperR + 1
        ≤ 2 * 2 ^ (14 + 15 * ell) := hSucc
    _ = 2 ^ (15 + 15 * ell) := by
      have hExp : 15 + 15 * ell = (14 + 15 * ell) + 1 := by omega
      rw [hExp, pow_succ]
      ring
    _ ≤ 2 ^ (20 + 15 * ell) :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)

/--
`|E|=1` packet の右側は既存 terminal-small-root theorem により既に polylog。
-/
theorem singleCorner_rightLength_le_log210
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) :
    S.rightLength ≤
      terminalCriticalSuffixPolylogConstant *
        (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 210 := by
  have h := M.terminalCriticalLength_le_log210 R hL
  simpa [
    PureBProfileObstruction.SingleExposedCornerRigidityPacket.rightLength,
    PureBProfileObstruction.terminalCriticalLength
  ] using h

/--
中央 dyadic seed が得られれば、右 polylog bound と合わせて左 critical prefix `b` は
explicit に長くなる。
-/
theorem singleCorner_leftStart_lower_of_dyadicSeed
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hSeed :
      2 ^ (S.width - 1) ≤
        8 * S.width ^ 14 * 2 ^ ell) :
    (M.toPureBProfileObstruction hL).m -
        (65536 * (ell + 1) +
          terminalCriticalSuffixPolylogConstant *
            (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 210) ≤
      S.b := by
  have hWidth : S.width ≤ 65536 * (ell + 1) :=
    S.width_le_linear_of_dyadicSeed hSeed
  have hRight := M.singleCorner_rightLength_le_log210 R hL S
  exact S.leftStart_lower_of_width_right_bounds hWidth hRight

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
