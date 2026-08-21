import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerCriticalizationRun

/-!
# Pure B single-corner: left start is terminal-localized to degree 14

前ファイルで

  criticalizationStart - b <= 18 + 15*ell

を得た。一方 square-window theorem は

  m - criticalizationStart
    <= terminalSquareLog14Constant W * (ell+1)^14

を与える。

両者を足すことで、`a<=b / b<a` を分岐せず

  m-b <= C14*(ell+1)^14 + 18 + 15*ell

を得る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/-- single-corner left start `b` までの terminal distance の dyadic degree-14 bound。 -/
theorem singleCorner_m_sub_b_le_dyadicLog14
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    (M.toPureBProfileObstruction hL).m - S.b ≤
      terminalSquareLog14Constant W * (ell + 1) ^ 14 +
        (18 + 15 * ell) := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hStartPos : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  have hTail :=
    P.criticalizationTail_le_dyadicSquareLog14
      W R hy hStartPos
      (by simpa [P] using hmSize)
  have hLeft :=
    M.singleCorner_criticalizationStart_sub_b_le_dyadic15
      R hL S hmSize
  have hStartLe : P.criticalizationStart ≤ P.m :=
    P.criticalizationStart_spec.1
  dsimp [P] at hTail hLeft hStartLe ⊢
  omega

/-- Nat-log form。 -/
theorem singleCorner_m_sub_b_le_log14
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) :
    (M.toPureBProfileObstruction hL).m - S.b ≤
      terminalSquareLog14Constant W *
          (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 14 +
        (33 + 15 * Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1)) := by
  let P := M.toPureBProfileObstruction hL
  let ell := Nat.log 2 (P.m + 1) + 1
  have hmLt :
      P.m + 1 < 2 ^ (Nat.log 2 (P.m + 1) + 1) := by
    simpa using
      Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (P.m + 1)
  have hmSize : P.m + 1 ≤ 2 ^ ell := by
    dsimp [ell]
    exact Nat.le_of_lt hmLt
  have h :=
    M.singleCorner_m_sub_b_le_dyadicLog14 W R hL S
      (by simpa [P] using hmSize)
  dsimp [ell, P] at h ⊢
  have hLinear :
      18 + 15 * (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 1) =
        33 + 15 * Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) := by
    ring
  simpa [Nat.add_assoc, hLinear] using h

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
