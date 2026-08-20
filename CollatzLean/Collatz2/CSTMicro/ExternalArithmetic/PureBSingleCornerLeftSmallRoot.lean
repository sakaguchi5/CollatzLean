import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerSmallRootReduction

/-!
# Pure B single-corner: left origin-critical small root

第2段。

single-corner の左側 `k<b` では profile depth が exact に zero なので checkpoint は
critical Beatty checkpoint に一致する。

actual representative `R_B` について左 critical prefix の整数 divisibility

  2^beta(r) | 3^r R_B + Psi(r),   r=b-1

が得られれば、それはそのまま `BoundaryXiCandidate` になり、既存
`smallXiCandidate_precision_le` を適用できる。

本ファイルはこの変換を完全に閉じる。したがって後に actual prefix arithmetic から
証明すべき obligation は上の divisibility 一個だけになる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- critical-prefix divisibility から finite Xi candidate を直接作る generic bridge。 -/
theorem boundaryXiCandidate_of_threePow_add_criticalPrefix_dvd
    {r x : ℕ}
    (hDiv :
      (2 : ℤ) ^ beattyIndex r ∣
        (3 : ℤ) ^ r * (x : ℤ) + criticalPrefixPhiZ r) :
    BoundaryXiCandidate (beattyIndex r) x := by
  have hCastEq :=
    PureBProfileObstruction.natCast_eq_criticalXi_of_threePow_add_phi_dvd hDiv
  refine ⟨r, rfl, ?_⟩
  have hVal := congrArg ZMod.val hCastEq
  simpa [ZMod.val_natCast] using hVal

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-- single-corner の left start は positive。 -/
theorem b_pos
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    0 < S.b := by
  have hcLe : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : S.b < P.m := lt_of_lt_of_le S.b_lt_c hcLe
  have hDepth := P.admissible.depth_le hbM
  rw [S.h_b_eq_one] at hDepth
  by_contra hnot
  have hb0 : S.b = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hb0, beattyIndex_zero] at hDepth
  omega

/-- `k<b` では depth は exact に zero。 -/
theorem left_depth_eq_zero
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k : ℕ}
    (hkb : k < S.b) :
    P.h k = 0 := by
  have hcLe : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k < P.m := by
    exact lt_trans hkb (lt_of_lt_of_le S.b_lt_c hcLe)
  exact S.depth_eq_zero_of_outside hkM (Or.inl hkb)

/-- `k<b` の checkpoint は critical Beatty checkpoint。 -/
theorem left_checkpoint_eq_beatty
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k : ℕ}
    (hkb : k < S.b) :
    profileCheckpoint P.h k = beattyIndex k := by
  unfold profileCheckpoint
  rw [S.left_depth_eq_zero hkb]
  omega

/-- left critical rank `r=b-1` は実際に `b` より小さい。 -/
theorem leftRank_lt_b
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    S.b - 1 < S.b := by
  have hb := S.b_pos
  omega

/-- `r=b-1` の checkpoint は exact critical position `beta(r)`。 -/
theorem leftRank_checkpoint_eq_beatty
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    profileCheckpoint P.h (S.b - 1) = beattyIndex (S.b - 1) := by
  exact S.left_checkpoint_eq_beatty S.leftRank_lt_b

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

namespace MinimalActualABObstructionPacket

/--
left prefix divisibility があれば actual representative は high-precision Xi candidate。
既存 López--Stoll / Christoffel height bound まで一気に通す。
-/
theorem singleCorner_leftPrecision_le_of_divisibility
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hDiv :
      (2 : ℤ) ^ beattyIndex (S.b - 1) ∣
        (3 : ℤ) ^ (S.b - 1) *
            (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
          criticalPrefixPhiZ (S.b - 1)) :
    beattyIndex (S.b - 1) ≤
      smallXiPrecisionBound (20 + 15 * ell) := by
  have hCandidate :
      BoundaryXiCandidate
        (beattyIndex (S.b - 1))
        M.actual.firstFailureEdge.step.edge.upperR :=
    boundaryXiCandidate_of_threePow_add_criticalPrefix_dvd hDiv
  have hxSize :
      M.actual.firstFailureEdge.step.edge.upperR + 1 ≤
        2 ^ (20 + 15 * ell) :=
    M.actualRepresentative_succ_le_dyadic R hL hmSize
  exact smallXiCandidate_precision_le R hxSize hCandidate

/--
left precision が既存 small-Xi bound を越えるなら、critical-prefix divisibility 自体が不可能。
この形が large-left branch の contradiction port。
-/
theorem singleCorner_leftDivisibility_impossible_of_largePrecision
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hLarge :
      smallXiPrecisionBound (20 + 15 * ell) <
        beattyIndex (S.b - 1)) :
    ¬ ((2 : ℤ) ^ beattyIndex (S.b - 1) ∣
        (3 : ℤ) ^ (S.b - 1) *
            (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
          criticalPrefixPhiZ (S.b - 1)) := by
  intro hDiv
  have hLe :=
    M.singleCorner_leftPrecision_le_of_divisibility
      R hL S hmSize hDiv
  omega

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
