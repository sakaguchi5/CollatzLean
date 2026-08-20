import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerTopLayerWidth
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ProfileIntervalCostBlocks
import Mathlib.Data.ZMod.Basic

/-!
# Pure B single-corner: consecutive top-cell residue congruence

同じ layer `j` の consecutive columns `k,k+1` で Beatty gap が 1 なら、
canonical power terms は

  3 M₂ = 2 M₁

を満たす。

pure canonical cell cost の exact law

  3^m C = G Q + M

を modulo `G` で比較し、`gcd(3,G)=1` を使って `3^m` を cancel すると

  3 C₂ = 2 C₁  (mod G)

を得る。`D = G-C` なので最終的に

  3 D₂ = 2 D₁  (mod G)

となる。

最後に top layer の幅が 2 の場合へ specialization する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- terminal gap `2^H-3^m` は `m>0` なら 3 と互いに素。 -/
theorem three_coprime_columnLayerGap
    {H m : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hm : 0 < m) :
    Nat.Coprime 3 (columnLayerGap H m) := by
  let G := columnLayerGap H m
  have hPow : 3 ^ m < 2 ^ H := by
    dsimp [G, columnLayerGap] at hGap
    exact Nat.sub_pos_iff_lt.mp hGap
  have hHPos : 0 < H := by
    by_contra hnot
    have hHzero : H = 0 := by omega
    rw [hHzero] at hPow
    simp at hPow
  have hGapAdd : G + 3 ^ m = 2 ^ H := by
    dsimp [G, columnLayerGap]
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  apply (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr
  intro hThreeDvdGap
  have hThreeDvdPow : 3 ∣ 3 ^ m :=
    dvd_pow_self 3 (Nat.ne_of_gt hm)
  have hThreeDvdSum : 3 ∣ G + 3 ^ m :=
    Nat.dvd_add hThreeDvdGap hThreeDvdPow
  rw [hGapAdd] at hThreeDvdSum
  have hThreeDvdTwo : 3 ∣ 2 :=
    (show Nat.Prime 3 by decide).dvd_of_dvd_pow hThreeDvdSum
  norm_num at hThreeDvdTwo

/--
consecutive same-layer cells で Beatty gap が 1 なら scaled power term は `3:2` 比。
-/
theorem three_mul_profileDyadicCellTerm_succ_eq_two_mul
    {m k j : ℕ}
    (hk : k + 1 < m)
    (hj : j < beattyIndex k)
    (hBeatty : beattyIndex (k + 1) = beattyIndex k + 1) :
    3 * profileDyadicCellTerm m (k + 1) j =
      2 * profileDyadicCellTerm m k j := by
  have hTwoExp :
      beattyIndex (k + 1) - j - 1 =
        (beattyIndex k - j - 1) + 1 := by
    omega
  have hThreeExp :
      m - (k + 1) =
        (m - ((k + 1) + 1)) + 1 := by
    omega
  unfold profileDyadicCellTerm
  rw [hTwoExp, hThreeExp]
  rw [pow_succ, pow_succ]
  ring

/--
consecutive same-layer canonical Farey residues の desired modular relation。
`D₁ = columnLayerFareyResidue H m k j`, `D₂ = ... (k+1) j`。
-/
theorem consecutive_columnLayerFareyResidue_mod
    {H m k j : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1)
    (hk : k + 1 < m)
    (hj : j < beattyIndex k)
    (hBeatty : beattyIndex (k + 1) = beattyIndex k + 1) :
    (3 : ZMod (columnLayerGap H m)) *
        (columnLayerFareyResidue H m (k + 1) j :
          ZMod (columnLayerGap H m)) =
      (2 : ZMod (columnLayerGap H m)) *
        (columnLayerFareyResidue H m k j :
          ZMod (columnLayerGap H m)) := by
  let G := columnLayerGap H m
  let C₁ := profileSignedCellCost H m k j
  let C₂ := profileSignedCellCost H m (k + 1) j
  have hmPos : 0 < m := by omega
  have hcop : Nat.Coprime 3 G := by
    simpa [G] using three_coprime_columnLayerGap hGap hmPos
  have hj₂ : j < beattyIndex (k + 1) := by
    rw [hBeatty]
    omega
  have hCost₁ :=
    threePow_mul_profileSignedCellCost_eq_gap_mul_quotient_add_term
      hGap hTerminal (by omega : k < m) hj
  have hCost₂ :=
    threePow_mul_profileSignedCellCost_eq_gap_mul_quotient_add_term
      hGap hTerminal hk hj₂
  have hCost₁Z :=
    congrArg (fun z : ℤ => (z : ZMod G)) hCost₁
  have hCost₂Z :=
    congrArg (fun z : ℤ => (z : ZMod G)) hCost₂
  have hGZero : ((G : ℤ) : ZMod G) = 0 := by
    simp
  push_cast at hCost₁Z hCost₂Z
  have hCost₁ZG :
      (3 : ZMod G) ^ m * (C₁ : ZMod G) =
        (G : ZMod G) *
            (profileCellScaledQuotient H m k j : ZMod G) +
          (profileDyadicCellTerm m k j : ZMod G) := by
    simpa [G, C₁] using hCost₁Z
  have hCost₂ZG :
      (3 : ZMod G) ^ m * (C₂ : ZMod G) =
        (G : ZMod G) *
            (profileCellScaledQuotient H m (k + 1) j : ZMod G) +
          (profileDyadicCellTerm m (k + 1) j : ZMod G) := by
    simpa [G, C₂] using hCost₂Z
  have hGZero :
      (G : ZMod G) = 0 := by
    simp
  rw [hGZero, zero_mul, zero_add] at hCost₁ZG hCost₂ZG
  have hTermNat :=
    three_mul_profileDyadicCellTerm_succ_eq_two_mul
      hk hj hBeatty
  have hTermZ :=
    congrArg
      (fun n : ℕ => (n : ZMod G))
      hTermNat
  push_cast at hTermZ
  have hScaled :
      (3 : ZMod G) ^ m *
          ((3 : ZMod G) * (C₂ : ZMod G)) =
        (3 : ZMod G) ^ m *
          ((2 : ZMod G) * (C₁ : ZMod G)) := by
    calc
      (3 : ZMod G) ^ m *
          ((3 : ZMod G) * (C₂ : ZMod G))
          =
        (3 : ZMod G) *
          ((3 : ZMod G) ^ m * (C₂ : ZMod G)) := by ring
      _ =
        (3 : ZMod G) *
          (profileDyadicCellTerm m (k + 1) j : ZMod G) := by
            simpa [C₂, G] using congrArg (fun z => (3 : ZMod G) * z) hCost₂Z
      _ =
        (2 : ZMod G) *
          (profileDyadicCellTerm m k j : ZMod G) := by
            exact hTermZ
      _ =
        (2 : ZMod G) *
          ((3 : ZMod G) ^ m * (C₁ : ZMod G)) := by
            simpa [C₁, G] using
              (congrArg (fun z => (2 : ZMod G) * z) hCost₁Z).symm
      _ =
        (3 : ZMod G) ^ m *
          ((2 : ZMod G) * (C₁ : ZMod G)) := by ring
  let U : (ZMod G)ˣ :=
    (ZMod.unitOfCoprime 3 hcop) ^ m
  have hU :
      (↑U : ZMod G) = (3 : ZMod G) ^ m := by
    dsimp [U]
  have hScaledU :
      (↑U : ZMod G) *
          ((3 : ZMod G) * (C₂ : ZMod G)) =
        (↑U : ZMod G) *
          ((2 : ZMod G) * (C₁ : ZMod G)) := by
    simpa [hU] using hScaled
  have hCancel := congrArg
    (fun z : ZMod G => (↑(U⁻¹) : ZMod G) * z)
    hScaledU
  have hCostRelation :
      (3 : ZMod G) * (C₂ : ZMod G) =
        (2 : ZMod G) * (C₁ : ZMod G) := by
    simpa [← mul_assoc] using hCancel
  have hD₁ :
      (columnLayerFareyResidue H m k j : ZMod G) =
        -(C₁ : ZMod G) := by
    dsimp [C₁]
    unfold profileSignedCellCost
    simp [G]
  have hD₂ :
      (columnLayerFareyResidue H m (k + 1) j : ZMod G) =
        -(C₂ : ZMod G) := by
    dsimp [C₂]
    unfold profileSignedCellCost
    simp [G]
  rw [hD₁, hD₂]
  calc
    (3 : ZMod G) * (-(C₂ : ZMod G))
        = -((3 : ZMod G) * (C₂ : ZMod G)) := by ring
    _ = -((2 : ZMod G) * (C₁ : ZMod G)) := by rw [hCostRelation]
    _ = (2 : ZMod G) * (-(C₁ : ZMod G)) := by ring

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/--
top layer 幅が 2 なら、その suffix start から terminal start までは
exact に 2 cell。
-/
theorem topLayerStart_add_two_eq_terminalStart
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    (hWidth :
      P.terminalCriticalStart -
          S.topLayerSuffixPacket.a = 2) :
    S.topLayerSuffixPacket.a + 2 =
      P.terminalCriticalStart := by
  have haLe :
      S.topLayerSuffixPacket.a ≤
        P.terminalCriticalStart :=
    Nat.le_of_lt
      S.topLayerSuffixPacket.a_lt_c
  rw [← hWidth]
  exact Nat.add_sub_of_le haLe


/--
top layer 幅 2 のとき、その二 cell 間の Beatty gap は exact に 1。
-/
theorem topTwoCell_beatty_gap_one
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    (hWidth :
      P.terminalCriticalStart -
          S.topLayerSuffixPacket.a = 2) :
    beattyIndex (S.topLayerSuffixPacket.a + 1) =
      beattyIndex S.topLayerSuffixPacket.a + 1 := by
  let T := S.topLayerSuffixPacket
  have hcEq :
      T.a + 2 = P.terminalCriticalStart := by
    simpa [T] using
      S.topLayerStart_add_two_eq_terminalStart hWidth
  have ha1c :
      T.a + 1 < P.terminalCriticalStart := by
    rw [← hcEq]
    omega
  have haMem :
      T.a ∈
        Finset.Ico T.a P.terminalCriticalStart :=
    Finset.mem_Ico.mpr
      ⟨le_rfl, T.a_lt_c⟩
  have ha1Mem :
      T.a + 1 ∈
        Finset.Ico T.a P.terminalCriticalStart :=
    Finset.mem_Ico.mpr
      ⟨by omega, ha1c⟩
  have hDepthA :
      P.h T.a =
        P.h (P.terminalCriticalStart - 1) := by
    simpa [T] using
      S.topLayer_depth_eq_terminalPredDepth
        (by
          simpa [T] using haMem)
  have hDepthA1 :
      P.h (T.a + 1) =
        P.h (P.terminalCriticalStart - 1) := by
    simpa [T] using
      S.topLayer_depth_eq_terminalPredDepth
        (by
          simpa [T] using ha1Mem)
  have hcLeM :
      P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have haM :
      T.a < P.m :=
    lt_of_lt_of_le
      T.a_lt_c
      hcLeM
  have ha1M :
      T.a + 1 < P.m :=
    lt_of_lt_of_le
      ha1c
      hcLeM
  have hDepthLeA :=
    P.admissible.depth_le haM
  have hDepthLeA1 :=
    P.admissible.depth_le ha1M
  have hLineA :=
    S.checkpoint_line
      T.a
      T.b_le_a
      T.a_lt_c
  have hbA1 :
      S.b ≤ T.a + 1 :=
    le_trans T.b_le_a
      (by omega)
  have hLineA1 :=
    S.checkpoint_line
      (T.a + 1)
      hbA1
      ha1c
  unfold profileCheckpoint at hLineA hLineA1
  rw [hDepthA] at hLineA hDepthLeA
  rw [hDepthA1] at hLineA1 hDepthLeA1
  have hOffset :
      T.a + 1 - S.b =
        (T.a - S.b) + 1 := by
    have hbA : S.b ≤ T.a :=
      T.b_le_a
    omega
  have hCheckpointSucc :
      beattyIndex (T.a + 1) -
          P.h (P.terminalCriticalStart - 1) =
        (beattyIndex T.a -
            P.h (P.terminalCriticalStart - 1)) + 1 := by
    rw [hLineA1, hLineA, hOffset]
    omega
  calc
    beattyIndex (T.a + 1)
        =
      (beattyIndex (T.a + 1) -
          P.h (P.terminalCriticalStart - 1)) +
        P.h (P.terminalCriticalStart - 1) := by
          exact
            (Nat.sub_add_cancel hDepthLeA1).symm
    _ =
      ((beattyIndex T.a -
          P.h (P.terminalCriticalStart - 1)) + 1) +
        P.h (P.terminalCriticalStart - 1) := by
          rw [hCheckpointSucc]
    _ =
      ((beattyIndex T.a -
          P.h (P.terminalCriticalStart - 1)) +
        P.h (P.terminalCriticalStart - 1)) + 1 := by
          omega
    _ =
      beattyIndex T.a + 1 := by
          rw [Nat.sub_add_cancel hDepthLeA]

/--
幅 2 の top ribbon で desired relation
`3D₂ = 2D₁ (mod G)`。
-/
theorem topTwoCell_residue_mod
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    (hWidth :
      P.terminalCriticalStart -
          S.topLayerSuffixPacket.a = 2) :
    (3 : ZMod P.gap) *
        (columnLayerFareyResidue
          P.H
          P.m
          (S.topLayerSuffixPacket.a + 1)
          P.topLayer :
          ZMod P.gap) =
      (2 : ZMod P.gap) *
        (columnLayerFareyResidue
          P.H
          P.m
          S.topLayerSuffixPacket.a
          P.topLayer :
          ZMod P.gap) := by
  let T := S.topLayerSuffixPacket
  have hcEq :
      T.a + 2 = P.terminalCriticalStart := by
    simpa [T] using
      S.topLayerStart_add_two_eq_terminalStart hWidth
  have ha1c :
      T.a + 1 < P.terminalCriticalStart := by
    rw [← hcEq]
    omega
  have hcLeM :
      P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hk :
      T.a + 1 < P.m :=
    lt_of_lt_of_le
      ha1c
      hcLeM
  have haM :
      T.a < P.m :=
    lt_of_lt_of_le
      T.a_lt_c
      hcLeM
  have hTopMem :
      T.a ∈
        profileLayerSupport
          P.m P.h P.topLayer := by
    exact T.left_mem
  have hTopLtDepth :
      P.topLayer < P.h T.a :=
    (Finset.mem_filter.mp hTopMem).2
  have hDepthLe :=
    P.admissible.depth_le haM
  have hj :
      P.topLayer < beattyIndex T.a :=
    lt_of_lt_of_le
      hTopLtDepth
      hDepthLe
  have hBeatty :
      beattyIndex (T.a + 1) =
        beattyIndex T.a + 1 := by
    simpa [T] using
      S.topTwoCell_beatty_gap_one hWidth
  have h :=
    consecutive_columnLayerFareyResidue_mod
      P.gap_pos
      P.terminal_beatty
      hk
      hj
      hBeatty
  change
    (3 : ZMod (columnLayerGap P.H P.m)) *
        (columnLayerFareyResidue
          P.H P.m (T.a + 1) P.topLayer :
          ZMod (columnLayerGap P.H P.m)) =
      (2 : ZMod (columnLayerGap P.H P.m)) *
        (columnLayerFareyResidue
          P.H P.m T.a P.topLayer :
          ZMod (columnLayerGap P.H P.m))
  exact h

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
