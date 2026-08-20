import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLayerSuffix

/-!
# Pure B single-corner: top layer has width at most two

`d = h(c-1)` を terminal predecessor の最大 depth とする。
最上段 layer `j = d-1` は occupied なので前ファイルから一つの suffix interval `[a,c)` を持つ。

single-corner depth は support 上で単調非減少であり、`c-1` で値 `d` を取るため、
最上段 support 内では depth は全て exact に `d`。
もし `a+2<c` なら、checkpoint line と同じ depth から

  beattyIndex(a+2) = beattyIndex(a) + 2

が出る。しかし `BeattyTwoStep` は

  beattyIndex(a+2) >= beattyIndex(a) + 3

を与えるので矛盾する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic
namespace PureBProfileObstruction

/--
terminal predecessor depth に対応する最上段 layer index。

値そのものは single-corner packet に依存せず、
`PureBProfileObstruction` だけから決まる。
-/
noncomputable def topLayer
    (P : PureBProfileObstruction) : ℕ :=
  P.h (P.terminalCriticalStart - 1) - 1


namespace SingleExposedCornerRigidityPacket

/--
single-corner の下では top layer は
terminal predecessor depth より strict に小さい。
-/
theorem topLayer_lt_terminalPredDepth
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    P.topLayer <
      P.h (P.terminalCriticalStart - 1) := by
  unfold PureBProfileObstruction.topLayer
  exact Nat.sub_lt
    S.terminalPred_depth_pos
    (by norm_num)


/--
top layer の canonical suffix packet。
-/
noncomputable def topLayerSuffixPacket
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    S.LayerSuffixPacket P.topLayer :=
  S.toLayerSuffixPacket
    S.topLayer_lt_terminalPredDepth


/--
top layer support 内では depth は
terminal predecessor depth と exact に一致する。
-/
theorem topLayer_depth_eq_terminalPredDepth
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k : ℕ}
    (hk :
      k ∈ Finset.Ico
        S.topLayerSuffixPacket.a
        P.terminalCriticalStart) :
    P.h k =
      P.h (P.terminalCriticalStart - 1) := by
  classical
  let T := S.topLayerSuffixPacket
  have hkIco :
      k ∈ Finset.Ico T.a P.terminalCriticalStart := by
    simpa [T] using hk
  have hkBounds :=
    Finset.mem_Ico.mp hkIco
  have hkALe :
      T.a ≤ k :=
    hkBounds.1
  have hkLtC :
      k < P.terminalCriticalStart :=
    hkBounds.2
  have hkMem :
      k ∈ profileLayerSupport P.m P.h P.topLayer := by
    rw [T.support_eq]
    exact hkIco
  have hkFilter :=
    Finset.mem_filter.mp hkMem
  have hTopLt :
      P.topLayer < P.h k :=
    hkFilter.2
  have hcPos :
      0 < P.terminalCriticalStart := by
    exact
      lt_of_le_of_lt
        (Nat.zero_le S.b)
        S.b_lt_c
  have htLtC :
      P.terminalCriticalStart - 1 <
        P.terminalCriticalStart := by
    exact
      Nat.sub_lt hcPos (by norm_num)
  have hkSuccLe :
      k + 1 ≤ P.terminalCriticalStart :=
    Nat.succ_le_iff.mpr hkLtC
  have hkLeT :
      k ≤ P.terminalCriticalStart - 1 := by
    exact
      Nat.le_sub_of_add_le hkSuccLe
  have hkB :
      S.b ≤ k :=
    le_trans T.b_le_a hkALe
  have hMono :
      P.h k ≤
        P.h (P.terminalCriticalStart - 1) :=
    S.depth_mono hkB hkLeT htLtC
  have hTerminalPos :
      0 < P.h (P.terminalCriticalStart - 1) :=
    S.terminalPred_depth_pos
  have hTerminalOneLe :
      1 ≤ P.h (P.terminalCriticalStart - 1) :=
    Nat.succ_le_iff.mpr hTerminalPos
  unfold PureBProfileObstruction.topLayer at hTopLt
  have hTerminalLe :
      P.h (P.terminalCriticalStart - 1) ≤
        P.h k := by
    calc
      P.h (P.terminalCriticalStart - 1)
          =
        (P.h (P.terminalCriticalStart - 1) - 1) + 1 := by
            exact
              (Nat.sub_add_cancel hTerminalOneLe).symm
      _ ≤ P.h k := by
          exact Nat.succ_le_iff.mpr hTopLt
  exact Nat.le_antisymm hMono hTerminalLe


/--
最上段 suffix interval の幅は高々 2。
-/
theorem topLayer_width_le_two
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    P.terminalCriticalStart -
        S.topLayerSuffixPacket.a ≤ 2 := by
  classical
  let T := S.topLayerSuffixPacket
  -- 以後 `S.topLayerSuffixPacket.a` と `T.a` を混在させない。
  change
    P.terminalCriticalStart - T.a ≤ 2
  by_contra hnot
  have hGap :
      2 < P.terminalCriticalStart - T.a := by
    omega
  have ha2c :
      T.a + 2 < P.terminalCriticalStart := by
    have haC :
        T.a < P.terminalCriticalStart :=
      T.a_lt_c
    omega
  have haMem :
      T.a ∈
        Finset.Ico T.a P.terminalCriticalStart :=
    Finset.mem_Ico.mpr
      ⟨le_rfl, T.a_lt_c⟩
  have ha2Mem :
      T.a + 2 ∈
        Finset.Ico T.a P.terminalCriticalStart :=
    Finset.mem_Ico.mpr
      ⟨by omega, ha2c⟩
  have hDepthA :
      P.h T.a =
        P.h (P.terminalCriticalStart - 1) := by
    simpa [T] using
      S.topLayer_depth_eq_terminalPredDepth
        (by
          simpa [T] using haMem)
  have hDepthA2 :
      P.h (T.a + 2) =
        P.h (P.terminalCriticalStart - 1) := by
    simpa [T] using
      S.topLayer_depth_eq_terminalPredDepth
        (by
          simpa [T] using ha2Mem)
  have hcLeM :
      P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have haM :
      T.a < P.m :=
    lt_of_lt_of_le
      T.a_lt_c
      hcLeM
  have ha2M :
      T.a + 2 < P.m :=
    lt_of_lt_of_le
      ha2c
      hcLeM
  have hDepthLeA :=
    P.admissible.depth_le haM
  have hDepthLeA2 :=
    P.admissible.depth_le ha2M
  have hLineA :=
    S.checkpoint_line
      T.a
      T.b_le_a
      T.a_lt_c
  have hbA2 :
      S.b ≤ T.a + 2 := by
    exact le_trans T.b_le_a (by omega)
  have hLineA2 :=
    S.checkpoint_line
      (T.a + 2)
      hbA2
      ha2c
  have hBeatty :=
    beattyIndex_add_two_ge_add_three T.a
  unfold profileCheckpoint at hLineA hLineA2
  rw [hDepthA2] at hLineA2 hDepthLeA2
  rw [hDepthA] at hLineA hDepthLeA
  omega


/--
top layer が nonempty なので、
その suffix 幅は 1 または 2。
-/
theorem topLayer_width_eq_one_or_two
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    P.terminalCriticalStart -
          S.topLayerSuffixPacket.a = 1 ∨
      P.terminalCriticalStart -
          S.topLayerSuffixPacket.a = 2 := by
  let w :=
    P.terminalCriticalStart -
      S.topLayerSuffixPacket.a
  have hwLe :
      w ≤ 2 := by
    simpa [w] using
      S.topLayer_width_le_two
  have hwPos :
      0 < w := by
    dsimp [w]
    exact
      Nat.sub_pos_iff_lt.mpr
        S.topLayerSuffixPacket.a_lt_c
  have hw :
      w = 1 ∨ w = 2 := by
    omega
  simpa [w] using hw


end SingleExposedCornerRigidityPacket
end PureBProfileObstruction
end ExternalArithmetic
end CSTMicro
end Collatz2
