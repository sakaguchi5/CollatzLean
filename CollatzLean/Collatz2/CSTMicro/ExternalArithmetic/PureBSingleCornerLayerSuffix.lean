import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerDepthMonotone
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.SturmianProfileLevelSets

/-!
# Pure B single-corner: every occupied layer is one suffix interval

single-corner support `[b,c)` 上では depth が単調非減少なので、固定 layer `j` の support

  { k < m | j < h(k) }

は空でなければ必ず一つの suffix interval `[a_j,c)` になる。

ここでは `j < h(c-1)` の occupied layer に対して canonical least start を取り、
`profileLayerSupport` と `Finset.Ico a c` の exact equality を packet 化する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-- terminal predecessor `c-1` は single-corner support 内にあり depth は正。 -/
theorem terminalPred_depth_pos
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    0 < P.h (P.terminalCriticalStart - 1) := by
  have hcPos : 0 < P.terminalCriticalStart := by
    exact lt_of_le_of_lt (Nat.zero_le S.b) S.b_lt_c
  have htLtC :
      P.terminalCriticalStart - 1 < P.terminalCriticalStart := by
    omega
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have htM :
      P.terminalCriticalStart - 1 < P.m :=
    lt_of_lt_of_le htLtC hcLeM
  have hbSuccLe :
      S.b + 1 ≤ P.terminalCriticalStart :=
    Nat.succ_le_iff.mpr S.b_lt_c
  have hbT :
      S.b ≤ P.terminalCriticalStart - 1 := by
    exact Nat.le_sub_of_add_le hbSuccLe
  exact S.depth_pos htM hbT htLtC

/-- occupied layer `j` の least support column が存在する。 -/
theorem exists_layer_start
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {j : ℕ}
    (hj : j < P.h (P.terminalCriticalStart - 1)) :
    ∃ a : ℕ,
      S.b ≤ a ∧
      a < P.terminalCriticalStart ∧
      j < P.h a := by
  have hcPos : 0 < P.terminalCriticalStart := by
    exact lt_of_le_of_lt (Nat.zero_le S.b) S.b_lt_c
  refine ⟨P.terminalCriticalStart - 1, ?_, ?_, hj⟩
  · have hbSuccLe :
        S.b + 1 ≤ P.terminalCriticalStart :=
      Nat.succ_le_iff.mpr S.b_lt_c
    exact Nat.le_sub_of_add_le hbSuccLe
  · exact Nat.sub_lt hcPos (by norm_num)

/--
一つの occupied layer を exact suffix interval として保持する packet。
-/
structure LayerSuffixPacket
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    (j : ℕ) where
  a : ℕ
  b_le_a : S.b ≤ a
  a_lt_c : a < P.terminalCriticalStart
  support_eq :
    profileLayerSupport P.m P.h j =
      Finset.Ico a P.terminalCriticalStart

/--
occupied layer `j` の canonical least start を取り、support を `[a_j,c)` に exact 化する。
-/
noncomputable def toLayerSuffixPacket
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {j : ℕ}
    (hj : j < P.h (P.terminalCriticalStart - 1)) :
    S.LayerSuffixPacket j := by
  classical
  let E : ∃ a : ℕ,
      S.b ≤ a ∧
      a < P.terminalCriticalStart ∧
      j < P.h a :=
    S.exists_layer_start hj
  let a := Nat.find E
  have haSpec :
      S.b ≤ a ∧
      a < P.terminalCriticalStart ∧
      j < P.h a := by
    simpa [a] using Nat.find_spec E
  refine {
    a := a
    b_le_a := haSpec.1
    a_lt_c := haSpec.2.1
    support_eq := ?_
  }
  ext k
  constructor
  · intro hk
    have hkFilter := Finset.mem_filter.mp hk
    have hkM : k < P.m := Finset.mem_range.mp hkFilter.1
    have hjk : j < P.h k := hkFilter.2
    have hkPos : 0 < P.h k := lt_of_le_of_lt (Nat.zero_le j) hjk
    have hSupport := (S.support_iff k hkM).1 hkPos
    have hCandidate :
        S.b ≤ k ∧
        k < P.terminalCriticalStart ∧
        j < P.h k :=
      ⟨hSupport.1, hSupport.2, hjk⟩
    have hak : a ≤ k := by
      have h := Nat.find_min' E hCandidate
      simpa [a] using h
    exact Finset.mem_Ico.mpr ⟨hak, hSupport.2⟩
  · intro hk
    have hkIco := Finset.mem_Ico.mp hk
    have hcLeM : P.terminalCriticalStart ≤ P.m :=
      P.terminalCriticalStart_spec.1
    have hkM : k < P.m :=
      lt_of_lt_of_le hkIco.2 hcLeM
    have hMono : P.h a ≤ P.h k :=
      S.depth_mono haSpec.1 hkIco.1 hkIco.2
    have hjk : j < P.h k :=
      lt_of_lt_of_le haSpec.2.2 hMono
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hkM, hjk⟩

/-- packet の left endpoint は実際にその layer に属する。 -/
theorem LayerSuffixPacket.left_mem
    {P : PureBProfileObstruction}
    {S : P.SingleExposedCornerRigidityPacket}
    {j : ℕ}
    (T : S.LayerSuffixPacket j) :
    T.a ∈ profileLayerSupport P.m P.h j := by
  rw [T.support_eq]
  exact Finset.mem_Ico.mpr ⟨le_rfl, T.a_lt_c⟩

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
