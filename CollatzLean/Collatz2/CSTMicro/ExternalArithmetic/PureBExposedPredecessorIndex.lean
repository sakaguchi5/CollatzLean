import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTopCellMinimalityPacket

/-!
# Pure B: exposed predecessor indices

odd checkpoint を endpoint まで延長して

  p_k = beta(k) - h(k)   (k < m),
  p_m = H,
  e_k = p_(k+1) - p_k

と置く。

`h(k)>0` かつ `e_k >= 2` の cut は、actual parity word では
selected odd の直後に少なくとも一つ even があり、かつ一段右へ戻しても
critical roof を越えない cut である。これを exposed predecessor index と呼ぶ。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- profile checkpoint を terminal endpoint `p_m = H` まで延長する。 -/
noncomputable def profileEndpointCheckpoint
    (P : PureBProfileObstruction)
    (k : ℕ) : ℕ :=
  if k < P.m then profileCheckpoint P.h k else P.H

/-- consecutive extended checkpoints の run gap。 -/
noncomputable def profileRunGap
    (P : PureBProfileObstruction)
    (k : ℕ) : ℕ :=
  P.profileEndpointCheckpoint (k + 1) -
    P.profileEndpointCheckpoint k

/-- pure-coordinate で見た removable/exposed predecessor cut。 -/
def IsExposedPredecessorIndex
    (P : PureBProfileObstruction)
    (k : ℕ) : Prop :=
  k < P.m ∧
    0 < P.h k ∧
    2 ≤ P.profileRunGap k

/-- exposed predecessor indices の finite support。 -/
noncomputable def exposedPredecessorSet
    (P : PureBProfileObstruction) : Finset ℕ := by
  classical
  exact (Finset.range P.m).filter P.IsExposedPredecessorIndex

@[simp] theorem profileEndpointCheckpoint_of_lt
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    P.profileEndpointCheckpoint k = profileCheckpoint P.h k := by
  simp [profileEndpointCheckpoint, hk]

@[simp] theorem profileEndpointCheckpoint_m
    (P : PureBProfileObstruction) :
    P.profileEndpointCheckpoint P.m = P.H := by
  simp [profileEndpointCheckpoint]

/-- interior run gap は ordinary profile checkpoints の差。 -/
theorem profileRunGap_of_succ_lt
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k + 1 < P.m) :
    P.profileRunGap k =
      profileCheckpoint P.h (k + 1) - profileCheckpoint P.h k := by
  unfold profileRunGap
  rw [P.profileEndpointCheckpoint_of_lt hk]
  rw [P.profileEndpointCheckpoint_of_lt (by omega : k < P.m)]

/-- last odd run では right endpoint は `H`。 -/
theorem profileRunGap_of_succ_eq_m
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k + 1 = P.m) :
    P.profileRunGap k =
      P.H - profileCheckpoint P.h k := by
  unfold profileRunGap
  rw [hk, P.profileEndpointCheckpoint_m]
  rw [P.profileEndpointCheckpoint_of_lt (by omega : k < P.m)]

@[simp] theorem mem_exposedPredecessorSet_iff
    (P : PureBProfileObstruction)
    {k : ℕ} :
    k ∈ P.exposedPredecessorSet ↔ P.IsExposedPredecessorIndex k := by
  classical
  simp [exposedPredecessorSet, IsExposedPredecessorIndex]

/-- exposed index は proper odd cut。 -/
theorem IsExposedPredecessorIndex.lt_m
    {P : PureBProfileObstruction}
    {k : ℕ}
    (E : P.IsExposedPredecessorIndex k) :
    k < P.m :=
  E.1

/-- exposed index の profile column は positive。 -/
theorem IsExposedPredecessorIndex.depth_pos
    {P : PureBProfileObstruction}
    {k : ℕ}
    (E : P.IsExposedPredecessorIndex k) :
    0 < P.h k :=
  E.2.1

/-- exposed index の run gap は少なくとも二。 -/
theorem IsExposedPredecessorIndex.two_le_runGap
    {P : PureBProfileObstruction}
    {k : ℕ}
    (E : P.IsExposedPredecessorIndex k) :
    2 ≤ P.profileRunGap k :=
  E.2.2

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
