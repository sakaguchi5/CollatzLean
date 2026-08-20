import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalExposedCorner

/-!
# Pure B: every positive-component endpoint is exposed

positive profile column `h(k)>0` の直後で profile が zero に戻る、または `k` が最後の
odd column なら、checkpoint は少なくとも二だけ前進する。

  h(k)>0,
  h(k+1)=0  ->  e_k >= 2.

従って positive support の各 connected component は、その右端に exposed predecessor
index を一つ持つ。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- positive column の checkpoint は Beatty roof より少なくとも一段下。 -/
theorem profileCheckpoint_succ_le_beatty_of_depth_pos
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m)
    (hPos : 0 < P.h k) :
    profileCheckpoint P.h k + 1 ≤ beattyIndex k := by
  have hDepth := P.admissible.depth_le hk
  unfold profileCheckpoint
  omega

/-- interior で positive support が終わるなら、その cut は exposed。 -/
theorem positiveEndpoint_isExposed_of_succ_lt
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k + 1 < P.m)
    (hPos : 0 < P.h k)
    (hNextZero : P.h (k + 1) = 0) :
    P.IsExposedPredecessorIndex k := by
  have hk0 : k < P.m := by omega
  have hBelow := P.profileCheckpoint_succ_le_beatty_of_depth_pos hk0 hPos
  have hBeatty : beattyIndex k < beattyIndex (k + 1) :=
    beattyIndex_strictMono (by omega)
  have hNextCheckpoint :
      profileCheckpoint P.h (k + 1) = beattyIndex (k + 1) := by
    unfold profileCheckpoint
    rw [hNextZero]
    simp
  have hGap : 2 ≤ P.profileRunGap k := by
    rw [P.profileRunGap_of_succ_lt hk, hNextCheckpoint]
    omega
  exact ⟨hk0, hPos, hGap⟩

/-- last odd column が positive なら terminal endpoint run は exposed。 -/
theorem positiveLastColumn_isExposed
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k + 1 = P.m)
    (hPos : 0 < P.h k) :
    P.IsExposedPredecessorIndex k := by
  have hk0 : k < P.m := by omega
  have hBelow := P.profileCheckpoint_succ_le_beatty_of_depth_pos hk0 hPos
  have hBeatty : beattyIndex k < beattyIndex P.m :=
    beattyIndex_strictMono (by omega)
  have hGap : 2 ≤ P.profileRunGap k := by
    rw [P.profileRunGap_of_succ_eq_m hk, P.terminal_beatty]
    omega
  exact ⟨hk0, hPos, hGap⟩

/--
positive support component の right endpoint は exposed。
`k+1=m` と interior zero-return を一つにまとめた形。
-/
theorem positiveComponentEndpoint_isExposed
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m)
    (hPos : 0 < P.h k)
    (hEnd : k + 1 = P.m ∨ P.h (k + 1) = 0) :
    P.IsExposedPredecessorIndex k := by
  rcases hEnd with hLast | hZero
  · exact P.positiveLastColumn_isExposed hLast hPos
  · by_cases hEq : k + 1 = P.m
    · exact P.positiveLastColumn_isExposed hEq hPos
    · have hLt : k + 1 < P.m := by omega
      exact P.positiveEndpoint_isExposed_of_succ_lt hLt hPos hZero

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
