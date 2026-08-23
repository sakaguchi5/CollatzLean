import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.BeattyPositions

/-!
# Restarted suffix Hensel staircase: exact Beatty arithmetic

`RestartedSuffixHenselBridge` で作った

  delta_i = beattyIndex (b+i) - (beattyIndex b - 1 + i)

を、Nat subtraction の外へ出した exact additive / integer-cast identity に直す。

これにより `delta` の一段増分は Beatty index の一段増分から straight-line の
`+1` を引いたものとして exact に扱える。

このファイルでは real logarithm や large-width finiteness は導入しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RestartedTerminalStraightPacket

/--
Beatty checkpoint = straight base + Hensel gap。
Nat subtraction を消した exact identity。
-/
theorem suffixHenselBase_add_delta_eq_beattyIndex
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    S.suffixHenselBase i + S.suffixHenselDelta i =
      beattyIndex (S.b + i) := by
  have hLine :=
    singleCornerLine_lt_beatty
      (b := S.b) (n := i) S.beattyIndex_b_pos
  have hLe :
      S.suffixHenselBase i ≤ beattyIndex (S.b + i) := by
    simpa [suffixHenselBase, Nat.add_assoc] using Nat.le_of_lt hLine
  unfold suffixHenselDelta
  exact Nat.add_sub_of_le hLe

/--
Hensel gap の exact integer displacement formula。

  delta_i - 1
    = beattyIndex(b+i) - beattyIndex(b) - i

を整数上で表す。
-/
theorem suffixHenselDelta_cast_sub_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    (S.suffixHenselDelta i : ℤ) - 1 =
      (beattyIndex (S.b + i) : ℤ) -
        (beattyIndex S.b : ℤ) - (i : ℤ) := by
  have hEq := S.suffixHenselBase_add_delta_eq_beattyIndex i
  have hBetaPos := S.beattyIndex_b_pos
  unfold suffixHenselBase at hEq
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hEq
  push_cast at hCast
  have hPred :
      ((beattyIndex S.b - 1 : ℕ) : ℤ) =
        (beattyIndex S.b : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ beattyIndex S.b)]
    norm_num
  rw [hPred] at hCast
  linarith

/--
一段の Hensel staircase increment は、Beatty increment から straight-line increment `1`
を引いたものに exact に等しい。
-/
theorem suffixHenselDelta_step_cast
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    (S.suffixHenselDelta (i + 1) : ℤ) -
        (S.suffixHenselDelta i : ℤ) =
      (beattyIndex (S.b + i + 1) : ℤ) -
        (beattyIndex (S.b + i) : ℤ) - 1 := by
  have h0 := S.suffixHenselDelta_cast_sub_one i
  have h1 := S.suffixHenselDelta_cast_sub_one (i + 1)
  have hIdx : S.b + (i + 1) = S.b + i + 1 := by omega
  rw [hIdx] at h1
  push_cast at h1
  linear_combination h1 - h0

/-- Beatty increment が `1` なら Hensel gap は据え置き。 -/
theorem suffixHenselDelta_succ_eq_of_beattyIndex_succ_eq_add_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ)
    (hBeatty :
      beattyIndex (S.b + i + 1) =
        beattyIndex (S.b + i) + 1) :
    S.suffixHenselDelta (i + 1) =
      S.suffixHenselDelta i := by
  have hStep := S.suffixHenselDelta_step_cast i
  rw [hBeatty] at hStep
  push_cast at hStep
  norm_num at hStep
  have hEq :
      (S.suffixHenselDelta (i + 1) : ℤ) =
        (S.suffixHenselDelta i : ℤ) := by
    exact sub_eq_zero.mp hStep
  exact_mod_cast hEq

/-- Beatty increment が `2` なら Hensel gap は exact に一つ増える。 -/
theorem suffixHenselDelta_succ_eq_add_one_of_beattyIndex_succ_eq_add_two
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ)
    (hBeatty :
      beattyIndex (S.b + i + 1) =
        beattyIndex (S.b + i) + 2) :
    S.suffixHenselDelta (i + 1) =
      S.suffixHenselDelta i + 1 := by
  have hStep := S.suffixHenselDelta_step_cast i
  rw [hBeatty] at hStep
  push_cast at hStep
  norm_num at hStep
  have hEq :
      (S.suffixHenselDelta (i + 1) : ℤ) =
        (S.suffixHenselDelta i : ℤ) + 1 := by
    linarith
  exact_mod_cast hEq

/--
逆向き：Hensel gap が据え置きなら Beatty increment は `1`。
-/
theorem beattyIndex_succ_eq_add_one_of_suffixHenselDelta_succ_eq
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ)
    (hDelta :
      S.suffixHenselDelta (i + 1) =
        S.suffixHenselDelta i) :
    beattyIndex (S.b + i + 1) =
      beattyIndex (S.b + i) + 1 := by
  have hStep := S.suffixHenselDelta_step_cast i
  rw [hDelta] at hStep
  have hInt :
      (beattyIndex (S.b + i + 1) : ℤ) =
        (beattyIndex (S.b + i) : ℤ) + 1 := by
    linarith
  exact_mod_cast hInt

/--
逆向き：Hensel gap が一つ増えたなら Beatty increment は `2`。
-/
theorem beattyIndex_succ_eq_add_two_of_suffixHenselDelta_succ_eq_add_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ)
    (hDelta :
      S.suffixHenselDelta (i + 1) =
        S.suffixHenselDelta i + 1) :
    beattyIndex (S.b + i + 1) =
      beattyIndex (S.b + i) + 2 := by
  have hStep := S.suffixHenselDelta_step_cast i
  rw [hDelta] at hStep
  push_cast at hStep
  have hInt :
      (beattyIndex (S.b + i + 1) : ℤ) =
        (beattyIndex (S.b + i) : ℤ) + 2 := by
    linarith
  exact_mod_cast hInt

/--
Hensel step pattern と Beatty gap `1/2` pattern の exact dictionary。
-/
theorem suffixHenselDelta_step_dictionary
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    (S.suffixHenselDelta (i + 1) = S.suffixHenselDelta i ↔
      beattyIndex (S.b + i + 1) = beattyIndex (S.b + i) + 1) ∧
    (S.suffixHenselDelta (i + 1) = S.suffixHenselDelta i + 1 ↔
      beattyIndex (S.b + i + 1) = beattyIndex (S.b + i) + 2) := by
  constructor
  · constructor
    · exact S.beattyIndex_succ_eq_add_one_of_suffixHenselDelta_succ_eq i
    · exact S.suffixHenselDelta_succ_eq_of_beattyIndex_succ_eq_add_one i
  · constructor
    · exact S.beattyIndex_succ_eq_add_two_of_suffixHenselDelta_succ_eq_add_one i
    · exact S.suffixHenselDelta_succ_eq_add_one_of_beattyIndex_succ_eq_add_two i

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
