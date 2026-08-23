import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyFactorRepeat
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselRepeatArithmetic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBeattyArithmetic

/-!
# Restarted suffix Hensel: Beatty factor repeat -> SameDeltaOffsetBlock

Beatty displacement factor の `m+1` complexity bound から、
`2*m+1 <= width` なら actual restarted Hensel staircase 内に length `m` の
`SameDeltaOffsetBlock` が自動的に存在することを示す。

ここでは repeated block を作るところまで。nonzero/zero repeat の size contradiction や
large-width finiteness は主張しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RestartedTerminalStraightPacket

/-- actual Hensel delta は global に nondecreasing。 -/
theorem suffixHenselDelta_mono_of_le
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i j : ℕ}
    (hij : i ≤ j) :
    S.suffixHenselDelta i ≤ S.suffixHenselDelta j := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases hijEq : i = j + 1
      · subst i
        exact le_rfl
      · have hij' : i ≤ j := by omega
        have hPrev := ih hij'
        rcases S.suffixHenselDelta_succ_eq_self_or_add_one j with hSame | hUp
        · rw [hSame]
          exact hPrev
        · rw [hUp]
          omega

/--
二つの Beatty displacement block が一致すれば、対応する actual Hensel delta profile は
一定 offset だけ平行移動する。
-/
theorem sameDeltaOffsetBlock_of_beattyDisplacementBlock
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i j m : ℕ}
    (hij : i ≤ j)
    (hDisp :
      ∀ r : ℕ, r ≤ m →
        beattyIndex (S.b + j + r) - beattyIndex (S.b + j) =
          beattyIndex (S.b + i + r) - beattyIndex (S.b + i)) :
    let C := S.toMonotoneSuffixHenselChain hStart
    let Delta := S.suffixHenselDelta j - S.suffixHenselDelta i
    C.SameDeltaOffsetBlock i j m Delta := by
  dsimp
  intro r hr
  have hMono :
      S.suffixHenselDelta i ≤ S.suffixHenselDelta j :=
    S.suffixHenselDelta_mono_of_le hij
  have hI0 := S.suffixHenselDelta_cast_sub_one i
  have hJ0 := S.suffixHenselDelta_cast_sub_one j
  have hIr := S.suffixHenselDelta_cast_sub_one (i + r)
  have hJr := S.suffixHenselDelta_cast_sub_one (j + r)
  have hDispR := hDisp r hr
  have hCastDisp := congrArg (fun n : ℕ => (n : ℤ)) hDispR
  by_cases hr0 : r = 0
  · subst r
    change
      S.suffixHenselDelta j =
        S.suffixHenselDelta i +
          (S.suffixHenselDelta j - S.suffixHenselDelta i)
    omega
  · have hBi' : beattyIndex (S.b + i) ≤ beattyIndex (S.b + i + r) := by
      exact Nat.le_of_lt (beattyIndex_strictMono (by omega))
    have hBj' : beattyIndex (S.b + j) ≤ beattyIndex (S.b + j + r) := by
      exact Nat.le_of_lt (beattyIndex_strictMono (by omega))
    rw [Nat.cast_sub hBj', Nat.cast_sub hBi'] at hCastDisp
    have hIdxI : S.b + (i + r) = S.b + i + r := by omega
    have hIdxJ : S.b + (j + r) = S.b + j + r := by omega
    rw [hIdxI] at hIr
    rw [hIdxJ] at hJr
    push_cast at hIr hJr hI0 hJ0
    have hDeltaInt :
        (S.suffixHenselDelta (j + r) : ℤ) -
            (S.suffixHenselDelta (i + r) : ℤ) =
          (S.suffixHenselDelta j : ℤ) -
            (S.suffixHenselDelta i : ℤ) := by
      linear_combination (hJr - hJ0) - (hIr - hI0) + hCastDisp
    have hGoalInt :
        (S.suffixHenselDelta (j + r) : ℤ) =
          (S.suffixHenselDelta (i + r) : ℤ) +
            ((S.suffixHenselDelta j - S.suffixHenselDelta i : ℕ) : ℤ) := by
      rw [Nat.cast_sub hMono]
      linarith
    exact_mod_cast hGoalInt

/--
`2*m+1 <= width` なら actual restarted Hensel chain 内に length `m` の
parallel exponent block が必ず存在する。

さらに repeat starts は `0 <= i < j <= m+1` に取れる。
-/
theorem exists_sameDeltaOffsetBlock_of_two_mul_add_one_le_width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (m : ℕ)
    (hWidth : 2 * m + 1 ≤ S.width) :
    let C := S.toMonotoneSuffixHenselChain hStart
    ∃ i j Delta : ℕ,
      i < j ∧
      j ≤ m + 1 ∧
      j + m ≤ C.width ∧
      C.SameDeltaOffsetBlock i j m Delta := by
  dsimp
  rcases
      exists_repeated_beattyDisplacementBlock S.b m with
    ⟨i, j, hij, hjBound, hDisp⟩
  let Delta := S.suffixHenselDelta j - S.suffixHenselDelta i
  refine ⟨i, j, Delta, hij, hjBound, ?_, ?_⟩
  · change j + m ≤ S.width
    omega
  · dsimp [Delta]
    exact
      S.sameDeltaOffsetBlock_of_beattyDisplacementBlock
        hStart (Nat.le_of_lt hij) hDisp

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
