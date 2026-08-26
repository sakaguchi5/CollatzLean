import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselChain
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity

/-!
# MultiCorner: restarted straight component から全-suffix Hensel chain への bridge

このファイルは restarted geometry と純粋算術の境界だけを担当する。

`RestartedTerminalStraightPacket` が与える

* restart entrance depth = 1,
* terminal component 上の straight checkpoint line,
* critical Beatty checkpoint との差が monotone `0/1` staircase になること,
* corridor 内の任意 cut に対する full local 3-adic divisibility

を使って、`ExternalArithmetic.MonotoneSuffixHenselChain` を実際に構成する。

ここでは full suffix Hensel rigidity や large-width termination は仮定しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-! ## Beatty staircase の局所算術 -/

/-- Beatty index の一段増分は高々 2。 -/
private theorem suffixHensel_beattyIndex_succ_le_add_two
    (n : ℕ) :
    beattyIndex (n + 1) ≤ beattyIndex n + 2 := by
  apply beattyIndex_le_of_upper
  have hUpper := beattyIndex_upper n
  have hMul :
      3 ^ n * 3 ≤
        2 ^ (beattyIndex n + 1) * 4 := by
    exact Nat.mul_le_mul hUpper (by norm_num)
  calc
    3 ^ (n + 1)
        = 3 ^ n * 3 := by
            rw [pow_succ]
    _ ≤ 2 ^ (beattyIndex n + 1) * 4 := hMul
    _ = 2 ^ ((beattyIndex n + 2) + 1) := by
      calc
        2 ^ (beattyIndex n + 1) * 4
            = 2 ^ (beattyIndex n + 1) * 2 ^ 2 := by
                norm_num
        _ = 2 ^ ((beattyIndex n + 1) + 2) := by
              rw [← pow_add]
        _ = 2 ^ ((beattyIndex n + 2) + 1) := by
              congr 1

/-- Beatty index の一段増分は exact に 1 または 2。 -/
private theorem suffixHensel_beattyIndex_succ_eq_add_one_or_two
    (n : ℕ) :
    beattyIndex (n + 1) = beattyIndex n + 1 ∨
      beattyIndex (n + 1) = beattyIndex n + 2 := by
  have hLower := beattyIndex_lt_succ n
  have hUpper := suffixHensel_beattyIndex_succ_le_add_two n
  omega

namespace RestartedTerminalStraightPacket

/-- terminal critical start は `b + width`。 -/
theorem terminalCriticalStart_eq_b_add_width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    P.terminalCriticalStart = S.b + S.width := by
  unfold width
  exact
    (Nat.add_sub_of_le
      (Nat.le_of_lt S.b_lt_terminalCriticalStart)).symm

/-- straight checkpoint line の offset `i` における dyadic base exponent。 -/
noncomputable def suffixHenselBase
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) : ℕ :=
  beattyIndex S.b - 1 + i

/-- critical Beatty checkpoint と straight checkpoint line の exponent gap。 -/
noncomputable def suffixHenselDelta
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) : ℕ :=
  beattyIndex (S.b + i) - S.suffixHenselBase i

/-- base exponent は offset を一つ進めるごとに exact に一つ増える。 -/
theorem suffixHenselBase_add
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i r : ℕ) :
    S.suffixHenselBase (i + r) =
      S.suffixHenselBase i + r := by
  unfold suffixHenselBase
  omega

/-- restart entrance では critical-minus-line gap は exact に 1。 -/
theorem suffixHenselDelta_zero
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    S.suffixHenselDelta 0 = 1 := by
  have hBetaPos := S.beattyIndex_b_pos
  unfold suffixHenselDelta suffixHenselBase
  simp only [Nat.add_zero]
  omega

/-- critical Beatty checkpoint は straight line より strict に上なので gap は正。 -/
theorem suffixHenselDelta_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    0 < S.suffixHenselDelta i := by
  have hLine :=
    singleCornerLine_lt_beatty
      (b := S.b) (n := i) S.beattyIndex_b_pos
  unfold suffixHenselDelta suffixHenselBase
  omega

/-- Beatty increment `1/2` から gap staircase の increment は exact に `0/1`。 -/
theorem suffixHenselDelta_succ_eq_self_or_add_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    S.suffixHenselDelta (i + 1) = S.suffixHenselDelta i ∨
      S.suffixHenselDelta (i + 1) = S.suffixHenselDelta i + 1 := by
  have hLine0 :
      beattyIndex S.b - 1 + i <
        beattyIndex (S.b + i) :=
    singleCornerLine_lt_beatty
      (b := S.b) (n := i) S.beattyIndex_b_pos
  have hLine1 :
      beattyIndex S.b - 1 + (i + 1) <
        beattyIndex (S.b + (i + 1)) :=
    singleCornerLine_lt_beatty
      (b := S.b) (n := i + 1) S.beattyIndex_b_pos
  have hBase0 :
      beattyIndex S.b - 1 + i ≤
        beattyIndex (S.b + i) :=
    Nat.le_of_lt hLine0
  have hBase1 :
      beattyIndex S.b - 1 + (i + 1) ≤
        beattyIndex (S.b + (i + 1)) :=
    Nat.le_of_lt hLine1
  have hSub0 :
      beattyIndex (S.b + i) -
            (beattyIndex S.b - 1 + i) +
          (beattyIndex S.b - 1 + i) =
        beattyIndex (S.b + i) :=
    Nat.sub_add_cancel hBase0
  have hSub1 :
      beattyIndex (S.b + (i + 1)) -
            (beattyIndex S.b - 1 + (i + 1)) +
          (beattyIndex S.b - 1 + (i + 1)) =
        beattyIndex (S.b + (i + 1)) :=
    Nat.sub_add_cancel hBase1
  rcases
      suffixHensel_beattyIndex_succ_eq_add_one_or_two
        (S.b + i) with hGap | hGap
  · left
    unfold suffixHenselDelta suffixHenselBase
    have hGap' :
        beattyIndex (S.b + (i + 1)) =
          beattyIndex (S.b + i) + 1 := by
      simpa [Nat.add_assoc] using hGap
    omega
  · right
    unfold suffixHenselDelta suffixHenselBase
    have hGap' :
        beattyIndex (S.b + (i + 1)) =
          beattyIndex (S.b + i) + 2 := by
      simpa [Nat.add_assoc] using hGap
    omega

/-- 一列分の normalized forcing term。 -/
noncomputable def suffixHenselForcing
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) : ℤ :=
  ((2 ^ S.suffixHenselDelta i - 1 : ℕ) : ℤ)

/-- forcing term を整数冪の形へ戻す。 -/
theorem suffixHenselForcing_eq
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    S.suffixHenselForcing i =
      (2 : ℤ) ^ S.suffixHenselDelta i - 1 := by
  unfold suffixHenselForcing
  have hPos :
      0 < 2 ^ S.suffixHenselDelta i := by
    positivity
  have hOneLe :
      1 ≤ 2 ^ S.suffixHenselDelta i := by
    omega
  rw [Nat.cast_sub hOneLe]
  push_cast
  norm_num

/--
cut `b+i` から長さ `r` の straight tail を common dyadic factor で割った unit。

forward recurrence は右端 column を一つ追加する形に合わせる。
-/
noncomputable def suffixHenselUnit
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) : ℕ → ℤ
  | 0 => 0
  | r + 1 =>
      3 * S.suffixHenselUnit i r +
        (2 : ℤ) ^ r * S.suffixHenselForcing (i + r)

@[simp] theorem suffixHenselUnit_zero
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i : ℕ) :
    S.suffixHenselUnit i 0 = 0 := rfl

/-- `suffixHenselUnit` の forward recurrence。 -/
theorem suffixHenselUnit_succ
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i r : ℕ) :
    S.suffixHenselUnit i (r + 1) =
      3 * S.suffixHenselUnit i r +
        (2 : ℤ) ^ r * S.suffixHenselForcing (i + r) := rfl

/--
同じ unit を左端 column と残り suffix に分ける recurrence。

  G_i(r+1) = 3^r forcing_i + 2 G_(i+1)(r)
-/
theorem suffixHenselUnit_left_rec
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i r : ℕ) :
    S.suffixHenselUnit i (r + 1) =
      (3 : ℤ) ^ r * S.suffixHenselForcing i +
        2 * S.suffixHenselUnit (i + 1) r := by
  induction r with
  | zero =>
      simp [suffixHenselUnit_succ]
  | succ r ih =>
      rw [suffixHenselUnit_succ S i (r + 1)]
      rw [ih]
      rw [suffixHenselUnit_succ S (i + 1) r]
      have hIdx : i + (r + 1) = (i + 1) + r := by omega
      rw [hIdx, pow_succ]
      ring

/-- straight component 内の一列 mass の exact dyadic factorization。 -/
theorem profileRightmostColumnMass_cast_eq_suffixHenselTerm
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i r : ℕ}
    (hir : i + r < S.width) :
    (profileRightmostColumnMass P.h (S.b + i + r) : ℤ) =
      (2 : ℤ) ^ S.suffixHenselBase i *
        (2 : ℤ) ^ r *
          S.suffixHenselForcing (i + r) := by
  have hcEq := S.terminalCriticalStart_eq_b_add_width
  have hkC : S.b + i + r < P.terminalCriticalStart := by
    rw [hcEq]
    omega
  have hCheckpoint :=
    S.checkpoint_line
      (k := S.b + i + r)
      (by omega)
      hkC
  have hDiff : S.b + i + r - S.b = i + r := by omega
  have hCheckpoint' :
      beattyIndex (S.b + i + r) - P.h (S.b + i + r) =
        S.suffixHenselBase (i + r) := by
    simpa [profileCheckpoint, suffixHenselBase, hDiff, Nat.add_assoc] using
      hCheckpoint
  have hLine0 :=
    singleCornerLine_lt_beatty
      (b := S.b) (n := i + r) S.beattyIndex_b_pos
  have hLine :
      S.suffixHenselBase (i + r) <
        beattyIndex (S.b + i + r) := by
    simpa [suffixHenselBase, Nat.add_assoc] using hLine0
  have hFactor :=
    twoPow_sub_twoPow_eq_factor
      (a := S.suffixHenselBase (i + r))
      (b := beattyIndex (S.b + i + r))
      (Nat.le_of_lt hLine)
  have hMassNat :
      profileRightmostColumnMass P.h (S.b + i + r) =
        2 ^ S.suffixHenselBase (i + r) *
          (2 ^ S.suffixHenselDelta (i + r) - 1) := by
    unfold profileRightmostColumnMass
    rw [hCheckpoint']
    simpa [suffixHenselDelta, Nat.add_assoc] using hFactor
  rw [hMassNat]
  push_cast
  rw [S.suffixHenselBase_add i r]
  rw [pow_add]
  unfold suffixHenselForcing
  ring

/--
straight tail 自身は common dyadic base と `suffixHenselUnit` の積に exact 分解する。
-/
theorem restartedClosedTailZ_eq_pow_mul_suffixHenselUnit
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i r : ℕ}
    (hir : i + r ≤ S.width) :
    restartedClosedTailZ P (S.b + i) (S.b + i + r) =
      (2 : ℤ) ^ S.suffixHenselBase i *
        S.suffixHenselUnit i r := by
  induction r with
  | zero =>
      simp [restartedClosedTailZ]
  | succ r ih =>
      have hirPrev : i + r ≤ S.width := by omega
      have hirMass : i + r < S.width := by omega
      have hIH := ih hirPrev
      have hTailRec :=
        restartedClosedTailZ_succ P
          (b := S.b + i)
          (c := S.b + i + r)
          (by omega)
      have hIndex :
          S.b + i + r + 1 = S.b + i + (r + 1) := by omega
      rw [hIndex] at hTailRec
      have hMass :=
        S.profileRightmostColumnMass_cast_eq_suffixHenselTerm
          (i := i) (r := r) hirMass
      rw [hTailRec, hMass, hIH]
      rw [suffixHenselUnit_succ]
      ring

/--
actual restarted straight component の任意 suffix unit は
local width と同じ深さの `3` 冪で割れる。
-/
theorem suffixHenselUnit_threePow_dvd
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i ≤ S.width) :
    (3 : ℤ) ^ (S.width - i) ∣
      S.suffixHenselUnit i (S.width - i) := by
  have hcEq := S.terminalCriticalStart_eq_b_add_width
  have hCritB : P.criticalizationStart ≤ S.b := by
    have hCrit := S.criticalization_le_previous
    have hGap := S.previous_succ_lt_b
    omega
  have hsk : P.criticalizationStart ≤ S.b + i := by omega
  have hkc : S.b + i ≤ P.terminalCriticalStart := by
    rw [hcEq]
    omega
  have hDeep :=
    restartedTail_localWidth_dvd P hStart hsk hkc
  have hExp :
      P.terminalCriticalStart - (S.b + i) =
        S.width - i := by
    rw [hcEq]
    omega
  rw [hExp] at hDeep
  have hFactor :=
    S.restartedClosedTailZ_eq_pow_mul_suffixHenselUnit
      (i := i) (r := S.width - i) (by omega)
  have hEnd :
      S.b + i + (S.width - i) =
        P.terminalCriticalStart := by
    rw [hcEq]
    omega
  rw [hEnd] at hFactor
  rw [hFactor] at hDeep
  exact MonotoneSuffixHenselChain.threePow_dvd_cancel_twoPow hDeep

/--
full suffix divisibility から選ぶ normalized quotient。

`i <= width` では

  G_i(width-i) = 3^(width-i) * q_i

を exact に満たす。
-/
noncomputable def suffixHenselQuotient
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (i : ℕ) : ℤ :=
  if hi : i ≤ S.width then
    Classical.choose (S.suffixHenselUnit_threePow_dvd hStart hi)
  else
    0

/-- `suffixHenselQuotient` の defining divisibility equation。 -/
theorem suffixHenselQuotient_spec
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i ≤ S.width) :
    S.suffixHenselUnit i (S.width - i) =
      (3 : ℤ) ^ (S.width - i) *
        S.suffixHenselQuotient hStart i := by
  unfold suffixHenselQuotient
  simp only [dite_eq_left hi]
  exact
    Classical.choose_spec
      (S.suffixHenselUnit_threePow_dvd hStart hi)

/-- terminal empty suffix の quotient は `0`。 -/
theorem suffixHenselQuotient_terminal
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    S.suffixHenselQuotient hStart S.width = 0 := by
  have hSpec :=
    S.suffixHenselQuotient_spec hStart (i := S.width) le_rfl
  have hSpec' := hSpec.symm
  simpa [suffixHenselUnit] using hSpec'

/--
隣接 suffix quotient は pure Hensel recurrence を exact に満たす。
-/
theorem suffixHenselQuotient_recurrence
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < S.width) :
    3 * S.suffixHenselQuotient hStart i =
      2 * S.suffixHenselQuotient hStart (i + 1) +
        (2 : ℤ) ^ S.suffixHenselDelta i - 1 := by
  let r : ℕ := S.width - (i + 1)
  have hiLe : i ≤ S.width := by omega
  have hi1Le : i + 1 ≤ S.width := by omega
  have hSplit : S.width - i = r + 1 := by
    dsimp [r]
    omega
  have hQi := S.suffixHenselQuotient_spec hStart hiLe
  have hQnext := S.suffixHenselQuotient_spec hStart hi1Le
  have hQi' :
      S.suffixHenselUnit i (r + 1) =
        (3 : ℤ) ^ (r + 1) *
          S.suffixHenselQuotient hStart i := by
    rw [← hSplit]
    exact hQi
  have hQnext' :
      S.suffixHenselUnit (i + 1) r =
        (3 : ℤ) ^ r *
          S.suffixHenselQuotient hStart (i + 1) := by
    simpa [r] using hQnext
  have hG := S.suffixHenselUnit_left_rec i r
  rw [hQi', hQnext'] at hG
  rw [pow_succ] at hG
  have hZero :
      (3 : ℤ) ^ r *
          (3 * S.suffixHenselQuotient hStart i -
            S.suffixHenselForcing i -
            2 * S.suffixHenselQuotient hStart (i + 1)) = 0 := by
    calc
      (3 : ℤ) ^ r *
          (3 * S.suffixHenselQuotient hStart i -
            S.suffixHenselForcing i -
            2 * S.suffixHenselQuotient hStart (i + 1)) =
        ((3 : ℤ) ^ r * 3) *
            S.suffixHenselQuotient hStart i -
          ((3 : ℤ) ^ r * S.suffixHenselForcing i +
            2 * ((3 : ℤ) ^ r *
              S.suffixHenselQuotient hStart (i + 1))) := by
              ring
      _ = 0 := by
        rw [hG]
        ring
  have hCore :
      3 * S.suffixHenselQuotient hStart i -
          S.suffixHenselForcing i -
          2 * S.suffixHenselQuotient hStart (i + 1) = 0 := by
    rcases mul_eq_zero.mp hZero with hPowZero | hCoreZero
    · have hNonzero : (3 : ℤ) ^ r ≠ 0 := by positivity
      exact (hNonzero hPowZero).elim
    · exact hCoreZero
  have hForce := S.suffixHenselForcing_eq i
  rw [hForce] at hCore
  linarith

/--
actual restarted packet から純粋な `MonotoneSuffixHenselChain` を構成する。

この theorem が geometry / arithmetic の境界であり、返り値以降は
Collatz / Ferrers / Beatty の情報を使わずに議論できる。
-/
noncomputable def toMonotoneSuffixHenselChain
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    MonotoneSuffixHenselChain where
  width := S.width
  width_pos := S.width_pos
  delta := S.suffixHenselDelta
  q := S.suffixHenselQuotient hStart
  delta_zero := S.suffixHenselDelta_zero
  delta_step := by
    intro i _hi
    exact S.suffixHenselDelta_succ_eq_self_or_add_one i
  q_terminal := S.suffixHenselQuotient_terminal hStart
  recurrence := by
    intro i hi
    exact S.suffixHenselQuotient_recurrence hStart hi

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
