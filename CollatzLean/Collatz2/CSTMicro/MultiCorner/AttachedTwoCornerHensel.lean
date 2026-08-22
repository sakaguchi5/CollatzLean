import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedBranchDivisibility

/-!
# MultiCorner: attached two-corner Hensel interface

attached branch では previous exposed cut と terminal exposed cut が同じ positive corridor にあり、
その間には別の exposed cut がない。

このファイルでは

* terminal 側 two-corner geometry、
* actual endpoint と分離された carry-normalized gaps、
* normalized Hensel step の mod 3 residue

を一つの interface に固定する。

exposed を depth drop と同一視しない。内部 corner の本体は `carryRunGap >= 2`。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
attached two-corner の geometry packet。
`samePositiveCorridor` は previous から terminal まで同じ positive component にいることを表す。
-/
structure AttachedTwoCornerPacket
    (P : PureBProfileObstruction) where
  normalForm : LastTwoExposedNormalForm P
  terminalCriticalStart_pos : 0 < P.terminalCriticalStart
  terminal_eq :
    normalForm.terminal = P.terminalCriticalStart - 1
  criticalization_le_previous :
    P.criticalizationStart ≤ normalForm.previous
  samePositiveCorridor :
    ∀ k : ℕ,
      normalForm.previous ≤ k →
      k ≤ normalForm.terminal →
      0 < P.h k

namespace AttachedTwoCornerPacket

/-- previous cut は exposed proposition としても読める。 -/
theorem previous_isExposed
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    P.IsExposedPredecessorIndex A.normalForm.previous := by
  exact (P.mem_exposedPredecessorSet_iff).1 A.normalForm.previous_mem

/-- terminal cut も exposed proposition として読める。 -/
theorem terminal_isExposed
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    P.IsExposedPredecessorIndex A.normalForm.terminal := by
  exact (P.mem_exposedPredecessorSet_iff).1 A.normalForm.terminal_mem

/-- previous は arithmetic criticalization corridor の中にいる。 -/
theorem previous_mem_arithmeticCorridor
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    P.criticalizationStart ≤ A.normalForm.previous ∧
      A.normalForm.previous < P.terminalCriticalStart := by
  have hLeft := A.criticalization_le_previous
  have hPrevTerm := A.normalForm.previous_lt_terminal
  have hTermEq := A.terminal_eq
  have hcPos := A.terminalCriticalStart_pos
  constructor
  · exact hLeft
  · omega

/-- previous corner は carry corridor の strict interior にある。 -/
theorem previous_succ_lt_terminalCriticalStart
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    A.normalForm.previous + 1 < P.terminalCriticalStart := by
  have hPrevTerm := A.normalForm.previous_lt_terminal
  have hTermEq := A.terminal_eq
  have hcPos := A.terminalCriticalStart_pos
  omega

/-- attached internal corner の carry-normalized gap は少なくとも二。 -/
theorem two_le_previous_carryRunGap
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    2 ≤ carryRunGap
      P P.terminalCriticalStart A.normalForm.previous := by
  have E := A.previous_isExposed
  have hSucc := A.previous_succ_lt_terminalCriticalStart
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  exact two_le_carryRunGap_of_exposed_of_succ_lt P E hSucc hcM

/-- terminal cut は carry endpoint の直前。 -/
theorem terminal_succ_eq_terminalCriticalStart
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    A.normalForm.terminal + 1 = P.terminalCriticalStart := by
  have hTermEq := A.terminal_eq
  have hcPos := A.terminalCriticalStart_pos
  omega

/--
terminal exposed cut も normalized endpoint `beta(c)` に対して gap `>=2` を保つ。
full endpoint `H` の `+1` correction に頼らない形。
-/
theorem two_le_terminal_carryRunGap
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    2 ≤ carryRunGap
      P P.terminalCriticalStart A.normalForm.terminal := by
  have E := A.terminal_isExposed
  have hSucc := A.terminal_succ_eq_terminalCriticalStart
  have hPos : 0 < P.h A.normalForm.terminal :=
    A.samePositiveCorridor
      A.normalForm.terminal
      (le_of_lt A.normalForm.previous_lt_terminal)
      le_rfl
  have hBelow :=
    P.profileCheckpoint_succ_le_beatty_of_depth_pos E.lt_m hPos
  have hTermLt :
      A.normalForm.terminal < P.terminalCriticalStart := by
    omega
  have hBeatty :
      beattyIndex A.normalForm.terminal <
        beattyIndex P.terminalCriticalStart :=
    beattyIndex_strictMono hTermLt
  rw [carryRunGap_of_succ_eq P hSucc]
  omega

/-- two corners の間には exposed cut はない。 -/
theorem no_exposed_between
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {k : ℕ}
    (hPrev : A.normalForm.previous < k)
    (hTerm : k < A.normalForm.terminal) :
    k ∉ P.exposedPredecessorSet :=
  A.normalForm.no_exposed_between k hPrev hTerm

end AttachedTwoCornerPacket

/--
normalized right-carry/Hensel step を subtraction-free に書いた形。

  3x = 2^e xNext + 2^h - 1

と同値な

  3x + 1 = 2^e xNext + 2^h

を採用する。
-/
def NormalizedHenselStep
    (h e x xNext : ℕ) : Prop :=
  3 * x + 1 = 2 ^ e * xNext + 2 ^ h

/-- Nat の Hensel step を `ZMod 3` へ落とす。 -/
theorem normalizedHenselStep_mod_three
    {h e x xNext : ℕ}
    (H : NormalizedHenselStep h e x xNext) :
    (1 : ZMod 3) =
      (2 : ZMod 3) ^ e * (xNext : ZMod 3) +
        (2 : ZMod 3) ^ h := by
  unfold NormalizedHenselStep at H
  have hCast :=
    congrArg (fun n : ℕ => (n : ZMod 3)) H
  push_cast at hCast
  have hThree :
      (3 : ZMod 3) = 0 := by
    decide
  rw [hThree, zero_mul, zero_add] at hCast
  exact hCast

private theorem zmod3_twoPow_even
    (r : ℕ) :
    (2 : ZMod 3) ^ (2 * r) = 1 := by
  have hTwoSq :
      (2 : ZMod 3) ^ 2 = 1 := by
    decide
  rw [pow_mul, hTwoSq, one_pow]


private theorem zmod3_twoPow_odd
    (r : ℕ) :
    (2 : ZMod 3) ^ (2 * r + 1) = 2 := by
  rw [pow_succ, zmod3_twoPow_even]
  norm_num

/-- depth `h` が even なら next state は `0 mod 3`。 -/
theorem normalizedHenselStep_next_eq_zero_mod_three_of_even_depth
    {r e x xNext : ℕ}
    (H : NormalizedHenselStep (2 * r) e x xNext) :
    (xNext : ZMod 3) = 0 := by
  have H3 := normalizedHenselStep_mod_three H
  rw [zmod3_twoPow_even] at H3
  have hMul :
      (2 : ZMod 3) ^ e * (xNext : ZMod 3) = 0 := by
    have hEq :
        (2 : ZMod 3) ^ e * (xNext : ZMod 3) + 1 = 0 + 1 := by
      calc
        (2 : ZMod 3) ^ e * (xNext : ZMod 3) + 1
            = 1 := H3.symm
        _ = 0 + 1 := by
          norm_num
    exact add_right_cancel hEq
  have hTwoNe :
      (2 : ZMod 3) ≠ 0 := by
    decide
  have hSelfInv :
      (2 : ZMod 3) ^ e * (2 : ZMod 3) ^ e = 1 := by
    calc
      (2 : ZMod 3) ^ e * (2 : ZMod 3) ^ e
          = (2 : ZMod 3) ^ (e + e) := by
              rw [← pow_add]
      _ = (2 : ZMod 3) ^ (2 * e) := by
              congr 1
              omega
      _ = 1 := zmod3_twoPow_even e
  calc
    (xNext : ZMod 3)
        = 1 * (xNext : ZMod 3) := by simp
    _ =
      ((2 : ZMod 3) ^ e * (2 : ZMod 3) ^ e) *
        (xNext : ZMod 3) := by
          rw [hSelfInv]
    _ =
      (2 : ZMod 3) ^ e *
        ((2 : ZMod 3) ^ e * (xNext : ZMod 3)) := by
          ring
    _ = 0 := by
          rw [hMul]
          simp

/-- depth odd・gap odd なら next state は `1 mod 3`。 -/
theorem normalizedHenselStep_next_eq_one_mod_three_of_odd_depth_odd_gap
    {r q x xNext : ℕ}
    (H : NormalizedHenselStep (2 * r + 1) (2 * q + 1) x xNext) :
    (xNext : ZMod 3) = 1 := by
  have H3 := normalizedHenselStep_mod_three H
  rw [zmod3_twoPow_odd, zmod3_twoPow_odd] at H3
  have hEq :
      (2 : ZMod 3) * (xNext : ZMod 3) + 2 =
        (2 : ZMod 3) * 1 + 2 := by
    calc
      (2 : ZMod 3) * (xNext : ZMod 3) + 2 = 1 := H3.symm
      _ = (2 : ZMod 3) * 1 + 2 := by decide
  have hMul :
      (2 : ZMod 3) * (xNext : ZMod 3) =
        (2 : ZMod 3) * 1 :=
    add_right_cancel hEq
  have hTwoSq :
      (2 : ZMod 3) * 2 = 1 := by
    decide
  calc
    (xNext : ZMod 3)
        = 1 * (xNext : ZMod 3) := by
            simp
    _ =
      ((2 : ZMod 3) * 2) * (xNext : ZMod 3) := by
        rw [hTwoSq]
    _ =
      (2 : ZMod 3) *
        ((2 : ZMod 3) * (xNext : ZMod 3)) := by
          ring
    _ =
      (2 : ZMod 3) * ((2 : ZMod 3) * 1) := by
        rw [hMul]
    _ =
      ((2 : ZMod 3) * 2) * 1 := by
        ring
    _ = 1 := by
        rw [hTwoSq]
        simp

/-- depth odd・gap even なら next state は `2 mod 3`。 -/
theorem normalizedHenselStep_next_eq_two_mod_three_of_odd_depth_even_gap
    {r q x xNext : ℕ}
    (H : NormalizedHenselStep (2 * r + 1) (2 * q) x xNext) :
    (xNext : ZMod 3) = 2 := by
  have H3 := normalizedHenselStep_mod_three H
  rw [zmod3_twoPow_even, zmod3_twoPow_odd] at H3
  have hEq :
      (xNext : ZMod 3) + 2 = (2 : ZMod 3) + 2 := by
    calc
      (xNext : ZMod 3) + 2 = 1 := by
        simpa using H3.symm
      _ = (2 : ZMod 3) + 2 := by decide
  exact add_right_cancel hEq

/--
attached internal corner で後段 Hensel scanner が見る最小 state。
geometry 由来の `h/e` と arithmetic state `x/xNext` を同じ packet に置く。
-/
structure AttachedCornerHenselState
    (P : PureBProfileObstruction)
    (A : AttachedTwoCornerPacket P) where
  x : ℕ
  xNext : ℕ
  step :
    NormalizedHenselStep
      (P.h A.normalForm.previous)
      (carryRunGap P P.terminalCriticalStart A.normalForm.previous)
      x xNext

end MultiCorner
end CSTMicro
end Collatz2
