import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTopCellDeltaB
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ExtraDepthFerrersTransport

/-!
# Pure B: actual word と pure profile の座標 bridge

`toPureBProfileObstruction` の profile は actual minimal bad word の
`parityExtraDepth` そのものであり、odd depth `m` も actual word の odd count と一致する。

terminal top cell を actual Ferrers predecessor として実現する前に、
この二つを public wrapper として固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/-- pure profile は actual minimal bad word の extra-depth profile そのもの。 -/
@[simp] theorem toPureBProfileObstruction_h_apply
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (k : ℕ) :
    (M.toPureBProfileObstruction hL).h k =
      parityExtraDepth M.word k := by
  rfl

/-- pure odd depth `m` は actual minimal bad word の odd count。 -/
theorem toPureBProfileObstruction_m_eq_wordOddCount
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).m = oddCount M.word := by
  change
    Collatz2.Word.oddSteps M.actual.firstFailureEdge.upperExponentWord =
      oddCount M.word
  rw [M.actual.firstFailureEdge.upperExponentWord_oddSteps]
  have hUpper :
      M.actual.firstFailureEdge.step.edge.upperWord = M.word := by
    unfold ActualABObstructionPacket.firstFailureEdge
    unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge
    unfold FirstFailureProvenance.toFirstFailureEdge
    dsimp
    exact M.failureStep_upperWord_eq_word
  calc
    M.actual.firstFailureEdge.step.edge.oddTotal
        = oddCount M.actual.firstFailureEdge.step.edge.upperWord :=
      M.actual.firstFailureEdge.step.edge.upperWord_oddCount.symm
    _ = oddCount M.word := congrArg oddCount hUpper

end MinimalActualABObstructionPacket

/-!
## 汎用補助: k 番目の odd で parity word を分解
-/

/-- `k < oddCount v` なら、`k` 個の odd の直後に次の `true` を切り出せる。 -/
theorem exists_append_true_of_lt_oddCount
    (v : ParityWord)
    {k : ℕ}
    (hk : k < oddCount v) :
    ∃ left right : ParityWord,
      v = left ++ true :: right ∧
      oddCount left = k := by
  induction v generalizing k with
  | nil =>
      simp [oddCount] at hk
  | cons b v ih =>
      cases b with
      | false =>
          have hk' : k < oddCount v := by
            simpa [oddCount, bitNat] using hk
          rcases ih hk' with ⟨left, right, hv, hodd⟩
          refine ⟨false :: left, right, ?_, ?_⟩
          · simp [hv]
          · simpa [oddCount, bitNat] using hodd
      | true =>
          by_cases hk0 : k = 0
          · subst k
            exact ⟨[], v, rfl, by simp [oddCount]⟩
          · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
            have hk' :
                j + 1 < 1 + oddCount v := by
              simpa [oddCount, bitNat, Nat.succ_eq_add_one] using hk
            have hj : j < oddCount v := by
              omega
            rcases ih hj with ⟨left, right, hv, hodd⟩
            refine ⟨true :: left, right, ?_, ?_⟩
            · simp [hv]
            · calc
                oddCount (true :: left)
                    = 1 + oddCount left := by
                        simp [oddCount, bitNat]
                _ = 1 + j := by
                      rw [hodd]
                _ = j + 1 := by
                      omega

namespace FerrersStep

/--
upper first-passage と selected lower-prefix の一段 slack があれば、
`10 -> 01` で下げた lower も first-passage。

terminal top cell の actual realization で使う downward preservation lemma。
-/
theorem lower_firstPassage_of_upper_and_rankCellSlack
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hUpper : IsFirstPassageWord upper)
    (hSlack :
      2 ^ (S.edge.position + 1) < 3 ^ S.edge.rankCut) :
    IsFirstPassageWord lower := by
  constructor
  · intro hnil
    have hProper :=
      S.rankCell_position_succ_lt_lower_length
    have hLen : lower.length = 0 := by
      simp only [hnil, List.length_nil]
    omega
  · constructor
    · intro j hjPos hjLt
      unfold CoefficientExpandingAt
      by_cases hspecial : j = S.edge.position + 1
      · subst j
        rw [S.lower_prefixOddCount_at_rankCell]
        exact hSlack
      · obtain ⟨i, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjPos)
        have hi : i ≠ S.edge.position := by
          omega
        have hCount :=
          S.prefixOddCount_upper_eq_lower_of_ne_rankCellPosition hi
        have hUpperLt : i + 1 < upper.length := by
          rw [← S.length_eq]
          exact hjLt
        have hExp := hUpper.2.1 (i + 1) (by omega) hUpperLt
        unfold CoefficientExpandingAt at hExp
        rw [← hCount]
        exact hExp
    · have hTerminal := hUpper.2.2
      unfold CoefficientContracting at hTerminal ⊢
      rw [S.length_eq, S.oddCount_eq]
      exact hTerminal

end FerrersStep

end ExternalArithmetic
end CSTMicro
end Collatz2
