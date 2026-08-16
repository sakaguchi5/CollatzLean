import CollatzLean.Collatz2.CSTMicro.FerrersChain

/-!
# General CST: first-passage preservation along Ferrers chains

`01 -> 10` は一つの proper prefix height だけを上げる。
したがって first-passage condition は Ferrers order の上向き cover で保存される。

これにより boundary から target までの chain の全 intermediate word が
同じ first-passage admissible class に残る。
-/

namespace Collatz2
namespace CSTMicro

/-- `01 -> 10` は全 prefix odd count を弱く増加させる。 -/
theorem prefixOddCount_swap_le
    (left right : ParityWord)
    (j : ℕ) :
    prefixOddCount (left ++ ([false, true] ++ right)) j ≤
      prefixOddCount (left ++ ([true, false] ++ right)) j := by
  induction left generalizing j with
  | nil =>
      cases j with
      | zero =>
          simp [prefixOddCount]
      | succ j =>
          cases j with
          | zero =>
              simp [prefixOddCount_cons_succ, bitNat]
          | succ j =>
              simp [prefixOddCount_cons_succ, bitNat]
  | cons b left ih =>
      cases j with
      | zero =>
          simp [prefixOddCount]
      | succ j =>
          simp only [List.cons_append, prefixOddCount_cons_succ]
          exact Nat.add_le_add_left (ih j) (bitNat b)

namespace AdjacentFerrersSwap

/-- edge packet 版 prefix dominance。 -/
theorem prefixOddCount_lower_le_upper
    (S : AdjacentFerrersSwap)
    (j : ℕ) :
    prefixOddCount S.lowerWord j ≤ prefixOddCount S.upperWord j := by
  exact prefixOddCount_swap_le S.leftContext S.rightContext j

end AdjacentFerrersSwap

namespace FerrersStep

/-- adjacent Ferrers cover は first-passage を保存する。 -/
theorem preserves_firstPassage
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLower : IsFirstPassageWord lower) :
    IsFirstPassageWord upper := by
  have hLowerEdge : IsFirstPassageWord S.edge.lowerWord := by
    simpa [S.lower_eq] using hLower
  have hUpperEdge : IsFirstPassageWord S.edge.upperWord := by
    constructor
    · simp [AdjacentFerrersSwap.upperWord]
    · constructor
      · intro k hkPos hkLt
        have hkLower : k < S.edge.lowerWord.length := by
          have hkEdge : k < S.edge.length := by
            simpa [S.edge.upperWord_length] using hkLt
          simpa [S.edge.lowerWord_length] using hkEdge
        have hExp := hLowerEdge.2.1 k hkPos hkLower
        unfold CoefficientExpandingAt at hExp ⊢
        have hCount := S.edge.prefixOddCount_lower_le_upper k
        have hPow :
            3 ^ prefixOddCount S.edge.lowerWord k ≤
              3 ^ prefixOddCount S.edge.upperWord k :=
          Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hCount
        exact lt_of_lt_of_le hExp hPow
      · have hContract := hLowerEdge.2.2
        unfold CoefficientContracting at hContract ⊢
        simpa using hContract
  simpa [S.upper_eq] using hUpperEdge

end FerrersStep

namespace FerrersChain

/-- boundary から上向きに進む chain の全 endpoint は first-passage のまま。 -/
theorem preserves_firstPassage
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStart : IsFirstPassageWord start) :
    IsFirstPassageWord finish := by
  induction C with
  | refl =>
      exact hStart
  | step C S ih =>
      exact S.preserves_firstPassage ih
end FerrersChain

/--
任意の first-passage target は、first-passage boundary から
first-passage を保つ Ferrers chain を持つ。
-/
theorem exists_admissible_ferrersBoundary_chain
    {target : ParityWord}
    (hTarget : IsFirstPassageWord target) :
    ∃ boundary : ParityWord,
      IsFerrersBoundary boundary ∧
        Nonempty (FerrersChain boundary target) ∧
        IsFirstPassageWord boundary := by
  rcases exists_ferrersBoundary_chain hTarget with
    ⟨boundary, hBoundary, hChain⟩
  exact ⟨boundary, hBoundary, hChain, hBoundary.1⟩

end CSTMicro
end Collatz2
