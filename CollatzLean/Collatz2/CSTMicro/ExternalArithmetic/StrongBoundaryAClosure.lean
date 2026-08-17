import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.StrongTwoLogDyadicSlack

/-!
# Boundary A closure with strong certified precision

strong matching

  e <= q_j + q_{j+1} - 1

を使って、current coarse window を通さず直接 A branch を閉じる。

このファイルまでの plumbing は純 Lean / finite arithmetic であり、
残る本質的な外部・組合せ論入力は

* `StrongBoundaryLopezStollMatch.xiTargetAgreement`
* `StrongTwoLogDyadicSlack`
* finite initial check

の三つになる。

特に strong matching の実証が入れば、最初の finite cutoff は
`strongFirstPrecision L = q_{start-1}+q_start-1` になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
strong windows + strong matching + height squeeze から、
十分大きい precision の small BoundaryXiCandidate は存在しない。
-/
theorem no_small_boundaryXiCandidate_eventually_strong
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (M : StrongBoundaryLopezStollMatch L)
    {B : ℕ → ℕ}
    (hSqueeze : StrongWindowHeightSqueeze C B)
    {e R : ℕ}
    (hLarge : strongFirstPrecision L ≤ e)
    (hR : R ≤ B e)
    (hCandidate : BoundaryXiCandidate e R) :
    False := by
  have hStartOne : 1 ≤ L.start := by
    exact le_trans (by decide : 1 ≤ 3) L.start_ge_three
  have hLow :
      strongDenominatorWindowLower L.q L.start ≤ e := by
    simpa [strongFirstPrecision] using hLarge
  have hCofinal :
      ∀ N : ℕ, ∃ j : ℕ,
        L.start ≤ j ∧
          N ≤ strongDenominatorWindowUpper L.q j :=
    strongDenominatorWindowUpper_cofinal_of_q_cofinal
      L.q L.q_cofinal
  rcases exists_strongDenominatorWindow_cofinal
      L.q hStartOne hLow hCofinal with
    ⟨j, hjStart, hLower, hUpper⟩
  have hPacketMatch : (L.packet j).Matches e R := by
    change MatchesAtTwoPower e (L.P j) (L.Q j) R
    exact M.xiTargetAgreement j e R hjStart hUpper hCandidate
  have hHeight :
      HasChristoffelHeightBound C.H (L.packet j).q
        (L.packet j).P (L.packet j).Q := by
    simpa [LopezStollInstantiation.packet] using C.height j
  have hSq0 := hSqueeze j e hjStart hLower hUpper
  have hSq :
      (C.H * (L.packet j).q * 2 ^ (L.packet j).q) *
          (B e + 1) < 2 ^ e := by
    simpa [LopezStollInstantiation.packet] using hSq0
  exact noSmallResidue_of_height_squeeze
    (L.packet j)
    hPacketMatch hHeight hR hSq

/-- large precision の critical boundary failure を strong route で排除する。 -/
theorem no_large_critical_boundary_failure_strong
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (M : StrongBoundaryLopezStollMatch L)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A *
            (2 ^ H - 3 ^ p))
    (S :
      StrongTwoLogDyadicSlack
        C (boundaryFailureResidueBound K A))
    {v : ParityWord}
    (hBoundary : IsFerrersBoundary v)
    (hLarge : strongFirstPrecision L ≤ v.length - 1) :
    WordPureSeparation v := by
  by_contra hFailure
  have hR :
      leastRepresentative v ≤
        boundaryFailureResidueBound K A (v.length - 1) :=
    ferrersBoundary_representative_le_failureBound
      hBoundary hGap hFailure
  have hCandidate :
      BoundaryXiCandidate
        (v.length - 1)
        (leastRepresentative v) :=
    ferrersBoundary_isBoundaryXiCandidate hBoundary
  exact
    no_small_boundaryXiCandidate_eventually_strong
      C M S.toStrongWindowHeightSqueeze
      hLarge hR hCandidate

/--
strong certified precision を使う nontrivial Boundary A 全排除。

finite side は

  e < q_{start-1}+q_start-1

だけ確認すればよい。
-/
theorem boundaryA_eliminated_from_strong_actual_family
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (M : StrongBoundaryLopezStollMatch L)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A *
            (2 ^ H - 3 ^ p))
    (S :
      StrongTwoLogDyadicSlack
        C (boundaryFailureResidueBound K A))
    (hFinite :
      ∀ v : ParityWord,
        IsFerrersBoundary v →
        2 < v.length →
        v.length - 1 < strongFirstPrecision L →
        WordPureSeparation v) :
    ∀ v : ParityWord,
      IsFerrersBoundary v →
      2 < v.length →
      WordPureSeparation v := by
  intro v hBoundary hNontrivial
  by_cases hLarge : strongFirstPrecision L ≤ v.length - 1
  · exact
      no_large_critical_boundary_failure_strong
        C M hGap S hBoundary hLarge
  · have hSmall : v.length - 1 < strongFirstPrecision L := by
      omega
    exact hFinite v hBoundary hNontrivial hSmall

end ExternalArithmetic
end CSTMicro
end Collatz2
