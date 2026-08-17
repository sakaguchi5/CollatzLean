import CollatzLean.Collatz2.CSTMicro.BoundaryXiTruncation
import CollatzLean.Collatz2.CSTMicro.CarryCorridorExtraction
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.TwoLogDyadicSlack

/-!
# Boundary A: critical Sturmian boundary -> integer-residue candidate

A branch は canonical critical Sturmian boundary 自身が
`WordPureSeparation` に失敗する場合。

このファイルでは

1. boundary least representative を `Candidate(e,R)` にする、
2. boundary failure から `R` の polynomial bound を得る、
3. actual López--Stoll family の candidate matching と
   two-log dyadic slack があれば large A failure を排除する、
4. 残る有限初期範囲を確認すれば nontrivial A branch 全体を排除する、

ところまで接続する。

ここで precision は exact に

  e = length - 1 = beattyIndex(endpointOddCount)

である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
critical Ξ finite truncation と一致する nonnegative integer residue。

無限 `Ξ` を構成せず、既存 `BoundaryXiTruncation` の finite class だけで持つ。
-/
def BoundaryXiCandidate (e R : ℕ) : Prop :=
  ∃ m : ℕ,
    e = beattyIndex m ∧
      R % (2 ^ e) =
        (criticalXiTruncationClass e m).val

/-- Ferrers boundary の least representative は canonical candidate。 -/
theorem ferrersBoundary_isBoundaryXiCandidate
    {v : ParityWord}
    (h : IsFerrersBoundary v) :
    BoundaryXiCandidate
      (v.length - 1)
      (leastRepresentative v) := by
  refine ⟨oddCount v, ?_, ?_⟩
  · exact
      ferrersBoundary_length_pred_eq_beattyIndex_oddCount h
  · have hres :=
      ferrersBoundary_leastRepresentative_mod_eq_xiTruncation_val h
    simpa using hres

/--
boundary failure 用の exact polynomial residue bound。

`e = k-1` なので既存 length bound
`K*(k+1)^(A+1)` は
`K*(e+2)^(A+1)` になる。
-/
def boundaryFailureResidueBound
    (K A e : ℕ) : ℕ :=
  K * (e + 2) ^ (A + 1)

private theorem natPow_le_natPow_of_le
    {a b : ℕ}
    (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact
        Nat.mul_le_mul
          (natPow_le_natPow_of_le hab n)
          hab

/-- boundary failure residue bound は precision に関して単調。 -/
theorem boundaryFailureResidueBound_mono
    (K A : ℕ) :
    NatBoundMonotone (boundaryFailureResidueBound K A) := by
  intro a b hab
  unfold boundaryFailureResidueBound
  have hbase : a + 2 ≤ b + 2 := by omega
  have hpow :
      (a + 2) ^ (A + 1) ≤
        (b + 2) ^ (A + 1) :=
    natPow_le_natPow_of_le hbase (A + 1)
  exact Nat.mul_le_mul_left K hpow

/--
canonical boundary が separation failure なら、
その least representative は
`boundaryFailureResidueBound K A e` 以下。
-/
theorem ferrersBoundary_representative_le_failureBound
    {v : ParityWord}
    (hBoundary : IsFerrersBoundary v)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A *
            (2 ^ H - 3 ^ p))
    (hFailure : ¬ WordPureSeparation v) :
    leastRepresentative v ≤
      boundaryFailureResidueBound
        K A (v.length - 1) := by
  let P : FirstPassagePath :=
    firstPassagePathOfWord v hBoundary.1
  have hPword : P.word = v := rfl
  have hPlength : P.length = v.length := rfl
  have hFailureP :
      ¬ WordPureSeparation P.word := by
    simpa [hPword] using hFailure
  have hEndpoint :=
    FirstFailureEdge.representative_le_endpointPolynomial_of_failure
      P hFailureP hGap
  have hLength :=
    FirstFailureEdge.endpointPolynomial_le_simpleLengthPolynomial
      P K A
  have hBound :
      leastRepresentative P.word ≤
        K * (P.length + 1) ^ (A + 1) :=
    le_trans hEndpoint hLength
  rw [hPword, hPlength] at hBound
  have hlenPos : 0 < v.length :=
    List.length_pos_of_ne_nil hBoundary.1.1
  have heq :
      (v.length - 1) + 2 = v.length + 1 := by
    omega
  unfold boundaryFailureResidueBound
  rw [heq]
  exact hBound

/--
actual López--Stoll corrected approximants が
boundary Ξ candidate と同じ 2-adic target を近似する、という bridge。

原論文 Lemma 21 + finite truncation tail valuation を
移植するときに埋める唯一の matching field。
-/
structure BoundaryLopezStollMatch
    (F : CriticalResidueApproximationFamily) where
  xiTargetAgreement :
    F.CandidateMatches BoundaryXiCandidate

/--
large precision の A failure は abstract separation engine で排除される。
-/
theorem no_large_critical_boundary_failure
    (F : CriticalResidueApproximationFamily)
    (M : BoundaryLopezStollMatch F)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A *
            (2 ^ H - 3 ^ p))
    (S :
      TwoLogDyadicSlack
        F (boundaryFailureResidueBound K A))
    {v : ParityWord}
    (hBoundary : IsFerrersBoundary v)
    (hLarge : F.firstPrecision ≤ v.length - 1) :
    WordPureSeparation v := by
  by_contra hFailure
  have hR :
      leastRepresentative v ≤
        boundaryFailureResidueBound
          K A (v.length - 1) :=
    ferrersBoundary_representative_le_failureBound
      hBoundary hGap hFailure
  have hCandidate :
      BoundaryXiCandidate
        (v.length - 1)
        (leastRepresentative v) :=
    ferrersBoundary_isBoundaryXiCandidate hBoundary
  exact
    F.no_small_candidate_eventually
      M.xiTargetAgreement
      S.toWindowHeightSqueeze
      hLarge
      hR
      hCandidate

/--
nontrivial A branch 全排除。

large precision は López--Stoll + height + two-log engine で落とし、
`e < firstPrecision` の有限個だけ直接確認する。

`length > 2` を入れるのは `0`, `10` という strict-separation の
trivial exceptions を除くため。
-/
theorem boundaryA_eliminated_of_finite_check
    (F : CriticalResidueApproximationFamily)
    (M : BoundaryLopezStollMatch F)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A *
            (2 ^ H - 3 ^ p))
    (S :
      TwoLogDyadicSlack
        F (boundaryFailureResidueBound K A))
    (hFinite :
      ∀ v : ParityWord,
        IsFerrersBoundary v →
        2 < v.length →
        v.length - 1 < F.firstPrecision →
        WordPureSeparation v) :
    ∀ v : ParityWord,
      IsFerrersBoundary v →
      2 < v.length →
      WordPureSeparation v := by
  intro v hBoundary hNontrivial
  by_cases hLarge :
      F.firstPrecision ≤ v.length - 1
  · exact
      no_large_critical_boundary_failure
        F M hGap S hBoundary hLarge
  · have hSmall :
        v.length - 1 < F.firstPrecision := by
      omega
    exact hFinite v hBoundary hNontrivial hSmall

/--
actual instantiation 版。

`LopezStollInstantiation` + `ChristoffelHeightInstantiation` から family を作り、
matching / two-log / finite check を供給すれば A branch が消える。
-/
theorem boundaryA_eliminated_from_actual_family
    {L : LopezStollInstantiation}
    (C : ChristoffelHeightInstantiation L)
    (M :
      BoundaryLopezStollMatch
        C.toApproximationFamily)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A *
            (2 ^ H - 3 ^ p))
    (S :
      TwoLogDyadicSlack
        C.toApproximationFamily
        (boundaryFailureResidueBound K A))
    (hFinite :
      ∀ v : ParityWord,
        IsFerrersBoundary v →
        2 < v.length →
        v.length - 1 <
          C.toApproximationFamily.firstPrecision →
        WordPureSeparation v) :
    ∀ v : ParityWord,
      IsFerrersBoundary v →
      2 < v.length →
      WordPureSeparation v := by
  exact
    boundaryA_eliminated_of_finite_check
      C.toApproximationFamily
      M
      hGap
      S
      hFinite

end ExternalArithmetic
end CSTMicro
end Collatz2
