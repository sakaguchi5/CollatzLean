import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualFerrersSuffixDecomposition
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelDefectValuation
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselChain
import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicActualWord


/-!
# actual Ferrers suffix: 3-adic corridor

whole actual Ferrers deficit の exact 3-adic order を `v` とし、

  s = p - v

と置く。

このファイルでは `s <= k <= p` の任意 cut に対して actual suffix が

  2^prefixDepth(k) * 3^(p-k)

で割れることを、PureB profile を経由せず actual word から直接証明する。

定義は増やしすぎず、最終的に後段 Hensel bridge が使う quotient function を
`ActualFerrersIntegralCorridor` として一度だけ束ねる。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

open ExternalArithmetic

/-- exponent が小さい power は大きい power を割る。 -/
private theorem intPow_dvd_intPow_of_le
    (a : ℤ)
    {r R : ℕ}
    (h : r ≤ R) :
    a ^ r ∣ a ^ R := by
  refine ⟨a ^ (R - r), ?_⟩
  have hExp : R = r + (R - r) := by omega
  rw [hExp, pow_add]
  simp only [add_tsub_cancel_left]

/-- 一列 deficit はその右側 `3` weight を必ず因子に持つ。 -/
theorem actualFerrersColumn_threePow_dvd
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    (3 : ℤ) ^ (Word.oddSteps w - (k + 1)) ∣
      actualFerrersColumnDeficitZ w k := by
  rw [actualFerrersColumnDeficitZ_eq_factor C.2 hk]
  refine ⟨
    (2 : ℤ) ^ Word.prefixTwoDepth w k *
      ((2 : ℤ) ^ Word.criticalDefect w k - 1), ?_⟩
  ring

/--
左 prefix `[0,k)` は少なくとも `3^(p-k)` を持つ。
これは各 earlier column の 3-weight だけから出る。
-/
theorem actualFerrersPrefixSegment_threePow_dvd
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {k : ℕ}
    (hk : k ≤ Word.oddSteps w) :
    (3 : ℤ) ^ (Word.oddSteps w - k) ∣
      actualFerrersSegmentDeficitZ w 0 k := by
  induction k with
  | zero =>
      simp [actualFerrersSegmentDeficitZ, actualFerrersBandsSegment,
        integerFerrersDeficit]
  | succ k ih =>
      have hkLt : k < Word.oddSteps w := by omega
      have hPrev := ih (by omega : k ≤ Word.oddSteps w)
      have hExpLe :
          Word.oddSteps w - (k + 1) ≤ Word.oddSteps w - k := by
        omega
      have hPowDvd :
          (3 : ℤ) ^ (Word.oddSteps w - (k + 1)) ∣
            (3 : ℤ) ^ (Word.oddSteps w - k) :=
        intPow_dvd_intPow_of_le 3 hExpLe
      have hPrevSmall :
          (3 : ℤ) ^ (Word.oddSteps w - (k + 1)) ∣
            actualFerrersSegmentDeficitZ w 0 k :=
        dvd_trans hPowDvd hPrev
      have hColumn := actualFerrersColumn_threePow_dvd C hkLt
      rw [actualFerrersSegmentDeficitZ_succ_right]
      simpa using dvd_add hPrevSmall hColumn

/--
valid actual word の interval suffix は左端 prefix depth の `2` power を持つ。
後続 prefix depth が strict に増えることだけを使う。
-/
theorem actualFerrersSegment_twoPow_dvd
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (start n : ℕ)
    (hEnd : start + n ≤ Word.oddSteps w) :
    (2 : ℤ) ^ Word.prefixTwoDepth w start ∣
      actualFerrersSegmentDeficitZ w start n := by
  induction n generalizing start with
  | zero =>
      simp [actualFerrersSegmentDeficitZ, actualFerrersBandsSegment,
        integerFerrersDeficit]
  | succ n ih =>
      have hStartLt : start < Word.oddSteps w := by omega
      have hNextEnd : start + 1 + n ≤ Word.oddSteps w := by omega
      have hColumnFactor :=
        actualFerrersColumnDeficitZ_eq_factor C.2 hStartLt
      have hColumn :
          (2 : ℤ) ^ Word.prefixTwoDepth w start ∣
            actualFerrersColumnDeficitZ w start := by
        rw [hColumnFactor]
        refine ⟨
          ((2 : ℤ) ^ Word.criticalDefect w start - 1) *
            (3 : ℤ) ^ (Word.oddSteps w - (start + 1)), ?_⟩
        ring
      have hTailLarge := ih (start := start + 1) hNextEnd
      have hDepthLt :
          Word.prefixTwoDepth w start <
            Word.prefixTwoDepth w (start + 1) :=
        Word.prefixTwoDepth_lt_of_valid C.1
          (i := start) (j := start + 1) (by omega) (by omega)
      have hPowDvd :
          (2 : ℤ) ^ Word.prefixTwoDepth w start ∣
            (2 : ℤ) ^ Word.prefixTwoDepth w (start + 1) :=
        intPow_dvd_intPow_of_le 2 (Nat.le_of_lt hDepthLt)
      have hTail :
          (2 : ℤ) ^ Word.prefixTwoDepth w start ∣
            actualFerrersSegmentDeficitZ w (start + 1) n :=
        dvd_trans hPowDvd hTailLarge
      rw [actualFerrersSegmentDeficitZ_succ_left]
      exact dvd_add hColumn hTail

/-- suffix 自身は左端 prefix depth の 2-power を持つ。 -/
theorem actualFerrersSuffix_twoPow_dvd
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {k : ℕ}
    (hk : k ≤ Word.oddSteps w) :
    (2 : ℤ) ^ Word.prefixTwoDepth w k ∣
      actualFerrersSuffixZ w k := by
  unfold actualFerrersSuffixZ
  apply actualFerrersSegment_twoPow_dvd C
  omega

/--
whole deficit の exact 3-adic order が `v` なら、
`s = p-v` より右の任意 suffix は local width `p-k` の 3-power を持つ。
-/
theorem actualFerrersSuffix_threePow_dvd_of_threeAdicOrder
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {v k : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w)
    (hStart : Word.oddSteps w - v ≤ k)
    (hk : k ≤ Word.oddSteps w) :
    (3 : ℤ) ^ (Word.oddSteps w - k) ∣
      actualFerrersSuffixZ w k := by
  have hExpLe : Word.oddSteps w - k ≤ v := by omega
  have hPowDvd :
      (3 : ℤ) ^ (Word.oddSteps w - k) ∣ (3 : ℤ) ^ v :=
    intPow_dvd_intPow_of_le 3 hExpLe
  have hWhole :
      (3 : ℤ) ^ (Word.oddSteps w - k) ∣ actualFerrersSuffixZ w 0 :=
    dvd_trans hPowDvd hOrder.1
  have hPrefix := actualFerrersPrefixSegment_threePow_dvd C hk
  have hSplit := actualFerrersSuffixZ_zero_split w hk
  have hEq :
      actualFerrersSuffixZ w k =
        actualFerrersSuffixZ w 0 - actualFerrersSegmentDeficitZ w 0 k := by
    linarith
  rw [hEq]
  exact dvd_sub hWhole hPrefix

/--
中心 lemma 2。

exact 3-adic order `v` から `s=p-v` より右の任意 cut で

  suffix(k) = 2^prefixDepth(k) * 3^(p-k) * q_k

となる整数 `q_k` を構成する。
-/
theorem actualSuffix_integral_of_threeAdicOrder
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {v k : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w)
    (hStart : Word.oddSteps w - v ≤ k)
    (hk : k ≤ Word.oddSteps w) :
    ∃ q : ℤ,
      actualFerrersSuffixZ w k =
        (2 : ℤ) ^ Word.prefixTwoDepth w k *
          (3 : ℤ) ^ (Word.oddSteps w - k) * q := by
  have hTwo := actualFerrersSuffix_twoPow_dvd C hk
  have hThree :=
    actualFerrersSuffix_threePow_dvd_of_threeAdicOrder
      C hOrder hv hStart hk
  rcases hTwo with ⟨u, hu⟩
  have hThreeU :
      (3 : ℤ) ^ (Word.oddSteps w - k) ∣ u := by
    apply MonotoneSuffixHenselChain.threePow_dvd_cancel_twoPow
    rw [← hu]
    exact hThree
  rcases hThreeU with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hu, hq]
  ring

/--
後段 Hensel bridge が使う quotient corridor。
`q_spec` だけを保持し、Ferrers geometry 自体は重複保持しない。
-/
structure ActualFerrersIntegralCorridor (w : Word) where
  start : ℕ
  start_le_terminal : start ≤ Word.oddSteps w
  q : ℕ → ℤ
  q_spec :
    ∀ {k : ℕ},
      start ≤ k →
      k ≤ Word.oddSteps w →
      actualFerrersSuffixZ w k =
        (2 : ℤ) ^ Word.prefixTwoDepth w k *
          (3 : ℤ) ^ (Word.oddSteps w - k) * q k

/-- exact-order certificate から選ぶ canonical quotient。 -/
noncomputable def actualSuffixIntegralQuotient
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {v : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w)
    (k : ℕ) : ℤ := by
  classical
  exact if h : Word.oddSteps w - v ≤ k ∧ k ≤ Word.oddSteps w then
    Classical.choose
      (actualSuffix_integral_of_threeAdicOrder C hOrder hv h.1 h.2)
  else
    0

/-- corridor 内では canonical quotient が defining factorization を満たす。 -/
theorem actualSuffixIntegralQuotient_spec
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {v : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w)
    {k : ℕ}
    (hStart : Word.oddSteps w - v ≤ k)
    (hk : k ≤ Word.oddSteps w) :
    actualFerrersSuffixZ w k =
      (2 : ℤ) ^ Word.prefixTwoDepth w k *
        (3 : ℤ) ^ (Word.oddSteps w - k) *
          actualSuffixIntegralQuotient C hOrder hv k := by
  classical
  unfold actualSuffixIntegralQuotient
  rw [dite_eq_left ⟨hStart, hk⟩]
  exact Classical.choose_spec
    (actualSuffix_integral_of_threeAdicOrder C hOrder hv hStart hk)

/-- whole exact order から quotient corridor を一度だけ構成する。 -/
noncomputable def actualFerrersIntegralCorridorOfThreeAdicOrder
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {v : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w) :
    ActualFerrersIntegralCorridor w where
  start := Word.oddSteps w - v
  start_le_terminal := by omega
  q := actualSuffixIntegralQuotient C hOrder hv
  q_spec := by
    intro k hStart hk
    exact actualSuffixIntegralQuotient_spec C hOrder hv hStart hk

end DoubleDecomposition
end CSTMicro
end Collatz2
