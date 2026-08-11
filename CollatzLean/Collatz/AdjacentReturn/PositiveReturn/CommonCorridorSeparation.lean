import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.BiCanonical
import CollatzLean.Collatz.AdjacentReturn.GapDepthDichotomy

/-!
# common corridor の separation

bounded gap-depth 枝で、異なる future-minimum start が同じ actual word を
どこまで共有できるかを有限語として明示する。

隣接 start の差を

  `valueGap = 2^D * u`, `u` odd

と exact に分解し、同じ actual word `w` を二つの start が走るなら
canonical residue modulus により

  `2^(w.twoSteps + 1) ∣ valueGap`

となる。したがって

  `w.twoSteps + 1 ≤ D`

であり、valid 性から `w.length < D` を得る。

また、異なる chain 項で同じ prefix word が現れても、その cut が両方とも
bi-canonical なら両 start が同じ canonical representative になってしまう。
chain start は狭義増加なので、これは不可能である。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace CanonicalChain

/--
`2^a` が exact 2進分解 `N = 2^d * u`, `u` odd の `N` を割るなら `a ≤ d`。
-/
private theorem twoPow_dvd_exactFactor_exponent_le
    {N a d u : ℕ}
    (hdiv : 2 ^ a ∣ N)
    (hfac : TwoAdic.ExactFactor N d u) :
    a ≤ d := by
  by_contra hnot
  have hda : d < a := by
    omega
  rcases hdiv with ⟨v, hv⟩
  have hpow :
      2 ^ d * u = 2 ^ a * v :=
    hfac.1.symm.trans hv
  obtain ⟨r, hur⟩ :=
    TwoAdic.oddPart_eq_twoPow_mul_of_lt hpow hda
  exact TwoAdic.odd_even_false hfac.2 (by
    rw [hur]
    exact TwoAdic.even_two_pow_succ_mul r v)

/--
隣接 future minima が同じ actual word `w` を走るなら、
その word が消費する2進指数に replay の1 bitを加えた深さは
adjacent gap depth 以下である。
-/
theorem commonRuns_twoSteps_succ_le_gapDepth
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ)
    {w : Collatz.Word} {y₀ y₁ : ℕ}
    (h₀ : Word.Runs w (C.state n).startValue y₀)
    (h₁ : Word.Runs w (C.state (n + 1)).startValue y₁) :
    w.twoSteps + 1 ≤ (C.core.valuationData n).gapDepth := by
  by_cases hw : w = []
  · subst w
    have htwo := C.core.gapDepth_two_le n
    simp [Word.twoSteps]
    omega
  · have h₀' :
        Word.Runs w (C.core.state n).startValue y₀ := by
      simpa [CanonicalChain.state] using h₀
    have h₁' :
        Word.Runs w (C.core.state (n + 1)).startValue y₁ := by
      simpa [CanonicalChain.state] using h₁
    have hy₀ : Odd y₀ :=
      h₀'.end_odd_of_ne_nil hw
    have hy₁ : Odd y₁ :=
      h₁'.end_odd_of_ne_nil hw
    have hxlt :
        (C.core.state n).startValue <
          (C.core.state (n + 1)).startValue := by
      calc
        (C.core.state n).startValue
            < (C.core.state n).nextValue :=
          (C.core.state n).startValue_lt_nextValue
        _ = (C.core.state (n + 1)).startValue :=
          C.core.nextValue_eq_next_startValue n
    have hx :
        (C.core.state n).startValue ≤
          (C.core.state (n + 1)).startValue :=
      Nat.le_of_lt hxlt
    have hdivRaw :=
      h₀'.realizes.residueModulus_dvd_startDifference
        h₁'.realizes hx hy₀ hy₁
    rw [← C.core.nextValue_eq_next_startValue n] at hdivRaw
    have hdiv :
        2 ^ (w.twoSteps + 1) ∣ (C.core.state n).valueGap := by
      simpa [Word.residueModulus, State.valueGap] using hdivRaw
    exact
      twoPow_dvd_exactFactor_exponent_le
        hdiv (C.core.valuationData n).gapFactor

/--
隣接 future minima が共有できる actual word の長さは gap depth 未満。
-/
theorem commonRuns_length_lt_gapDepth
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ)
    {w : Collatz.Word} {y₀ y₁ : ℕ}
    (h₀ : Word.Runs w (C.state n).startValue y₀)
    (h₁ : Word.Runs w (C.state (n + 1)).startValue y₁) :
    w.length < (C.core.valuationData n).gapDepth := by
  have hdepth :=
    C.commonRuns_twoSteps_succ_le_gapDepth n h₀ h₁
  have hvalid : Word.Valid w := h₀.valid
  have hlength : w.length ≤ w.twoSteps := by
    simpa [Word.oddSteps] using Word.oddSteps_le_twoSteps hvalid
  omega

/--
bounded gap-depth `M` の枝では、隣接 future minima の common actual word は
一様に長さ `M` 未満。
-/
theorem commonRuns_length_lt_of_gapDepth_bounded
    {O : OddOrbit} (C : CanonicalChain O)
    {M n : ℕ}
    (hB : C.core.GapDepthBounded M)
    {w : Collatz.Word} {y₀ y₁ : ℕ}
    (h₀ : Word.Runs w (C.state n).startValue y₀)
    (h₁ : Word.Runs w (C.state (n + 1)).startValue y₁) :
    w.length < M := by
  have hlength := C.commonRuns_length_lt_gapDepth n h₀ h₁
  have hbound :
      (C.core.valuationData n).gapDepth ≤ M := by
    simpa [CanonicalContractingChain.gapDepth] using hB n
  exact lt_of_lt_of_le hlength hbound

/-- chain の start value は chain index とともに狭義増加する。 -/
private theorem startValue_strict_of_lt
    {O : OddOrbit} (C : CanonicalChain O)
    {i j : ℕ} (hij : i < j) :
    (C.state i).startValue < (C.state j).startValue := by
  have hadj :
      ∀ k : ℕ,
        (C.state k).startValue <
          (C.state (k + 1)).startValue := by
    intro k
    calc
      (C.state k).startValue
          < (C.state k).nextValue :=
        (C.state k).startValue_lt_nextValue
      _ = (C.state (k + 1)).startValue := by
        simpa [CanonicalChain.state] using
          C.core.nextValue_eq_next_startValue k
  induction j generalizing i with
  | zero =>
      omega
  | succ j ih =>
      by_cases hEq : i = j
      · subst i
        exact hadj j
      · have hij' : i < j := by
          omega
        exact lt_trans (ih hij') (hadj j)

/--
異なる2つの chain 項で prefix word が一致している cut は、
両方同時に bi-canonical にはなれない。

bi-canonical ならどちらの actual start も同じ word の canonicalStart に等しくなるが、
chain start value 自体は狭義増加するため矛盾する。
-/
theorem commonPrefix_not_biCanonical_both
    {O : OddOrbit} (C : CanonicalChain O)
    {n₀ n₁ k₀ k₁ : ℕ}
    (hn : n₀ < n₁)
    (hword :
      FirstCrossingData.prefixWord (C.firstCrossing n₀) k₀ =
        FirstCrossingData.prefixWord (C.firstCrossing n₁) k₁) :
    ¬ (
      BiCanonicalCutData (C.firstCrossing n₀) k₀ ∧
      BiCanonicalCutData (C.firstCrossing n₁) k₁) := by
  rintro ⟨D₀, D₁⟩
  have hstartEq :
      (C.state n₀).startValue =
        (C.state n₁).startValue := by
    calc
      (C.state n₀).startValue
          = Word.canonicalStart
              (FirstCrossingData.prefixWord
                (C.firstCrossing n₀) k₀) :=
        D₀.prefixStart_eq
      _ = Word.canonicalStart
              (FirstCrossingData.prefixWord
                (C.firstCrossing n₁) k₁) := by
        rw [hword]
      _ = (C.state n₁).startValue :=
        D₁.prefixStart_eq.symm
  have hstrict := startValue_strict_of_lt C hn
  omega

end CanonicalChain
end PositiveReturn
end AdjacentReturn
end Collatz
