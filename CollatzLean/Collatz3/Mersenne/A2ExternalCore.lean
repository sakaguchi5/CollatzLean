import CollatzLean.Collatz3.External.ChimTwoLogarithms
import CollatzLean.Collatz3.External.StephanVariablePeriod
import CollatzLean.Collatz3.Mersenne.SourceTwoEvenAnalytic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleFinalExternalArithmetic
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleBlockComplexityProof
import CollatzLean.Collatz3.Mersenne.TwoHoleFinalExternalArithmetic
set_option exponentiation.threshold 392
/-!
# Collatz3 Mersenne: A2 external core の branch-free 化・第1段階

A1 と同じ設計へ A2 を移すため、branch package に置かれていた深い入力を
純粋数論 `External` 層へ順次移す。

この段階で内部化するもの:

* source-even:
  exact identity `3^k(2^n-7)=2^(L+3)-7`
  + pure Chim specialization
  + internal `2^392 ∣ k`
  により完全排除。
* target-large analytic side:
  internal `period-break≤5` と valuation width
  + pure Stephan variable-period theorem
  により depth bound の存在を内部導出。

従って新しい主 API では

* source field は不要。
* target-large は analytic bound を外部から受け取らず、
  bounded finite sieve だけを受け取る。
* split の3枝はまだ従来 package のまま残す。

未証明 branch を名前だけ `External` へ移すことはしない。
このファイルは A2 final package を本当に空にするための中間層である。
-/

namespace Collatz3
namespace Mersenne

/-! ## source-even: pure Chim input から完全内部化 -/

/--
source-even の exact identity から `3^k ∣ 2^(L+3)-7` を取り出し、
pure Chim specialization で `k<2^392` を得る。
-/
theorem SourceTwoHoleEquation.evenLowResonance_depth_lt_twoPow392_externalCore
    {k n r L : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 1 2) :
    k < 2 ^ 392 := by
  have hIdentity :=
    hEq.evenLowResonance_integer_identity hk7
  have hDiv :
      (3 : ℤ) ^ k ∣ (2 : ℤ) ^ (L + 3) - 7 := by
    refine ⟨(2 : ℤ) ^ n - 7, ?_⟩
    exact hIdentity.symm
  exact
    External.ChimTwoLogarithms.twoPow_sub_seven_threeAdic_depth_lt_twoPow392
      hk7 hDiv

/--
source-even は external branch field なしで不可能。

analytic `k<2^392` と内部 `2^392∣k` を衝突させる。
-/
theorem SourceTwoHoleEquation.evenLowResonance_impossible_externalCore
    {k n r L : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 1 2) :
    False := by
  have hLt :=
    hEq.evenLowResonance_depth_lt_twoPow392_externalCore hk7
  have hDvd :=
    hEq.evenLowResonance_twoPow392_dvd_depth hk7
  have hLe : 2 ^ 392 ≤ k :=
    Nat.le_of_dvd (by omega : 0 < k) hDvd
  omega

/--
旧 `SourceTwoFinalExternalArithmetic` を canonical に内部構成する。

旧型は互換性のため field を持ったままだが、呼び出し側が witness を与える必要はない。
-/
theorem sourceTwoFinalExternalArithmetic_internal :
    SourceTwoFinalExternalArithmetic where
  even_resonance_bound := by
    intro k n r L hk7 hEq
    exact hEq.evenLowResonance_depth_lt_twoPow392_externalCore hk7

/-! ## target-large: variable-period analytic bound を External へ移す -/

/--
`Mersenne.BlockComplexity` の旧 interface を、
pure External theorem から内部構成する。
-/
theorem stephanValuationWidthPeriodBreakEscape_externalCore :
    StephanValuationWidthPeriodBreakEscape := by
  simpa [
    StephanValuationWidthPeriodBreakEscape,
    External.StephanVariablePeriod.ValuationWidthPeriodBreakEscape
  ] using
    External.StephanVariablePeriod.valuationWidthPeriodBreakEscape

/--
target-two `n≥4` の analytic depth bound は、
pure Stephan theorem と内部 `period-break≤5` だけから得られる。
-/
theorem targetTwo_large_depth_bounded_externalCore :
    ∃ K : ℕ,
      ∀ {k n r L a b : ℕ},
        2 ≤ k →
        4 ≤ n →
        ((r = 1 ∧ Even k) ∨ (r = 2 ∧ k % 2 = 1)) →
        TargetTwoHoleGeometricBranch k n r L a b →
        k < K :=
  targetTwo_depth_bounded_of_stephan_internal
    stephanValuationWidthPeriodBreakEscape_externalCore

/--
target-large 用の bound witness。

現段階では Stephan corollary が existential なので noncomputable。
次段で four-log proof engine の explicit constant を移植したら
計算可能な定数へ置き換える。
-/
noncomputable def targetTwoLargeInternalDepthBound : ℕ :=
  Classical.choose targetTwo_large_depth_bounded_externalCore

/-- 固定した target-large bound witness の仕様。 -/
theorem targetTwoLargeInternalDepthBound_spec
    {k n r L a b : ℕ}
    (hk2 : 2 ≤ k)
    (hn4 : 4 ≤ n)
    (hParity : (r = 1 ∧ Even k) ∨ (r = 2 ∧ k % 2 = 1))
    (hGeom : TargetTwoHoleGeometricBranch k n r L a b) :
    k < targetTwoLargeInternalDepthBound := by
  exact
    (Classical.choose_spec targetTwo_large_depth_bounded_externalCore)
      hk2 hn4 hParity hGeom

/-- target-large even final case の analytic bound。 -/
theorem TargetTwoLargeEvenFinalCase.internal_depth_bound_externalCore
    {k : ℕ}
    (h : TargetTwoLargeEvenFinalCase k) :
    k < targetTwoLargeInternalDepthBound := by
  rcases h with
    ⟨n, L, a, b, hk7, hkEven, hn4, ha0, hab, hbDeep, hEq⟩
  have hGeom :=
    hEq.exists_geometricData
      hn4 (Or.inl rfl) ha0 hab (by omega : b < L)
  exact
    targetTwoLargeInternalDepthBound_spec
      (k := k) (n := n) (r := 1) (L := L) (a := a) (b := b)
      (by omega : 2 ≤ k)
      hn4
      (Or.inl ⟨rfl, (Nat.even_iff).2 hkEven⟩)
      hGeom

/-- target-large odd final case の analytic bound。 -/
theorem TargetTwoLargeOddFinalCase.internal_depth_bound_externalCore
    {k : ℕ}
    (h : TargetTwoLargeOddFinalCase k) :
    k < targetTwoLargeInternalDepthBound := by
  rcases h with
    ⟨n, L, a, b, hk7, hkOdd, hn4, ha0, hab, hbDeep, hEq⟩
  have hGeom :=
    hEq.exists_geometricData
      hn4 (Or.inr rfl) ha0 hab (by omega : b < L)
  exact
    targetTwoLargeInternalDepthBound_spec
      (k := k) (n := n) (r := 2) (L := L) (a := a) (b := b)
      (by omega : 2 ≤ k)
      hn4
      (Or.inr ⟨rfl, hkOdd⟩)
      hGeom

/-! ## target final package を finite-only に縮約 -/

/--
target-large では analytic bound を内部化したので、
新しい主 API が外部から受け取るのは bounded finite sieve だけ。
-/
structure TargetTwoFinalFiniteArithmetic : Prop where
  large_even_finite_sieve :
    ∀ {k : ℕ},
      TargetTwoLargeEvenFinalCase k →
      k < targetTwoLargeInternalDepthBound →
      False
  large_odd_finite_sieve :
    ∀ {k : ℕ},
      TargetTwoLargeOddFinalCase k →
      k < targetTwoLargeInternalDepthBound →
      False

/--
finite-only target package から旧 target package を復元する。
-/
theorem TargetTwoFinalFiniteArithmetic.toExternalArithmetic
    (A : TargetTwoFinalFiniteArithmetic) :
    TargetTwoFinalExternalArithmetic where
  large_even := by
    refine ⟨targetTwoLargeInternalDepthBound, ?_, ?_⟩
    · intro k h
      exact TargetTwoLargeEvenFinalCase.internal_depth_bound_externalCore h
    · intro k h hBound
      exact A.large_even_finite_sieve h hBound
  large_odd := by
    refine ⟨targetTwoLargeInternalDepthBound, ?_, ?_⟩
    · intro k h
      exact TargetTwoLargeOddFinalCase.internal_depth_bound_externalCore h
    · intro k h hBound
      exact A.large_odd_finite_sieve h hBound

/-! ## 新しい A2 主 package -/

/--
A2 external core 第1段階の主 package。

source は完全内部化済みなので field を持たない。
target analytic bound も内部化済みなので finite sieve だけを受け取る。
split の3枝だけは次段の p-adic / real two-log internalization 待ち。
-/
structure TwoHoleFinalExternalArithmeticCore : Prop where
  split : SplitTwoFinalExternalArithmetic
  target : TargetTwoFinalFiniteArithmetic

/--
新 core package から旧 final package を互換構成する。
-/
theorem TwoHoleFinalExternalArithmeticCore.toFinalExternalArithmetic
    (A : TwoHoleFinalExternalArithmeticCore) :
    TwoHoleFinalExternalArithmetic where
  source := sourceTwoFinalExternalArithmetic_internal
  split := A.split
  target := A.target.toExternalArithmetic

/--
新 core package から従来 full-six-term package を構成する。
A1 は canonical internal witness を自動挿入する。
-/
theorem twoHoleFullExternalArithmetic_of_finalA2_core
    (A : TwoHoleFinalExternalArithmeticCore) :
    TwoHoleFullExternalArithmetic := by
  exact
    twoHoleFullExternalArithmetic_of_A1_finalA2
      targetOneHoleExternalArithmetic_internal
      A.toFinalExternalArithmetic

/-- 新 core package から `AtMostTwoHoleDepthBound`。 -/
theorem atMostTwoHoleDepthBound_of_finalA2_core
    (A : TwoHoleFinalExternalArithmeticCore) :
    AtMostTwoHoleDepthBound := by
  exact
    atMostTwoHoleDepthBound_of_A1_finalA2
      targetOneHoleExternalArithmetic_internal
      A.toFinalExternalArithmetic

/-- 新 core package から concrete small-hole lower bound。 -/
theorem blockSparsePow3LowerBound_smallHole_of_finalA2_core
    (A : TwoHoleFinalExternalArithmeticCore) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact
    blockSparsePow3LowerBound_smallHole_of_A1_finalA2
      targetOneHoleExternalArithmetic_internal
      A.toFinalExternalArithmetic

end Mersenne
end Collatz3
