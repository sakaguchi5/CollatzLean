import CollatzLean.Collatz3.Mersenne.TargetTwoHoleBlockComplexityProof
import CollatzLean.Collatz3.Mersenne.SmallHoleExitDepth
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: target-two の small source width

`TargetTwoHolePhase` は `n≥4` を扱うため、`n=1,2,3` は別に切り出す。

このファイルでは次を行う。

1. `n=2` を exact に `n=1`, depth `k+1` へ移す。
2. `n=3` を mod 7 で完全な residue phase に分類する。
3. `n=1,3` に必要な period-break statement を薄い内部 target として固定する。
4. その target が得られれば、既存 `StephanValuationWidthPeriodBreakEscape` により
   `n≤3` 全体が bounded-depth になることを証明する。

ここで新しく外部数論仮定を追加しない。
`TargetTwoHoleSmallSourcePeriodBreak` は binary bookkeeping の残りを明示するための
内部 target であり、axiom ではない。
-/

namespace Collatz3
namespace Mersenne

/-- `n=2` は `2^2-1=3` により `n=1`, depth `k+1` へ exact に移る。 -/
theorem TargetTwoHoleEquation.source_two_to_source_one
    {k r L a b : ℕ}
    (hEq : TargetTwoHoleEquation k 2 r L a b) :
    TargetTwoHoleEquation (k + 1) 1 r L a b := by
  unfold TargetTwoHoleEquation at hEq ⊢
  norm_num at hEq ⊢
  rw [pow_succ]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hEq

/--
`n=3` の mod 7 phase を有限状態として読むための residue class。

`r=1` では3型、`r=2` では5型だけが残る。
最後の二型 `(2,0,2)`, `(2,2,0)` が `n≥4` phase theorem に無い小幅固有型。
-/
def TargetTwoHoleN3ResidueClass
    (r L a b : ℕ) : Prop :=
  (r = 1 ∧
    ((L = 0 ∧ a = 1 ∧ b = 1) ∨
     (L = 1 ∧ a = 0 ∧ b = 2) ∨
     (L = 1 ∧ a = 2 ∧ b = 0))) ∨
  (r = 2 ∧
    ((L = 0 ∧ a = 0 ∧ b = 0) ∨
     (L = 1 ∧ a = 0 ∧ b = 1) ∨
     (L = 1 ∧ a = 1 ∧ b = 0) ∨
     (L = 2 ∧ a = 0 ∧ b = 2) ∨
     (L = 2 ∧ a = 2 ∧ b = 0)))

/--
`Fin 3` の各指数に対する mod 7 equation の真偽を、
完全に閉じた有限計算として判定する。
-/
private theorem targetTwo_n3_mod7_table
    (R T A B : Fin 3) :
    (R.1 = 1 ∨ R.1 = 2) →
    (2 : ZMod 7) ^ R.1 *
        ((2 : ZMod 7) ^ T.1 - 1 -
          (2 : ZMod 7) ^ A.1 -
          (2 : ZMod 7) ^ B.1) + 1 = 0 →
    TargetTwoHoleN3ResidueClass R.1 T.1 A.1 B.1 := by
  fin_cases R <;>
    fin_cases T <;>
    fin_cases A <;>
    fin_cases B <;>
    simp only [TargetTwoHoleN3ResidueClass] <;>
    decide

/-- `Fin 3` 上の mod 7 residue equation は上の8型に完全分類される。 -/
private theorem targetTwo_n3_residue_finite :
    ∀ R T A B : Fin 3,
      (R.1 = 1 ∨ R.1 = 2) →
      (2 : ZMod 7) ^ R.1 *
          ((2 : ZMod 7) ^ T.1 - 1 -
            (2 : ZMod 7) ^ A.1 - (2 : ZMod 7) ^ B.1) + 1 = 0 →
      TargetTwoHoleN3ResidueClass R.1 T.1 A.1 B.1 :=
  targetTwo_n3_mod7_table


/--
well-formed `n=3` target-two は mod 7 でちょうど8 residue phase のどれかに入る。

exit depth は既存 low-bit theorem により `r=1` または `r=2` に先に固定する。
-/
theorem TargetTwoHoleEquation.source_three_residue_class
    {k r L a b : ℕ}
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k 3 r L a b) :
    TargetTwoHoleN3ResidueClass r (L % 3) (a % 3) (b % 3) := by
  have hr12 : r = 1 ∨ r = 2 := by
    rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
    · exact Or.inl
        (hEq.exitDepth_eq_one_of_largeSource_even
          hkEven (by omega : 3 ≤ 3) hr)
    · exact Or.inr
        (hEq.exitDepth_eq_two_of_largeSource_odd
          hkOdd (by omega : 3 ≤ 3) hr ha0 hab hbL)
  have hMod := hEq.to_mod 7
  unfold TargetTwoHoleModEquation at hMod
  norm_num at hMod
  have hPeriod : (2 : ZMod 7) ^ 3 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 7) (e := L) hPeriod,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 7) (e := a) hPeriod,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 7) (e := b) hPeriod] at hMod
  have hSeven : (7 : ZMod 7) = 0 := by
    decide
  have hResidueEq :
      (2 : ZMod 7) ^ r *
          ((2 : ZMod 7) ^ (L % 3) - 1 -
            (2 : ZMod 7) ^ (a % 3) -
              (2 : ZMod 7) ^ (b % 3)) + 1 = 0 := by
    rw [hSeven, mul_zero] at hMod
    exact hMod.symm
  have hrLt : r < 3 := by rcases hr12 with rfl | rfl <;> omega
  let Rf : Fin 3 := ⟨r, hrLt⟩
  let Tf : Fin 3 := ⟨L % 3, Nat.mod_lt _ (by norm_num)⟩
  let Af : Fin 3 := ⟨a % 3, Nat.mod_lt _ (by norm_num)⟩
  let Bf : Fin 3 := ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩
  apply targetTwo_n3_residue_finite Rf Tf Af Bf
  · simpa [Rf] using hr12
  · simpa [Rf, Tf, Af, Bf] using hResidueEq

/--
small source width に対して内部で残る binary target。

* `n=1`: shift された two-hole Mersenne word なので安全側 `break≤6`。
* `n=3`: 上の有限8 phase を block 化して安全側 `break≤8`。

この定義自体は仮定ではなく、後続の binary proof を置くための名前付き target。
-/
def TargetTwoHoleSmallSourcePeriodBreak : Prop :=
  (∀ {k r L a b : ℕ},
      0 < r →
      0 < a → a < b → b < L →
      TargetTwoHoleEquation k 1 r L a b →
      Binary.HasPeriodBreakAtMost (3 ^ k) 1 6) ∧
  (∀ {k r L a b : ℕ},
      0 < r →
      0 < a → a < b → b < L →
      TargetTwoHoleEquation k 3 r L a b →
      Binary.HasPeriodBreakAtMost (3 ^ k) 3 8)

/--
small-source period-break target と Stephan corollary が揃えば、`1≤n≤3` は一様有界。

`n=2` は `k+1,n=1` へ exact shift してから同じ Stephan bound を使う。
-/
theorem targetTwo_smallSource_depth_bounded_of_stephan
    (hStephan : StephanValuationWidthPeriodBreakEscape)
    (hSmall : TargetTwoHoleSmallSourcePeriodBreak) :
    ∃ K : ℕ,
      ∀ {k n r L a b : ℕ},
        2 ≤ k →
        0 < n → n ≤ 3 →
        0 < r →
        0 < a → a < b → b < L →
        TargetTwoHoleEquation k n r L a b →
        k < K := by
  unfold StephanValuationWidthPeriodBreakEscape at hStephan
  rcases hStephan 8 with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k n r L a b hk2 hnPos hn3 hr ha0 hab hbL hEq
  have hnCases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hnCases with rfl | rfl | rfl
  · have hPB6 := hSmall.1 hr ha0 hab hbL hEq
    have hPB8 := hPB6.mono (by omega : 6 ≤ 8)
    exact hK hk2 (Or.inl (by omega)) hPB8
  · have hShift := hEq.source_two_to_source_one
    have hPB6 := hSmall.1 hr ha0 hab hbL hShift
    have hPB8 := hPB6.mono (by omega : 6 ≤ 8)
    have hBound : k + 1 < K :=
      hK (by omega : 2 ≤ k + 1) (Or.inl (by omega)) hPB8
    omega
  · have hPB8 := hSmall.2 hr ha0 hab hbL hEq
    exact hK hk2 (Or.inl (by omega)) hPB8

/--
`n≥4` の完成済み内部 theorem と small-source target を合わせた target-two 全 source-width 版。

まだ外部入力は `StephanValuationWidthPeriodBreakEscape` と
small-source の binary bookkeeping target の二つだけである。
-/
theorem targetTwo_allSource_depth_bounded_of_stephan
    (hStephan : StephanValuationWidthPeriodBreakEscape)
    (hSmall : TargetTwoHoleSmallSourcePeriodBreak) :
    ∃ K : ℕ,
      ∀ {k n r L a b : ℕ},
        2 ≤ k →
        0 < n →
        0 < r →
        0 < a → a < b → b < L →
        TargetTwoHoleEquation k n r L a b →
        k < K := by
  rcases targetTwo_smallSource_depth_bounded_of_stephan hStephan hSmall with
    ⟨Ksmall, hKsmall⟩
  rcases targetTwo_depth_bounded_of_stephan_internal hStephan with
    ⟨Klarge, hKlarge⟩
  let K : ℕ := max Ksmall Klarge
  refine ⟨K, ?_⟩
  intro k n r L a b hk2 hn hr ha0 hab hbL hEq
  by_cases hnSmall : n ≤ 3
  · have hkLt := hKsmall hk2 hn hnSmall hr ha0 hab hbL hEq
    exact lt_of_lt_of_le hkLt (Nat.le_max_left _ _)
  · have hn4 : 4 ≤ n := by omega
    rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
    · have hrOne :=
        hEq.exitDepth_eq_one_of_largeSource_even hkEven (by omega : 3 ≤ n) hr
      have hGeom :=
        hEq.exists_geometricData hn4 (Or.inl hrOne) ha0 hab hbL
      have hParity :
          (r = 1 ∧ Even k) ∨ (r = 2 ∧ k % 2 = 1) := by
        left
        refine ⟨hrOne, ?_⟩
        exact even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hkEven)
      have hkLt := hKlarge hk2 hn4 hParity hGeom
      exact lt_of_lt_of_le hkLt (Nat.le_max_right _ _)
    · have hrTwo :=
        hEq.exitDepth_eq_two_of_largeSource_odd
          hkOdd (by omega : 3 ≤ n) hr ha0 hab hbL
      have hGeom :=
        hEq.exists_geometricData hn4 (Or.inr hrTwo) ha0 hab hbL
      have hParity :
          (r = 1 ∧ Even k) ∨ (r = 2 ∧ k % 2 = 1) :=
        Or.inr ⟨hrTwo, hkOdd⟩
      have hkLt := hKlarge hk2 hn4 hParity hGeom
      exact lt_of_lt_of_le hkLt (Nat.le_max_right _ _)

end Mersenne
end Collatz3
