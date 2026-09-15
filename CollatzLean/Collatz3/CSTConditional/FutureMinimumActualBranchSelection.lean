import CollatzLean.Collatz3.CSTConditional.FutureMinimumIntegralCompletionLattice
import CollatzLean.Collatz3.CSTConditional.FutureMinimumBlockHenselTransport
import CollatzLean.Collatz3.Bridge.SurvivorCompletionAllStepNormalizedLift
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionGridSeparation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Collatz3 CSTConditional: actual-compatible completion branch selection

Stage 8 の future-minimum integral defect-grid、Stage 9 の A/C block Hensel transport、
既存の actual completion grid separation を同じ transition 上で接続する。

重要なのは、future-minimum defect-grid の `Z` 候補そのものへ grid separation を
直接当てないことである。`Z mod 2^δ` を固定すると `xi=Z/2^δ` の候補差は整数、
centered lift では差 `4` になるため、既存 separation の spacing `2/1` とは一致しない。

代わりに current future minimum から最初の completion step を見る。
normalized lift-step の algebraic branch は `4` 間隔であり、

* `survivorSturmianStep = 0` なら next centered lift は spacing `2`,
* `survivorSturmianStep = 1` なら next centered lift は spacing `1`

になる。ここで既存 actual grid separation が exact に効く。

Global CST の A/C refinement により

* `A` は必ず step `1`,
* 長さ1の `C` は step `0`,
* 非自明 `C` は既存の `C0/C1` 二分岐

なので、block Hensel transport と next completion branch separation を同じ theorem に束ねられる。

新しい branch state / alphabet / compatibility predicate は定義しない。
すべて既存 scalar と proposition の derived theorem として記録する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
normalized lift-step の候補差が `4` で、Sturmian step が `0` なら、
対応する next centered lift の差は `2`。

従って同じ actual residue fraction `theta_(m+1)` と両立する二候補は存在しない。
-/
theorem not_both_nextCenteredLiftCompatible_of_stepSpacing_four_of_sturmianStep_zero
    (O : Collatz3.OddOrbit)
    {m : ℕ}
    (hs : survivorSturmianStep m = 0)
    (q₁ q₂ tauCurrent tau₁ tau₂ : ℝ)
    (z₁ z₂ : ℤ)
    (hRec₁ :
      q₁ =
        (2 : ℝ) ^ (1 + survivorSturmianStep m) * tau₁ - tauCurrent)
    (hRec₂ :
      q₂ =
        (2 : ℝ) ^ (1 + survivorSturmianStep m) * tau₂ - tauCurrent)
    (hSpacing : q₁ = q₂ + 4 ∨ q₂ = q₁ + 4)
    (hCompat₁ :
      O.defectActualResidueFraction (m + 1) +
          ((3 : ℝ) ^ (m + 1) / 4) * (tau₁ - 2) =
        (z₁ : ℝ))
    (hCompat₂ :
      O.defectActualResidueFraction (m + 1) +
          ((3 : ℝ) ^ (m + 1) / 4) * (tau₂ - 2) =
        (z₂ : ℝ)) :
    False := by
  rw [hs] at hRec₁ hRec₂
  norm_num at hRec₁ hRec₂
  rcases hSpacing with h12 | h21
  · have hLift : tau₁ - 2 = (tau₂ - 2) + 2 := by
      linarith
    exact
      Bridge.not_both_centeredLiftCompatible_of_eq_add_two
        (m + 1)
        (O.defectActualResidueFraction (m + 1))
        (tau₁ - 2) (tau₂ - 2) z₁ z₂
        hCompat₁ hCompat₂ hLift
  · have hLift : tau₂ - 2 = (tau₁ - 2) + 2 := by
      linarith
    exact
      Bridge.not_both_centeredLiftCompatible_of_eq_add_two
        (m + 1)
        (O.defectActualResidueFraction (m + 1))
        (tau₂ - 2) (tau₁ - 2) z₂ z₁
        hCompat₂ hCompat₁ hLift

/--
normalized lift-step の候補差が `4` で、Sturmian step が `1` なら、
対応する next centered lift の差は `1`。

従って同じ actual residue fraction `theta_(m+1)` と両立する二候補は存在しない。
-/
theorem not_both_nextCenteredLiftCompatible_of_stepSpacing_four_of_sturmianStep_one
    (O : Collatz3.OddOrbit)
    {m : ℕ}
    (hs : survivorSturmianStep m = 1)
    (q₁ q₂ tauCurrent tau₁ tau₂ : ℝ)
    (z₁ z₂ : ℤ)
    (hRec₁ :
      q₁ =
        (2 : ℝ) ^ (1 + survivorSturmianStep m) * tau₁ - tauCurrent)
    (hRec₂ :
      q₂ =
        (2 : ℝ) ^ (1 + survivorSturmianStep m) * tau₂ - tauCurrent)
    (hSpacing : q₁ = q₂ + 4 ∨ q₂ = q₁ + 4)
    (hCompat₁ :
      O.defectActualResidueFraction (m + 1) +
          ((3 : ℝ) ^ (m + 1) / 4) * (tau₁ - 2) =
        (z₁ : ℝ))
    (hCompat₂ :
      O.defectActualResidueFraction (m + 1) +
          ((3 : ℝ) ^ (m + 1) / 4) * (tau₂ - 2) =
        (z₂ : ℝ)) :
    False := by
  rw [hs] at hRec₁ hRec₂
  norm_num at hRec₁ hRec₂
  rcases hSpacing with h12 | h21
  · have hLift : tau₁ - 2 = (tau₂ - 2) + 1 := by
      linarith
    exact
      Bridge.not_both_centeredLiftCompatible_of_eq_add_one
        (m + 1)
        (O.defectActualResidueFraction (m + 1))
        (tau₁ - 2) (tau₂ - 2) z₁ z₂
        hCompat₁ hCompat₂ hLift
  · have hLift : tau₂ - 2 = (tau₁ - 2) + 1 := by
      linarith
    exact
      Bridge.not_both_centeredLiftCompatible_of_eq_add_one
        (m + 1)
        (O.defectActualResidueFraction (m + 1))
        (tau₂ - 2) (tau₁ - 2) z₂ z₁
        hCompat₂ hCompat₁ hLift

/--
`A` transition では開始 absolute Sturmian step が `1` なので、
normalized lift-step の隣接 (`4` spacing) 二候補は next actual residue と同時には両立しない。
-/
theorem symbol_A_nextCompletionBranch_pairwiseSeparated_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A)
    (q₁ q₂ tauCurrent tau₁ tau₂ : ℝ)
    (z₁ z₂ : ℤ)
    (hRec₁ :
      q₁ =
        (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₁ - tauCurrent)
    (hRec₂ :
      q₂ =
        (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₂ - tauCurrent)
    (hSpacing : q₁ = q₂ + 4 ∨ q₂ = q₁ + 4)
    (hCompat₁ :
      O.defectActualResidueFraction (i + 1) +
          ((3 : ℝ) ^ (i + 1) / 4) * (tau₁ - 2) =
        (z₁ : ℝ))
    (hCompat₂ :
      O.defectActualResidueFraction (i + 1) +
          ((3 : ℝ) ^ (i + 1) / 4) * (tau₂ - 2) =
        (z₂ : ℝ)) :
    False := by
  have hs :=
    O.nextFutureMinimum_symbol_A_sturmianStep_eq_one_of_globalCST
      G SInf hStart hNext hA
  exact
    O.not_both_nextCenteredLiftCompatible_of_stepSpacing_four_of_sturmianStep_one
      hs q₁ q₂ tauCurrent tau₁ tau₂ z₁ z₂
      hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂

/--
長さ1の `C` transition では開始点 `i` の absolute Sturmian step が `0`。
したがって、normalized lift-step で `4` だけ離れた二候補は、
次の actual residue 条件を同時には満たせない。
-/
theorem symbol_C_length_one_nextCompletionBranch_pairwiseSeparated
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hC : O.transitionSymbol i j = .C)
    (hLengthOne : j = i + 1)
    (q₁ q₂ tauCurrent tau₁ tau₂ : ℝ)
    (z₁ z₂ : ℤ)
    (hRec₁ :
      q₁ =
        (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₁ - tauCurrent)
    (hRec₂ :
      q₂ =
        (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₂ - tauCurrent)
    (hSpacing : q₁ = q₂ + 4 ∨ q₂ = q₁ + 4)
    (hCompat₁ :
      O.defectActualResidueFraction (i + 1) +
          ((3 : ℝ) ^ (i + 1) / 4) * (tau₁ - 2) =
        (z₁ : ℝ))
    (hCompat₂ :
      O.defectActualResidueFraction (i + 1) +
          ((3 : ℝ) ^ (i + 1) / 4) * (tau₂ - 2) =
        (z₂ : ℝ)) :
    False := by
  have hs :=
    O.nextFutureMinimum_symbol_C_length_one_sturmianStep_eq_zero
      hNext hC hLengthOne
  exact
    O.not_both_nextCenteredLiftCompatible_of_stepSpacing_four_of_sturmianStep_zero
      hs q₁ q₂ tauCurrent tau₁ tau₂ z₁ z₂
      hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂

/--
非自明 `C` transition では既存の `C0/C1` 二分岐に応じて、
next completion branch の actual-compatible spacing separation も `2/1` に分岐する。

新しい `C0/C1` alphabet は作らない。
-/
theorem symbol_C_nontrivial_nextCompletionBranch_pairwiseSeparation_cases_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hC : O.transitionSymbol i j = .C)
    (hLong : i + 1 < j) :
    (survivorSturmianStep i = 0 ∧
      Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 ∧
      O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1 ∧
      (∀ (q₁ q₂ tauCurrent tau₁ tau₂ : ℝ) (z₁ z₂ : ℤ),
        q₁ =
            (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₁ - tauCurrent →
        q₂ =
            (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₂ - tauCurrent →
        (q₁ = q₂ + 4 ∨ q₂ = q₁ + 4) →
        O.defectActualResidueFraction (i + 1) +
            ((3 : ℝ) ^ (i + 1) / 4) * (tau₁ - 2) = (z₁ : ℝ) →
        O.defectActualResidueFraction (i + 1) +
            ((3 : ℝ) ^ (i + 1) / 4) * (tau₂ - 2) = (z₂ : ℝ) →
        False)) ∨
    (survivorSturmianStep i = 1 ∧
      Critical.beattyCarry (i + 1) (j - (i + 1)) = 0 ∧
      O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1 ∧
      (∀ (q₁ q₂ tauCurrent tau₁ tau₂ : ℝ) (z₁ z₂ : ℤ),
        q₁ =
            (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₁ - tauCurrent →
        q₂ =
            (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₂ - tauCurrent →
        (q₁ = q₂ + 4 ∨ q₂ = q₁ + 4) →
        O.defectActualResidueFraction (i + 1) +
            ((3 : ℝ) ^ (i + 1) / 4) * (tau₁ - 2) = (z₁ : ℝ) →
        O.defectActualResidueFraction (i + 1) +
            ((3 : ℝ) ^ (i + 1) / 4) * (tau₂ - 2) = (z₂ : ℝ) →
        False)) := by
  rcases
      O.nextFutureMinimum_symbol_C_nontrivial_sturmianTail_cases_of_globalCST
        G SInf hStart hNext hC hLong with h0 | h1
  · left
    refine ⟨h0.1, h0.2.1, h0.2.2, ?_⟩
    intro q₁ q₂ tauCurrent tau₁ tau₂ z₁ z₂ hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂
    exact
      O.not_both_nextCenteredLiftCompatible_of_stepSpacing_four_of_sturmianStep_zero
        h0.1 q₁ q₂ tauCurrent tau₁ tau₂ z₁ z₂
        hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂
  · right
    refine ⟨h1.1, h1.2.1, h1.2.2, ?_⟩
    intro q₁ q₂ tauCurrent tau₁ tau₂ z₁ z₂ hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂
    exact
      O.not_both_nextCenteredLiftCompatible_of_stepSpacing_four_of_sturmianStep_one
        h1.1 q₁ q₂ tauCurrent tau₁ tau₂ z₁ z₂
        hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂

/--
Stage 8/9 と actual grid separation を `A` transition 上で一つに束ねた package。

current future minimum では

* actual-compatible dyadic state は defect-grid `xi_i = Z/2^δ_i` 上、
* same `Z` は centered Hensel congruenceを満たす、
* whole A block は rise-by-one centered Hensel transport を持つ、
* 開始 step は `1` なので最初の normalized completion branch の隣接二候補は
  next actual residue と同時には両立しない。
-/
theorem exists_symbol_A_currentGrid_blockTransport_and_nextBranchSeparation_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j t : ℕ}
    (hi : 0 < i)
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A)
    (hCompletionStart :
      O.endpointCompletionStart SInf hi =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent i * t) :
    ∃ Z h : ℤ,
      O.normalizedCompletionDyadicState i t =
          (Z : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i ∧
      (((O.defectActualResidue i + 1) / 4 : ℕ) : ℤ) +
          (3 : ℤ) ^ i * Z ≡ 0
        [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i] ∧
      2 * (3 : ℝ) ^ (j - i) *
          centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j) =
        centeredNormalizedCompletionCocycleResidue
            i (infiniteSurvivorDefect O.exponent i) + 4 * (h : ℝ) ∧
      (∀ (q₁ q₂ tau₁ tau₂ : ℝ) (z₁ z₂ : ℤ),
        q₁ =
            (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₁ -
              O.normalizedCompletionLiftCoefficient i t →
        q₂ =
            (2 : ℝ) ^ (1 + survivorSturmianStep i) * tau₂ -
              O.normalizedCompletionLiftCoefficient i t →
        (q₁ = q₂ + 4 ∨ q₂ = q₁ + 4) →
        O.defectActualResidueFraction (i + 1) +
            ((3 : ℝ) ^ (i + 1) / 4) * (tau₁ - 2) = (z₁ : ℝ) →
        O.defectActualResidueFraction (i + 1) +
            ((3 : ℝ) ^ (i + 1) / 4) * (tau₂ - 2) = (z₂ : ℝ) →
        False) := by
  rcases
      O.exists_futureMinimum_dyadicState_defectGrid
        SInf hi hStart hCompletionStart with ⟨Z, hXi, hCong⟩
  rcases
      O.exists_symbol_A_centeredCompletion_blockTransport_of_globalCST
        G SInf hStart hNext hA with ⟨h, hTransport, hs⟩
  refine ⟨Z, h, hXi, hCong, hTransport, ?_⟩
  intro q₁ q₂ tau₁ tau₂ z₁ z₂ hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂
  exact
    O.not_both_nextCenteredLiftCompatible_of_stepSpacing_four_of_sturmianStep_one
      hs q₁ q₂ (O.normalizedCompletionLiftCoefficient i t) tau₁ tau₂ z₁ z₂
      hRec₁ hRec₂ hSpacing hCompat₁ hCompat₂

end OddOrbit
end Collatz3
