import CollatzLean.Collatz3.CSTConditional.FutureMinimumActualBranchUniqueness
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionHensel

/-!
# Collatz3 CSTConditional: completion branch selector の整数版

前段では actual-compatible branch digit が高々一つであることを得た。
ここでは canonical natural completion が連続幅 `m,m+1` で実在する場合、
その実際の next lift を witness にして、actual-compatible integer branch digit が
**存在しかつ一意**であることをまとめる。

新しい selector 関数や branch predicate は定義しない。
`∃! j : ℤ, ...` の derived theorem としてのみ保存する。

branch digit `j` が選ぶものは、ある `tauNext ∈ (0,4)` と整数 `z` が存在して

`rho_m + 4j = 2^(1+s_m) tauNext - tau_m`

かつ

`theta_(m+1) + (3^(m+1)/4)(tauNext-2) = z`

を同時に満たすことである。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
連続する canonical natural completion が与えられたとき、
actual-compatible normalized completion branch digit は `∃!` で一意に選ばれる。

selector 自体は定義せず、存在一意性だけを API とする。
-/
theorem exists_unique_actualCompatible_normalizedCompletionBranchDigit
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (huPos : 0 < u)
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    ∃! j : ℤ,
      ∃ tauNext : ℝ, ∃ z : ℤ,
        normalizedCompletionCocycleResidue
              m (infiniteSurvivorDefect O.exponent m) + 4 * (j : ℝ) =
            (2 : ℝ) ^ (1 + survivorSturmianStep m) * tauNext -
              O.normalizedCompletionLiftCoefficient m t ∧
        (0 < tauNext ∧ tauNext < 4) ∧
        O.defectActualResidueFraction (m + 1) +
            ((3 : ℝ) ^ (m + 1) / 4) * (tauNext - 2) =
          (z : ℝ) := by
  rcases
      O.exists_normalizedCompletionLiftStep_residue_digit
        SInf hm hStartM hStartN with ⟨j, hj⟩
  have hRec :=
    O.normalizedCompletionLiftStep_eq_sturmianScale_mul_sub
      SInf m t u
  have hTauN :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf huPos hu
  rcases
      O.exists_integer_defectActualResidueFraction_add_scaled_centeredLift
        SInf (by omega : 0 < m + 1) hStartN with ⟨z, hz⟩
  have hCompat :
      O.defectActualResidueFraction (m + 1) +
          ((3 : ℝ) ^ (m + 1) / 4) *
            (O.normalizedCompletionLiftCoefficient (m + 1) u - 2) =
        (z : ℝ) := by
    simpa [centeredNormalizedCompletionLiftCoefficient] using hz
  have hBranchRec :
      normalizedCompletionCocycleResidue
            m (infiniteSurvivorDefect O.exponent m) + 4 * (j : ℝ) =
          (2 : ℝ) ^ (1 + survivorSturmianStep m) *
              O.normalizedCompletionLiftCoefficient (m + 1) u -
            O.normalizedCompletionLiftCoefficient m t := by
    calc
      normalizedCompletionCocycleResidue
            m (infiniteSurvivorDefect O.exponent m) + 4 * (j : ℝ)
          =
          ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
            (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := hj.symm
      _ =
          (2 : ℝ) ^ (1 + survivorSturmianStep m) *
              O.normalizedCompletionLiftCoefficient (m + 1) u -
            O.normalizedCompletionLiftCoefficient m t := hRec
  refine ⟨j, ?_, ?_⟩
  · exact
      ⟨O.normalizedCompletionLiftCoefficient (m + 1) u, z,
        hBranchRec, hTauN, hCompat⟩
  · intro j' hj'
    rcases hj' with ⟨tauNext, z', hRec', hTauNext, hCompat'⟩
    have hEq :=
      O.actualCompatible_normalizedCompletionBranchDigit_unique
        (m := m)
        (O.normalizedCompletionLiftCoefficient m t)
        (normalizedCompletionCocycleResidue
          m (infiniteSurvivorDefect O.exponent m))
        (O.normalizedCompletionLiftCoefficient (m + 1) u)
        tauNext
        j j' z z'
        hBranchRec hRec' hTauN hTauNext hCompat hCompat'
    exact hEq.symm

end OddOrbit
end Collatz3
