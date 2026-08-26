import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianStrongOverlap
import Mathlib.Data.ZMod.Basic

/-!
# Strong overlap -> finite Xi identity target

Boundary A strong matching の arithmetic core を finite `ZMod (2^e)` identity として
切り出す。

各 `j`, `e <= q_j+q_{j+1}-1`, `e = beattyIndex m` について

  P_j + Xi_e(m) Q_j = 0  in ZMod(2^e)

を示せば、`BoundaryXiCandidate e R` の residue equality から

  2^e | P_j + R Q_j

が従う。

このファイルでは後者の変換を完全に証明する。
残る mathematical bridge は
`CriticalSturmianStrongOverlap` から `CriticalFiniteXiIdentity` を構成する部分だけ。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- index `j`, precision `e`, truncation height `m` の finite Xi identity。 -/
def CriticalFiniteXiIdentityAt
    (D : CriticalContinuedFractionData)
    (j e m : ℕ) : Prop :=
  (correctedChristoffelP D j : ZMod (2 ^ e)) +
      criticalXiTruncationClass e m *
        (correctedChristoffelQ D j : ZMod (2 ^ e)) = 0

/-- strong certified precision 全体での finite Xi identity family。 -/
structure CriticalFiniteXiIdentity
    (D : CriticalContinuedFractionData) where
  identity :
    ∀ j e m : ℕ,
      D.start ≤ j →
      e ≤ strongDenominatorWindowUpper D.q j →
      e = beattyIndex m →
      CriticalFiniteXiIdentityAt D j e m

namespace CriticalFiniteXiIdentity

/--
finite Xi identity と candidate residue equality から純整数 divisibility を得る。
-/
theorem matches_of_candidate
    {D : CriticalContinuedFractionData}
    (I : CriticalFiniteXiIdentity D)
    {j e R : ℕ}
    (hjStart : D.start ≤ j)
    (hPrecision : e ≤ strongDenominatorWindowUpper D.q j)
    (hCandidate : BoundaryXiCandidate e R) :
    MatchesAtTwoPower e
      (correctedChristoffelP D j)
      (correctedChristoffelQ D j)
      R := by
  rcases hCandidate with ⟨m, hem, hResidue⟩
  let : NeZero (2 ^ e) := ⟨by positivity⟩
  have hRcast :
      (R : ZMod (2 ^ e)) =
        criticalXiTruncationClass e m := by
    apply ZMod.val_injective (2 ^ e)
    simpa only [ZMod.val_natCast] using hResidue
  have hXi :
      CriticalFiniteXiIdentityAt D j e m :=
    I.identity j e m hjStart hPrecision hem
  have hLinearCast :
      ((correctedChristoffelP D j +
          (R : ℤ) * correctedChristoffelQ D j : ℤ) :
        ZMod (2 ^ e)) = 0 := by
    push_cast
    rw [hRcast]
    exact hXi
  have hDvd :
      (((2 ^ e : ℕ) : ℤ)) ∣
        correctedChristoffelP D j +
          (R : ℤ) * correctedChristoffelQ D j :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (correctedChristoffelP D j +
        (R : ℤ) * correctedChristoffelQ D j)
      (2 ^ e)).mp hLinearCast
  unfold MatchesAtTwoPower
  simpa using hDvd

end CriticalFiniteXiIdentity

/--
strong Sturmian overlap から finite Xi identity を作る最後の finite bridge。

この structure の唯一の field が、次に standard-word / Christoffel recurrence と
`BoundaryXiTruncation` の finite scan identity から埋める本質的 theorem obligation。
-/
structure CriticalSturmianFiniteXiBridge
    (D : CriticalContinuedFractionData)
    (O : CriticalSturmianStrongOverlap D) where
  finiteIdentity : CriticalFiniteXiIdentity D

end ExternalArithmetic
end CSTMicro
end Collatz2
