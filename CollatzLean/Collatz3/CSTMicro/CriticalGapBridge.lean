import CollatzLean.Collatz3.Arithmetic.CriticalGap
import CollatzLean.Collatz3.CSTMicro.Capacity


/-!
# Collatz3 CSTMicro: pure critical-gap input から single-lift へ

CSTMicro 内の path-wise 仮定

  endpointOddCount P < 3 * terminalGap P

を、path の外に置いた純整数論 interface

  Arithmetic.CriticalGapLinearBound

から一括して供給する。

これにより combinatorics / parity residue / capacity の証明は
2--3 gap の解析的・整数論的証明から独立したまま保たれる。
-/

namespace Collatz3
namespace CSTMicro
namespace FirstPassagePath

/-- universal critical-gap lower bound から各 first-passage path の single-lift 条件を得る。 -/
theorem singleLiftGapCondition_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hGap : Arithmetic.CriticalGapLinearBound) :
    P.SingleLiftGapCondition := by
  unfold Arithmetic.CriticalGapLinearBound at hGap
  have h := hGap P.endpointOddCount
  unfold SingleLiftGapCondition
  rw [P.terminalGap_eq_criticalGap]
  simpa [Arithmetic.criticalGap] using h

/-- stronger interface `criticalGap p ≥ p` からも各 path の single-lift 条件を得る。 -/
theorem singleLiftGapCondition_of_criticalGapAtLeastOddCount
    (P : FirstPassagePath)
    (hGap : Arithmetic.CriticalGapAtLeastOddCount) :
    P.SingleLiftGapCondition := by
  exact P.singleLiftGapCondition_of_criticalGapLinearBound
    (Arithmetic.criticalGapLinearBound_of_atLeastOddCount hGap)

/--
pure critical-gap lower bound のもとでは、非下降 affine realization の start は
最小 parity representative に一致する。
-/
theorem nondecreasing_start_eq_leastRepresentative_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hGap : Arithmetic.CriticalGapLinearBound)
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hxy : x ≤ y) :
    x = leastRepresentative P.word := by
  exact P.nondecreasing_start_eq_leastRepresentative
    (P.singleLiftGapCondition_of_criticalGapLinearBound hGap) h hxy

/-- exact parity trace についての universal single-lift reduction。 -/
theorem nondecreasing_trace_start_eq_leastRepresentative_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hGap : Arithmetic.CriticalGapLinearBound)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y) :
    x = leastRepresentative P.word := by
  exact P.nondecreasing_trace_start_eq_leastRepresentative
    (P.singleLiftGapCondition_of_criticalGapLinearBound hGap) h hxy

/--
最小 representative 以外の affine realization は strict descent する。
したがって higher parity lifts はすべて排除される。
-/
theorem strictDescent_of_start_ne_leastRepresentative_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hGap : Arithmetic.CriticalGapLinearBound)
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hx : x ≠ leastRepresentative P.word) :
    y < x := by
  by_contra hNot
  have hxy : x ≤ y := by omega
  have hEq :=
    P.nondecreasing_start_eq_leastRepresentative_of_criticalGapLinearBound
      hGap h hxy
  exact hx hEq

/-- exact parity trace 版: canonical representative 以外はすべて strict descent。 -/
theorem strictDescent_of_trace_start_ne_leastRepresentative_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hGap : Arithmetic.CriticalGapLinearBound)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hx : x ≠ leastRepresentative P.word) :
    y < x := by
  exact P.strictDescent_of_start_ne_leastRepresentative_of_criticalGapLinearBound
    hGap h.affine hx

/-- universal critical-gap bound のもとで、非下降 affine start は高々一つ。 -/
theorem nondecreasing_start_unique_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hGap : Arithmetic.CriticalGapLinearBound)
    {x₁ y₁ x₂ y₂ : ℕ}
    (h₁ : AffineRealizes P.word x₁ y₁)
    (h₂ : AffineRealizes P.word x₂ y₂)
    (h₁nd : x₁ ≤ y₁)
    (h₂nd : x₂ ≤ y₂) :
    x₁ = x₂ := by
  have hGapP := P.singleLiftGapCondition_of_criticalGapLinearBound hGap
  exact P.nondecreasing_start_unique hGapP h₁ h₂ h₁nd h₂nd

end FirstPassagePath
end CSTMicro
end Collatz3
