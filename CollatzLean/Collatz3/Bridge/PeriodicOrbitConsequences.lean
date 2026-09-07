import CollatzLean.Collatz3.Semantics.PeriodicOrbit
import CollatzLean.Collatz3.Bridge.RunsToCanonical

/-!
# Collatz3: actual periodic orbit からの canonical consequence

文字列反復は使わない。actual return `Runs w x x` だけから affine relation と
canonical lift 条件を導く。
-/

namespace Collatz3
namespace OrbitReturn

/-- actual return が持つ endpoint equation。 -/
theorem endpointEquation
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    w.EndpointEquation x x :=
  h.run.endpointEquation

/-- actual return では `2^H x = 3^p x + B`。 -/
theorem affineEquation
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    2 ^ Word.twoSteps w * x =
      3 ^ Word.oddSteps w * x + Word.affineConst w :=
  (Word.endpointEquation_iff w x x).1 (endpointEquation h)

/-- actual return では `B = (2^H - 3^p) x`。 -/
theorem affineConst_int_eq_scaleGap_mul_start
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    (Word.affineConst w : ℤ) =
      Word.signedScaleGap w * (x : ℤ) := by
  have hNat := affineEquation h
  have hInt := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hInt
  calc
    (Word.affineConst w : ℤ)
        = (2 : ℤ) ^ Word.twoSteps w * (x : ℤ) -
            (3 : ℤ) ^ Word.oddSteps w * (x : ℤ) := by
              rw [hInt]
              ring
    _ = ((2 : ℤ) ^ Word.twoSteps w -
          (3 : ℤ) ^ Word.oddSteps w) * (x : ℤ) := by ring
    _ = Word.signedScaleGap w * (x : ℤ) := by
          simp [Word.signedScaleGap_eq]

/-- actual return も canonical pair からの一意な affine lift。 -/
theorem existsCanonicalLiftIndex
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    ∃ k : ℕ,
      x = Word.canonicalStart w + Word.oddEndpointModulus w * k ∧
      x = Word.canonicalEnd w + 2 * (3 ^ Word.oddSteps w) * k :=
  h.run.exists_canonicalLift h.word_nonempty

/--
actual return なら canonical gap は signed scale gap の `2k` 倍。
`Q = 2 k (2^H - 3^p)`。
-/
theorem canonicalGap_is_evenScaleGapMultiple
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    ∃ k : ℕ,
      Word.canonicalGap w =
        2 * (k : ℤ) * Word.signedScaleGap w := by
  rcases existsCanonicalLiftIndex h with ⟨k, hx, hy⟩
  have hGap := Word.lift_gap_formula
    (w := w) (x := x) (y := x) (k := k) hx hy
  simp only [sub_self] at hGap
  refine ⟨k, ?_⟩
  exact sub_eq_zero.mp hGap.symm

/-- primitive return にも同じ canonical multiple 条件が従う。 -/
theorem primitive_canonicalGap_is_evenScaleGapMultiple
    {w : Word} {x : ℕ}
    (h : PrimitiveReturn w x) :
    ∃ k : ℕ,
      Word.canonicalGap w =
        2 * (k : ℤ) * Word.signedScaleGap w :=
  canonicalGap_is_evenScaleGapMultiple h.returnsTo

/-- 非自明周期にも同じ canonical multiple 条件が従う。 -/
theorem nontrivial_canonicalGap_is_evenScaleGapMultiple
    {w : Word} {x : ℕ}
    (h : IsNontrivialPeriodicOrbit w x) :
    ∃ k : ℕ,
      Word.canonicalGap w =
        2 * (k : ℤ) * Word.signedScaleGap w :=
  primitive_canonicalGap_is_evenScaleGapMultiple h.1

end OrbitReturn
end Collatz3
