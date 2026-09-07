import CollatzLean.Collatz3.Semantics.ReachOne
import CollatzLean.Collatz3.Bridge.RunsToCanonical

/-!
# Collatz3: 終点 1 仮定からの canonical consequence

`EndsAtOne` 自体は Semantics 層の薄い語彙に留め、affine / canonical の強い帰結は
この Bridge 層で初めて導く。
-/

namespace Collatz3
namespace ReachOne

/-- 終点 1 の actual run が持つ endpoint equation。 -/
theorem endpointEquation
    {w : Word} {x : ℕ}
    (h : EndsAtOne w x) :
    w.EndpointEquation x 1 := by
  exact (show Runs w x 1 from h).endpointEquation

/-- 終点 1 なら `2^H = 3^p x + B`。 -/
theorem affineEquation
    {w : Word} {x : ℕ}
    (h : EndsAtOne w x) :
    2 ^ Word.twoSteps w =
      3 ^ Word.oddSteps w * x + Word.affineConst w := by
  have hEq := (Word.endpointEquation_iff w x 1).1 (endpointEquation h)
  simpa using hEq

/-- 終点 1 なら signed translation は `B = 2^H - 3^p x`。 -/
theorem affineConst_int_eq
    {w : Word} {x : ℕ}
    (h : EndsAtOne w x) :
    (Word.affineConst w : ℤ) =
      (2 : ℤ) ^ Word.twoSteps w -
        (3 : ℤ) ^ Word.oddSteps w * (x : ℤ) := by
  have hNat := affineEquation h
  have hInt := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hInt
  calc
    (Word.affineConst w : ℤ)
        = ((3 : ℤ) ^ Word.oddSteps w * (x : ℤ) +
            (Word.affineConst w : ℤ)) -
            (3 : ℤ) ^ Word.oddSteps w * (x : ℤ) := by ring
    _ = (2 : ℤ) ^ Word.twoSteps w -
          (3 : ℤ) ^ Word.oddSteps w * (x : ℤ) := by rw [← hInt]

/--
非空の終点 1 run は canonical lift の `k = 0` そのもの。
したがって `R = x`, `Y = 1`, `Q = 1-x`。
-/
theorem canonicalCoordinates
    {w : Word} {x : ℕ}
    (h : EndsAtOne w x)
    (hne : w ≠ []) :
    Word.canonicalStart w = x ∧
      Word.canonicalEnd w = 1 ∧
      Word.canonicalGap w = (1 : ℤ) - (x : ℤ) := by
  have hRun : Runs w x 1 := h
  rcases hRun.exists_canonicalLift hne with ⟨k, hx, hy⟩
  have hEndPos : 0 < Word.canonicalEnd w := by
    rcases Word.canonicalEnd_odd w with ⟨t, ht⟩
    omega
  have hLiftZero : 2 * (3 ^ Word.oddSteps w) * k = 0 := by
    omega
  have hk : k = 0 := by
    rcases Nat.mul_eq_zero.mp hLiftZero with hCoeff | hk
    · have hCoeffPos : 0 < 2 * (3 ^ Word.oddSteps w) :=
        Nat.mul_pos (by decide) (Arithmetic.threePow_pos _)
      omega
    · exact hk
  subst k
  have hStart : Word.canonicalStart w = x := by
    simpa using hx.symm
  have hEnd : Word.canonicalEnd w = 1 := by
    simpa using hy.symm
  refine ⟨hStart, hEnd, ?_⟩
  simp [Word.canonicalGap, hStart, hEnd]

/-- first hit は特に上の canonical 座標固定を満たす。 -/
theorem firstHit_canonicalCoordinates
    {w : Word} {x : ℕ}
    (h : FirstHitsOne w x) :
    Word.canonicalStart w = x ∧
      Word.canonicalEnd w = 1 ∧
      Word.canonicalGap w = (1 : ℤ) - (x : ℤ) :=
  canonicalCoordinates h.endsAtOne h.word_nonempty

end ReachOne
end Collatz3
