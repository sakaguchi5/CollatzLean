import CollatzLean.Collatz3.Critical.ProfileCanonical
import CollatzLean.Collatz3.Canonical.REQ

/-!
# Collatz3: Profile / Word affine data bridge

Profile と Word を同一視しない。
両者が同じ affine data `(p,H,B)` を持つことだけを薄い relation として定義し、
共有 canonical 核から `R,Y,Q` の一致を導く。
-/

namespace Collatz3
namespace Critical

/--
profile `h` と word `w` が同じ affine data `(p,H,B)` を表す。
actuality / admissibility / minimality はここに混ぜない。
-/
def SameAffineData
    {m : ℕ}
    (h : Profile m)
    (w : Word) : Prop :=
  Word.oddSteps w = m ∧
  Word.twoSteps w = criticalTwoDepth m ∧
  Word.affineConst w = profileAffineNumerator h

namespace SameAffineData

/-- 同じ affine data なら odd-endpoint modulus が一致。 -/
theorem oddEndpointModulus_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.oddEndpointModulus w =
      profileOddEndpointModulus m := by
  change
    oddEndpointModulusOfAffineData (Word.twoSteps w) =
      oddEndpointModulusOfAffineData (criticalTwoDepth m)
  rw [A.2.1]

/-- 同じ affine data なら canonical start `R` が一致。 -/
theorem canonicalStart_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.canonicalStart w =
      profileCanonicalStart h := by
  rcases A with ⟨hp, hH, hB⟩
  change
    canonicalStartOfAffineData
        (Word.oddSteps w)
        (Word.twoSteps w)
        (Word.affineConst w) =
      canonicalStartOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h)
  rw [hp, hH, hB]

/-- 同じ affine data なら canonical numerator が一致。 -/
theorem canonicalNumerator_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.canonicalNumerator w =
      profileCanonicalNumerator h := by
  rcases A with ⟨hp, hH, hB⟩
  change
    canonicalNumeratorOfAffineData
        (Word.oddSteps w)
        (Word.twoSteps w)
        (Word.affineConst w) =
      canonicalNumeratorOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h)
  rw [hp, hH, hB]

/-- 同じ affine data なら canonical endpoint `Y` が一致。 -/
theorem canonicalEnd_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.canonicalEnd w =
      profileCanonicalEnd h := by
  rcases A with ⟨hp, hH, hB⟩
  change
    canonicalEndOfAffineData
        (Word.oddSteps w)
        (Word.twoSteps w)
        (Word.affineConst w) =
      canonicalEndOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h)
  rw [hp, hH, hB]

/-- 同じ affine data なら canonical drift `Q` が一致。 -/
theorem canonicalGap_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.canonicalGap w =
      profileCanonicalGap h := by
  rcases A with ⟨hp, hH, hB⟩
  change
    canonicalGapOfAffineData
        (Word.oddSteps w)
        (Word.twoSteps w)
        (Word.affineConst w) =
      canonicalGapOfAffineData
        m
        (criticalTwoDepth m)
        (profileAffineNumerator h)
  rw [hp, hH, hB]

end SameAffineData

end Critical
end Collatz3
