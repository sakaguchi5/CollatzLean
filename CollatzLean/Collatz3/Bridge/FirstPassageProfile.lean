import CollatzLean.Collatz3.Semantics.FirstPassage
import CollatzLean.Collatz3.Critical.ProfileExtraction
import CollatzLean.Collatz3.Bridge.ProfileWordCanonical

/-!
# Collatz3: actual first-passage → finite profile → canonical data

ここで初めて actual `Runs` と pure finite profile を接続する。
actuality から得る `Valid` と pure first-passage geometry だけを使い、
抽出 profile の admissibility と `(p,H,B)` 一致を導く。
-/

namespace Collatz3
namespace ActualFirstPassage

/-- actual first-passage から抽出した finite profile は admissible。 -/
theorem extractedProfile_admissible
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Critical.Admissible (Critical.profileFromWord w) :=
  Critical.profileFromWord_admissible h.critical h.valid

/-- 抽出 profile の checkpoint は actual word の prefix two-depth。 -/
theorem extractedProfile_checkpoint_eq_prefixTwoDepth
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y)
    (k : Fin (Word.oddSteps w)) :
    Critical.checkpoint (Critical.profileFromWord w) k =
      Word.prefixTwoDepth w k.1 :=
  Critical.checkpoint_profileFromWord_eq_prefixTwoDepth h.critical k

/-- 抽出 profile の affine numerator は actual word の affine translation。 -/
theorem extractedProfile_affineNumerator_eq_affineConst
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Critical.profileAffineNumerator (Critical.profileFromWord w) =
      Word.affineConst w :=
  Critical.profileAffineNumerator_profileFromWord_eq_affineConst h.critical

/--
actual first-passage word と抽出 profile は同じ affine data `(p,H,B)` を持つ。
これが actual → pure bridge の中心定理。
-/
theorem sameAffineData_extractedProfile
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Critical.SameAffineData (Critical.profileFromWord w) w := by
  constructor
  · rfl
  · constructor
    · exact h.critical.totalTwoDepth_eq
    · exact h.extractedProfile_affineNumerator_eq_affineConst.symm

/-- actual first-passage の canonical start は抽出 profile の `R` と一致。 -/
theorem canonicalStart_eq_extractedProfile
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Word.canonicalStart w =
      Critical.profileCanonicalStart (Critical.profileFromWord w) :=
  (h.sameAffineData_extractedProfile).canonicalStart_eq

/-- actual first-passage の canonical endpoint は抽出 profile の `Y` と一致。 -/
theorem canonicalEnd_eq_extractedProfile
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Word.canonicalEnd w =
      Critical.profileCanonicalEnd (Critical.profileFromWord w) :=
  (h.sameAffineData_extractedProfile).canonicalEnd_eq

/-- actual first-passage の canonical drift は抽出 profile の `Q` と一致。 -/
theorem canonicalGap_eq_extractedProfile
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Word.canonicalGap w =
      Critical.profileCanonicalGap (Critical.profileFromWord w) :=
  (h.sameAffineData_extractedProfile).canonicalGap_eq

end ActualFirstPassage
end Collatz3
