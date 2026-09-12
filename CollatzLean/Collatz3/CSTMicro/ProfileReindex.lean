import CollatzLean.Collatz3.CSTMicro.ProfileExtraction

/-!
# Collatz3 CSTMicro Stage 5: profile width の reindex bridge

Stage 5 の canonical extraction が返す profile の型添字は

  Word.oddSteps P.compressedExponentWord

である。一方、後段の RecordFerrers / Ferrers geometry では standard path 自身の

  P.endpointOddCount

を型添字として直接使いたい。

両者は theorem として exact に等しいので、profile の数学的内容を変えずに
型添字だけを transport する薄い bridge をここに置く。
-/

namespace Collatz3
namespace Critical

/-- profile の幅を等式に沿って transport するだけの薄い reindex。 -/
def reindexProfile
    {m n : ℕ}
    (e : m = n)
    (h : Profile m) : Profile n :=
  e ▸ h

@[simp] theorem reindexProfile_rfl
    {m : ℕ}
    (h : Profile m) :
    reindexProfile rfl h = h := rfl

/-- admissibility は profile 幅の reindex で不変。 -/
theorem reindexProfile_admissible
    {m n : ℕ}
    {h : Profile m}
    (e : m = n)
    (A : Admissible h) :
    Admissible (reindexProfile e h) := by
  subst n
  simpa [reindexProfile] using A

/-- affine numerator も profile 幅の reindex では変わらない。 -/
theorem profileAffineNumerator_reindexProfile
    {m n : ℕ}
    (e : m = n)
    (h : Profile m) :
    profileAffineNumerator (reindexProfile e h) =
      profileAffineNumerator h := by
  subst n
  simp [reindexProfile]

end Critical

namespace CSTMicro
namespace FirstPassagePath

/--
Stage 5 の extracted profile を standard path の `endpointOddCount` で直接添字付けした view。

数学的 profile は同じで、型添字だけを
`compressedExponentWord_oddSteps_eq` に沿って transport している。
-/
def endpointIndexedCriticalProfile
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.Profile P.endpointOddCount :=
  Critical.reindexProfile
    (P.compressedExponentWord_oddSteps_eq hp)
    P.extractedCriticalProfile

/-- endpoint-indexed view も admissible。 -/
theorem endpointIndexedCriticalProfile_admissible
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.Admissible (P.endpointIndexedCriticalProfile hp) := by
  exact
    Critical.reindexProfile_admissible
      (P.compressedExponentWord_oddSteps_eq hp)
      (P.extractedCriticalProfile_admissible hp)

/-- endpoint-indexed view の affine numerator は元 standard path の `B` と exact に一致。 -/
theorem endpointIndexedCriticalProfile_affineNumerator_eq
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.profileAffineNumerator (P.endpointIndexedCriticalProfile hp) =
      affineConst P.word := by
  calc
    Critical.profileAffineNumerator (P.endpointIndexedCriticalProfile hp)
        = Critical.profileAffineNumerator P.extractedCriticalProfile :=
          Critical.profileAffineNumerator_reindexProfile
            (P.compressedExponentWord_oddSteps_eq hp)
            P.extractedCriticalProfile
    _ = affineConst P.word :=
          P.extractedCriticalProfile_affineNumerator_eq hp

end FirstPassagePath
end CSTMicro
end Collatz3
