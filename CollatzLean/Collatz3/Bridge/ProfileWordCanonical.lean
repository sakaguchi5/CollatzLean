import CollatzLean.Collatz3.Critical.ProfileCanonical
import CollatzLean.Collatz3.Canonical.REQ

/-!
# Collatz3: profile affine data と既存 Word canonical kernel の橋

profile と word を同一視しない。

両者が同じ affine data `(p,H,B)` を持つことだけを
薄い relation として定義し、そこから canonical coordinates の一致を導く。

重要なのは、Word と Profile の canonical start を直接比較しないこと。

両者はともに

`canonicalStartOfAffineData p H B`

から導かれるため、`SameAffineData` が与える
`p`, `H`, `B` の一致だけで canonical start の一致が従う。
-/

namespace Collatz3

namespace Critical

/--
profile `h` と word `w` が同じ affine data `(p,H,B)` を表す。

ここでは profile と word の構造そのものは同一視しない。
比較するのは次の3量だけ。

- `p`: odd-step 数
- `H`: total two-depth
- `B`: affine numerator / translate
-/
def SameAffineData
    {m : ℕ}
    (h : Profile m)
    (w : Word) : Prop :=
  Word.oddSteps w = m ∧
  Word.twoSteps w = criticalTwoDepth m ∧
  Word.affineConst w = profileAffineNumerator h

namespace SameAffineData

/--
同じ affine data なら odd-endpoint modulus も一致する。

これは `H` の一致だけから従う。
-/
theorem oddEndpointModulus_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.oddEndpointModulus w =
      profileOddEndpointModulus m := by
  change
    Arithmetic.twoPowModulus (Word.twoSteps w + 1) =
      Arithmetic.twoPowModulus (criticalTwoDepth m + 1)
  rw [A.2.1]

/--
同じ affine data なら canonical start が一致する。

両辺を `canonicalStartOfAffineData` に戻すことで、
`ZMod` の dependent transport を一切使わずに証明する。
-/
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

/--
同じ affine data なら canonical numerator が一致する。

start の一致と `(p,B)` の一致だけを使う。
-/
theorem canonicalNumerator_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.canonicalNumerator w =
      profileCanonicalNumerator h := by
  change
    3 ^ Word.oddSteps w * Word.canonicalStart w +
        Word.affineConst w =
      3 ^ m * profileCanonicalStart h +
        profileAffineNumerator h
  rw [A.1, A.2.2, canonicalStart_eq A]

/--
同じ affine data なら canonical endpoint が一致する。

numerator の一致と `H` の一致だけを使う。
-/
theorem canonicalEnd_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.canonicalEnd w =
      profileCanonicalEnd h := by
  change
    Word.canonicalNumerator w / 2 ^ Word.twoSteps w =
      profileCanonicalNumerator h / 2 ^ criticalTwoDepth m
  rw [canonicalNumerator_eq A, A.2.1]

/--
同じ affine data なら canonical drift も一致する。

start と endpoint の一致から直接従う。
-/
theorem canonicalGap_eq
    {m : ℕ}
    {h : Profile m}
    {w : Word}
    (A : SameAffineData h w) :
    Word.canonicalGap w =
      profileCanonicalGap h := by
  change
    (Word.canonicalEnd w : ℤ) -
        (Word.canonicalStart w : ℤ) =
      (profileCanonicalEnd h : ℤ) -
        (profileCanonicalStart h : ℤ)
  rw [canonicalStart_eq A, canonicalEnd_eq A]

end SameAffineData

end Critical
end Collatz3
