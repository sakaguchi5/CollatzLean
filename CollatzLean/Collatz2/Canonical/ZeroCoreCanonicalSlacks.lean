import CollatzLean.Collatz2.Global.EndpointFloorNaturalCoordinates
import CollatzLean.Collatz2.Canonical.ZeroCoreSlack

/-!
# Collatz2 Canonical: endpoint-floor true j=0 と fundamental slacks

endpoint-floor natural coordinates に、tail replay quotient `j=0` の内容

  first boundary = canonicalStart(v)
  whole endpoint = canonicalEnd(v)

だけを追加した thin packet を置く。

ここから既存 `ZeroCoreCoordinates` へ直接変換し、
fundamental slacks `a,c` と

  G + 3*c + 3*n = 2*a
  g + c = d + a

を回収する。

最終 core defect は subtraction を避け

  coreDefect = 3*n

と定義する。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- true tail replay `j=0` を natural coordinates に接続する packet。 -/
structure CanonicalZeroCoreData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) where
  natural : D.NaturalCoordinates
  boundary_eq_tailStart :
    natural.boundary =
      Word.canonicalStart natural.tail
  fullEnd_eq_tailEnd :
    Word.canonicalEnd D.word =
      Word.canonicalEnd natural.tail

namespace CanonicalZeroCoreData

/-- tail は valid。 -/
theorem tail_valid
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    Word.Valid Z.natural.tail := by
  have hFull :
      Word.Valid (1 :: Z.natural.tail) := by
    rw [← Z.natural.word_eq]
    exact D.word_valid
  intro e he
  exact hFull e (by simp [he])

/-- whole all-suffix profile を tail に落とす。 -/
theorem tail_allSuffixesContracting
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    Word.AllSuffixesContracting Z.natural.tail := by
  have hAll :
      Word.AllSuffixesContracting
        (1 :: Z.natural.tail) := by
    rw [← Z.natural.word_eq]
    exact D.allSuffixesContracting
  exact Word.AllSuffixesNegativeDeterminant.tail hAll

/-- tail 自身は contracting。 -/
theorem tail_contracting
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    Word.Contracting Z.natural.tail :=
  Z.tail_allSuffixesContracting.whole_contracting
    Z.natural.tail_nonempty

/-- 既存 `ZeroCoreCoordinates` への bridge。 -/
theorem toZeroCoreCoordinates
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    Word.ZeroCoreCoordinates
      Z.natural.tail Z.natural.n Z.natural.d := {
  tailValid := Z.tail_valid
  fullStart_add_one := by
    rw [← Z.natural.word_eq]
    exact Z.natural.fullStart_add_one
  tailStart_add_one := by
    rw [← Z.boundary_eq_tailStart]
    exact Z.natural.boundary_add_one
  tailEnd_add_one := by
    rw [← Z.fullEnd_eq_tailEnd]
    exact Z.natural.fullEnd_add_one
}

/-- canonical slack packet。 -/
structure SlackData
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) where
  a : ℕ
  c : ℕ

  twoPow_eq :
    2 ^ Word.twoSteps Z.natural.tail =
      3 * (Z.natural.n + Z.natural.d) + a

  threePow_eq :
    3 ^ Word.oddSteps Z.natural.tail =
      3 * Z.natural.n + 2 * Z.natural.d + c

  fullGap_balance :
    (AffineTransfer.ofWord (1 :: Z.natural.tail)).centerGap +
        3 * c + 3 * Z.natural.n =
      2 * a

  tailGap_balance :
    (AffineTransfer.ofWord Z.natural.tail).centerGap + c =
      Z.natural.d + a

namespace SlackData

/-- core defect。counterexample 側では exact に `3*n`。 -/
def coreDefect
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {Z : CanonicalZeroCoreData D}
    (_L : SlackData Z) : ℕ :=
  3 * Z.natural.n

/-- core defect は正。 -/
theorem coreDefect_pos
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {Z : CanonicalZeroCoreData D}
    (L : SlackData Z) :
    0 < L.coreDefect := by
  dsimp [coreDefect]
  have hn := Z.natural.n_pos
  omega

/-- full gap balance を core defect で書く。 -/
theorem fullGap_add_three_mul_c_add_coreDefect
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {Z : CanonicalZeroCoreData D}
    (L : SlackData Z) :
    (AffineTransfer.ofWord (1 :: Z.natural.tail)).centerGap +
        3 * L.c + L.coreDefect =
      2 * L.a := by
  simpa [coreDefect] using L.fullGap_balance

end SlackData

/-- fundamental slacks を構成する。 -/
noncomputable def toSlackData
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    SlackData Z := by
  classical
  let C := Z.toZeroCoreCoordinates
  let H :=
    C.exists_fundamentalSlacks_with_gapBalances
      (by
        have h := D.contracting
        rw [Z.natural.word_eq] at h
        exact h)
      Z.tail_contracting
  let a : ℕ :=
    Classical.choose H
  let Hc :=
    Classical.choose_spec H
  let c : ℕ :=
    Classical.choose Hc
  have hPack :=
    Classical.choose_spec Hc
  have hA :=
    hPack.1
  have hC :=
    hPack.2.1
  have hFull :=
    hPack.2.2.1
  have hTail :=
    hPack.2.2.2
  exact {
    a := a
    c := c
    twoPow_eq := hA
    threePow_eq := hC
    fullGap_balance := hFull
    tailGap_balance := hTail
  }

end CanonicalZeroCoreData
end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
