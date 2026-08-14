import CollatzLean.Collatz2.Mountain.FiniteHercherNarrow
import CollatzLean.Collatz2.External.BarinaHercher

/-!
# Collatz2 Mountain: Barina--Hercher finite lower bound

current A の finite positive FirstCrossing に対し

* Barina `2^71`: S > 2^71
* finite Hercher narrow division-free inequality
* Hercher Lemma 22 continued-fraction certificate

を合成して、cycle を一切仮定せず

  oddSteps(w) >= 72057431991

を得る。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- unbounded current A の canonical start は `2^71` より大きい。 -/
theorem canonicalStart_gt_twoPow71
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hBarina : External.BarinaTwoPow71Input) :
    2 ^ 71 < Word.canonicalStart D.word := by
  have h :=
    hBarina.unbounded_odd_orbit_above
      O D.unbounded D.startIndex
  calc
    2 ^ 71 < O.value D.startIndex := h
    _ = Word.canonicalStart D.word := by
      simpa [word] using D.startCanonical

/--
Barina + finite Hercher + continued fraction から current A の odd-step 数の絶対下界。
-/
theorem oddSteps_ge_72057431991
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hBarina : External.BarinaTwoPow71Input)
    (hCF : External.HercherTwoPow71DenominatorInput) :
    72057431991 ≤ Word.oddSteps D.word := by
  let K := Word.oddSteps D.word
  let H := Word.twoSteps D.word
  have hKPos : 0 < K := by
    dsimp [K, Word.oddSteps]
    exact List.length_pos_iff.mpr D.word_nonempty
  have hContract : 3 ^ K < 2 ^ H := by
    dsimp [K, H]
    exact
      (Word.contracting_iff_threePow_lt_twoPow).1
        D.contracting
  have hStart :
      2 ^ 71 < Word.canonicalStart D.word :=
    D.canonicalStart_gt_twoPow71 hBarina
  have hNarrow :
      3 * (2 ^ H - 3 ^ K) * 2 ^ 71 <
        K * 3 ^ K := by
    dsimp [K, H]
    exact
      D.finiteHercherNarrow_of_lowerStart hStart
  have hDen :=
    hCF.denominator_bound K H hKPos hContract hNarrow
  rw [Arithmetic.hercherTwoPow71_denominator_eq] at hDen
  exact hDen

/-- repository default external inputs を使う convenience theorem。 -/
theorem oddSteps_ge_72057431991_external
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    72057431991 ≤ Word.oddSteps D.word :=
  D.oddSteps_ge_72057431991
    External.barinaTwoPow71
    External.hercherTwoPow71Denominator

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
