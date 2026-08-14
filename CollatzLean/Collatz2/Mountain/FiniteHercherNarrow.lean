import CollatzLean.Collatz2.Global.EndpointFloorNaturalCoordinates
import CollatzLean.Collatz2.Canonical.PrefixBudgetExcess

/-!
# Collatz2 Mountain: finite Hercher narrow interval, division-free form

cycle の積 identity を使わず、current A が持つ

* actual canonical positive return S < T
* whole Contracting: 3^K < 2^H
* FirstCrossing proper-prefix budget: 3B < K*3^K

だけから finite Hercher 型の narrow interval を得る。

real log を導入する直前の exact integer formは

  3 * (2^H - 3^K) * S < K * 3^K.      (FH)

(FH) を正数で割り、`log(1+x) < x` を使えば

  log(3)/log(2)
    < H/K
    < log(3)/log(2) + 1/(3*S*log(2))

となる。

このファイルでは downstream の continued-fraction certificate がそのまま使えるよう、
Nat subtraction を含む division-free formを正本とする。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- coefficient gap `2^H - 3^K` は正。 -/
theorem twoThreeGap_pos
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    0 <
      2 ^ Word.twoSteps D.word -
        3 ^ Word.oddSteps D.word := by
  have hC :=
    (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
  exact Nat.sub_pos_of_lt hC

/--
positive canonical return から、coefficient gap times start は affine translation 未満。

  (2^H - 3^K) * S < B.
-/
theorem gap_mul_start_lt_affineConst
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    (2 ^ Word.twoSteps D.word -
        3 ^ Word.oddSteps D.word) *
        Word.canonicalStart D.word <
      Word.affineConst D.word := by
  let A := 2 ^ Word.twoSteps D.word
  let C := 3 ^ Word.oddSteps D.word
  let S := Word.canonicalStart D.word
  let T := Word.canonicalEnd D.word
  let B := Word.affineConst D.word
  have hC : C < A := by
    dsimp [A, C]
    exact
      (Word.contracting_iff_threePow_lt_twoPow).1
        D.contracting
  have hPos : S < T := by
    dsimp [S, T]
    exact D.canonicalPositive
  have hReal : A * T = C * S + B := by
    dsimp [A, C, S, T, B]
    exact
      (Word.realizes_iff D.word _ _).1
        D.runsCanonical.realizes
  have hGapAdd : (A - C) + C = A :=
    Nat.sub_add_cancel (Nat.le_of_lt hC)
  have hAPos : 0 < A := by
    dsimp [A]
    exact Nat.pow_pos (by omega)
  have hASlt : A * S < A * T :=
    (Nat.mul_lt_mul_left hAPos).2 hPos
  rw [hReal] at hASlt
  by_contra hnot
  have hBle : B ≤ (A - C) * S :=
    Nat.le_of_not_gt hnot
  have hRhsLe : C * S + B ≤ A * S := by
    calc
      C * S + B
          ≤ C * S + (A - C) * S :=
            Nat.add_le_add_left hBle _
      _ = ((A - C) + C) * S := by ring
      _ = A * S := by rw [hGapAdd]
  omega

/--
## Finite Hercher narrow inequality

current A の finite positive FirstCrossing について

  3 * gap * S < K * 3^K.

周期性を一切使わない。
-/
theorem finiteHercherNarrow_divisionFree
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    3 *
        (2 ^ Word.twoSteps D.word -
          3 ^ Word.oddSteps D.word) *
        Word.canonicalStart D.word <
      Word.oddSteps D.word *
        3 ^ Word.oddSteps D.word := by
  have hGap := D.gap_mul_start_lt_affineConst
  have hTripleGap :
      3 *
          ((2 ^ Word.twoSteps D.word -
              3 ^ Word.oddSteps D.word) *
            Word.canonicalStart D.word) <
        3 * Word.affineConst D.word :=
    (Nat.mul_lt_mul_left (by omega : 0 < (3 : ℕ))).2 hGap
  have hF : Word.FirstCrossing D.word := by
    simpa [word] using D.firstCrossing
  have hPrefix :
      3 * Word.affineConst D.word <
        Word.oddSteps D.word *
          3 ^ Word.oddSteps D.word :=
    hF.three_mul_affineConst_lt_oddSteps_mul_threePow
      D.word_length_gt_one
  have h := lt_trans hTripleGap hPrefix
  simpa [Nat.mul_assoc] using h

/--
start に任意の strict lower bound `X < S` があれば、同じ denominator window を
`X` に弱めて使える。
-/
theorem finiteHercherNarrow_of_lowerStart
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {X : ℕ}
    (hX : X < Word.canonicalStart D.word) :
    3 *
        (2 ^ Word.twoSteps D.word -
          3 ^ Word.oddSteps D.word) * X <
      Word.oddSteps D.word *
        3 ^ Word.oddSteps D.word := by
  let G :=
    2 ^ Word.twoSteps D.word -
      3 ^ Word.oddSteps D.word
  have hG : 0 < G := by
    dsimp [G]
    exact D.twoThreeGap_pos
  have hScale : 3 * G * X < 3 * G * Word.canonicalStart D.word := by
    have h3G : 0 < 3 * G := Nat.mul_pos (by omega) hG
    exact (Nat.mul_lt_mul_left h3G).2 hX
  exact lt_trans hScale (by
    simpa [G] using D.finiteHercherNarrow_divisionFree)

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
