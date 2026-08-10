import CollatzLean.Collatz.Canonical.PrependOneCoreZeroObstruction
import CollatzLean.Collatz.External.TwoThreeGap

/-!
# quotient zero obstruction の polynomial canonical-start bound

smallest-first paradoxical exact obstruction の exact return equation

`D = G*S + 2^(J+1)*n`

と、all-suffix contracting から得る sharp affine bound

`3*D < p*2^J`

を組み合わせる。さらに Baker 型 polynomial gap

`3^p <= K*(p+1)^A*G`

を用いると、canonical start `S` は

`3*S < (p - 6*n) * (K*(p+1)^A + 1)`

を満たす。

ここでは `n` を existential witness のまま保持し、同時に `6*n < p` も記録する。
-/

namespace Collatz
namespace Word

/--
smallest-first paradoxical exact obstruction と Baker 型 polynomial gap から、
return witness `n` を保持した polynomial canonical-start bound を得る。
-/
theorem SmallestFirstParadoxicalExactObstruction.polynomialCanonicalStartBound
    {w : Collatz.Word}
    (O : SmallestFirstParadoxicalExactObstruction w)
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ K A n : ℕ,
      0 < K ∧
      0 < n ∧
      w.canonicalEnd = w.canonicalStart + 2 * n ∧
      w.affineConst =
        w.contractingGap * w.canonicalStart +
          2 ^ (w.twoSteps + 1) * n ∧
      6 * n < w.oddSteps ∧
      3 * w.canonicalStart <
        (w.oddSteps - 6 * n) *
          (K * (w.oddSteps + 1) ^ A + 1) := by
  rcases hGap with ⟨K, A, hKpos, hBaker⟩
  rcases O.exactReturn with ⟨n, hnPos, hreturn, hexact⟩
  have hAffine :
      3 * w.affineConst <
        w.oddSteps * 2 ^ w.twoSteps :=
    Word.AllSuffixesContracting.three_mul_affineConst_lt_oddSteps
      O.firstCrossing.nonempty O.allSuffixesContracting
  have hAffine' := hAffine
  rw [hexact, pow_succ] at hAffine'
  have hBudget :
      3 * w.contractingGap * w.canonicalStart +
          (6 * n) * 2 ^ w.twoSteps <
        w.oddSteps * 2 ^ w.twoSteps := by
    nlinarith [hAffine']
  have hPowPos : 0 < 2 ^ w.twoSteps :=
    Nat.pow_pos (by omega)
  have hSixScaled :
      (6 * n) * 2 ^ w.twoSteps <
        w.oddSteps * 2 ^ w.twoSteps := by
    calc
      (6 * n) * 2 ^ w.twoSteps
          ≤ 3 * w.contractingGap * w.canonicalStart +
              (6 * n) * 2 ^ w.twoSteps := by
                omega
      _ < w.oddSteps * 2 ^ w.twoSteps := hBudget
  have hSix : 6 * n < w.oddSteps :=
    (Nat.mul_lt_mul_right hPowPos).1 hSixScaled
  have hpPos : 0 < w.oddSteps := by
    simpa [Word.oddSteps] using
      List.length_pos_of_ne_nil O.firstCrossing.nonempty
  have hContract :
      3 ^ w.oddSteps < 2 ^ w.twoSteps :=
    O.firstCrossing.terminalContracting
  have hBakerGap :
      3 ^ w.oddSteps ≤
        K * (w.oddSteps + 1) ^ A * w.contractingGap := by
    simpa [Word.contractingGap] using
      hBaker w.oddSteps w.twoSteps hpPos hContract
  have hGapEq :
      3 ^ w.oddSteps + w.contractingGap =
        2 ^ w.twoSteps := by
    unfold Word.contractingGap
    exact Nat.add_sub_of_le (Nat.le_of_lt hContract)
  have hPowBound :
      2 ^ w.twoSteps ≤
        (K * (w.oddSteps + 1) ^ A + 1) *
          w.contractingGap := by
    calc
      2 ^ w.twoSteps
          = 3 ^ w.oddSteps + w.contractingGap := hGapEq.symm
      _ ≤ K * (w.oddSteps + 1) ^ A * w.contractingGap +
            w.contractingGap :=
          Nat.add_le_add_right hBakerGap w.contractingGap
      _ = (K * (w.oddSteps + 1) ^ A + 1) *
            w.contractingGap := by ring
  have hpDecomp :
      w.oddSteps =
        (w.oddSteps - 6 * n) + 6 * n := by
    exact
      (Nat.sub_add_cancel
        (Nat.le_of_lt hSix)).symm
  have hMulDecomp :
      w.oddSteps * 2 ^ w.twoSteps =
        (w.oddSteps - 6 * n) * 2 ^ w.twoSteps +
          (6 * n) * 2 ^ w.twoSteps := by
    calc
      w.oddSteps * 2 ^ w.twoSteps
          =
        ((w.oddSteps - 6 * n) + 6 * n) *
          2 ^ w.twoSteps := by
            exact
              congrArg
                (fun p : ℕ => p * 2 ^ w.twoSteps)
                hpDecomp
      _ =
        (w.oddSteps - 6 * n) * 2 ^ w.twoSteps +
          (6 * n) * 2 ^ w.twoSteps := by
            rw [Nat.add_mul]
  have hBudget' :
      3 * w.contractingGap * w.canonicalStart +
          (6 * n) * 2 ^ w.twoSteps <
        (w.oddSteps - 6 * n) * 2 ^ w.twoSteps +
          (6 * n) * 2 ^ w.twoSteps := by
    exact lt_of_lt_of_eq hBudget hMulDecomp
  have hLeft :
      3 * w.contractingGap * w.canonicalStart <
        (w.oddSteps - 6 * n) * 2 ^ w.twoSteps := by
    exact Nat.lt_of_add_lt_add_right hBudget'
  have hRight :
      (w.oddSteps - 6 * n) * 2 ^ w.twoSteps ≤
        (w.oddSteps - 6 * n) *
          ((K * (w.oddSteps + 1) ^ A + 1) *
            w.contractingGap) :=
    Nat.mul_le_mul_left (w.oddSteps - 6 * n) hPowBound
  have hGapPos : 0 < w.contractingGap :=
    O.firstCrossing.terminalContracting.contractingGap_pos
  have hScaled :
      w.contractingGap * (3 * w.canonicalStart) <
        w.contractingGap *
          ((w.oddSteps - 6 * n) *
            (K * (w.oddSteps + 1) ^ A + 1)) := by
    calc
      w.contractingGap * (3 * w.canonicalStart)
          = 3 * w.contractingGap * w.canonicalStart := by ring
      _ < (w.oddSteps - 6 * n) * 2 ^ w.twoSteps := hLeft
      _ ≤ (w.oddSteps - 6 * n) *
            ((K * (w.oddSteps + 1) ^ A + 1) *
              w.contractingGap) := hRight
      _ = w.contractingGap *
            ((w.oddSteps - 6 * n) *
              (K * (w.oddSteps + 1) ^ A + 1)) := by ring
  have hCanonicalBound :
      3 * w.canonicalStart <
        (w.oddSteps - 6 * n) *
          (K * (w.oddSteps + 1) ^ A + 1) :=
    (Nat.mul_lt_mul_left hGapPos).1 hScaled
  exact
    ⟨K, A, n, hKpos, hnPos, hreturn, hexact, hSix,
      hCanonicalBound⟩

/--
prepend-one quotient zero failure packet から polynomial canonical-start bound を直接得る。
-/
theorem PrependOneZeroFailureObstruction.polynomialCanonicalStartBound
    {v : Collatz.Word} {boundary : ℕ}
    (O : PrependOneZeroFailureObstruction v boundary)
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ K A n : ℕ,
      0 < K ∧
      0 < n ∧
      canonicalEnd (1 :: v) =
        canonicalStart (1 :: v) + 2 * n ∧
      affineConst (1 :: v) =
        contractingGap (1 :: v) * canonicalStart (1 :: v) +
          2 ^ (twoSteps (1 :: v) + 1) * n ∧
      6 * n < oddSteps (1 :: v) ∧
      3 * canonicalStart (1 :: v) <
        (oddSteps (1 :: v) - 6 * n) *
          (K * (oddSteps (1 :: v) + 1) ^ A + 1) :=
  O.paradoxical.polynomialCanonicalStartBound hGap

end Word
end Collatz
