import CollatzLean.CollatzSupport.Arithmetic
import CollatzLean.CollatzOrbitCore.Crossing


/-!
# Baker型gapによるfirst-crossingの多項式評価
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
future-minimumから始まるfirst-crossingでは、
乗法gapと開始値の積は`p * 3^p`以下。
-/
theorem firstCrossing_gap_mul_start_le
    {O : OddOrbit} {n p : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    (2 ^ twoSteps (O.segmentWord n p) - 3 ^ p) * O.value n ≤
      p * 3 ^ p := by
  let w := O.segmentWord n p
  have hrun : Realizes w (O.value n) (O.value (n + p)) :=
    O.realizes_segment n p
  have hend : O.value n ≤ O.value (n + p) :=
    O.futureMinimum_le_segment_end hmin p
  have hscaled :
      2 ^ twoSteps w * O.value n ≤
        3 ^ oddSteps w * O.value n + affineConst w := by
    calc
      2 ^ twoSteps w * O.value n
          ≤ 2 ^ twoSteps w * O.value (n + p) :=
        Nat.mul_le_mul_left _ hend
      _ = 3 ^ oddSteps w * O.value n + affineConst w := hrun
  have hcontract : 3 ^ oddSteps w < 2 ^ twoSteps w :=
    hC.terminalContracting
  have hdecomp :
      2 ^ twoSteps w =
        3 ^ oddSteps w +
          (2 ^ twoSteps w - 3 ^ oddSteps w) :=
    (Nat.add_sub_of_le hcontract.le).symm
  have hgap :
      (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n ≤
        affineConst w := by
    have hcancel :
        3 ^ oddSteps w * O.value n +
            (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n ≤
          3 ^ oddSteps w * O.value n + affineConst w := by
      calc
        3 ^ oddSteps w * O.value n +
            (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
            = 2 ^ twoSteps w * O.value n := by
                calc
                  3 ^ oddSteps w * O.value n +
                      (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
                      =
                    (3 ^ oddSteps w +
                        (2 ^ twoSteps w - 3 ^ oddSteps w)) *
                      O.value n := by
                        rw [Nat.add_mul]
                  _ = 2 ^ twoSteps w * O.value n := by
                        rw [← hdecomp]
        _ ≤ 3 ^ oddSteps w * O.value n + affineConst w := hscaled
    exact Nat.le_of_add_le_add_left hcancel
  calc
    (2 ^ twoSteps (O.segmentWord n p) - 3 ^ p) * O.value n
        = (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n := by
          simp [w, oddSteps]
    _ ≤ affineConst w := hgap
    _ ≤ w.length * 3 ^ w.length :=
      affineConst_le_length_mul_threePow hC
    _ = p * 3 ^ p := by simp [w]

/-- Baker型gap入力からfirst-crossing開始値を多項式で抑える。 -/
theorem futureMinimum_firstCrossing_start_polynomial
    (hGap : TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ n p : ℕ,
        O.FutureMinimumAt n →
        FirstCrossingAt O n p →
        O.value n ≤ K * (p + 1) ^ A := by
  rcases hGap with ⟨K, A, hK, hgap⟩
  refine ⟨K, A + 1, ?_⟩
  intro O n p hmin hC
  have hp : 0 < p := hC.length_pos
  let H := twoSteps (O.segmentWord n p)
  let g := 2 ^ H - 3 ^ p
  have hC' : FirstCrossing (O.segmentWord n p) := by
    exact hC
  have hcontractRaw :
      3 ^ oddSteps (O.segmentWord n p) <
        2 ^ twoSteps (O.segmentWord n p) :=
    hC'.terminalContracting
  have hcontract : 3 ^ p < 2 ^ H := by
    simpa [H, oddSteps] using hcontractRaw
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.sub_pos_of_lt hcontract
  have hGX : g * O.value n ≤ p * 3 ^ p := by
    simpa [g, H] using firstCrossing_gap_mul_start_le hmin hC
  exact start_le_polynomial_of_gap_bound hg hGX
    (hgap p H hp hcontract)

/-- first-crossing終点は開始値と語長の和以下。 -/
theorem firstCrossing_endpoint_le_start_add_length
    {O : OddOrbit} {n p : ℕ}
    (hC : FirstCrossingAt O n p) :
    O.value (n + p) ≤ O.value n + p := by
  let w := O.segmentWord n p
  have hrun : Realizes w (O.value n) (O.value (n + p)) :=
    O.realizes_segment n p
  have hcontract : 3 ^ oddSteps w < 2 ^ twoSteps w :=
    hC.terminalContracting
  have hB : affineConst w ≤ p * 3 ^ p := by
    simpa [w] using affineConst_le_length_mul_threePow hC
  have hB' : affineConst w ≤ p * 2 ^ twoSteps w := by
    exact hB.trans
      (Nat.mul_le_mul_left p (by
        simpa [w, oddSteps] using hcontract.le))
  have hmain :
      2 ^ twoSteps w * O.value (n + p) ≤
        2 ^ twoSteps w * (O.value n + p) := by
    calc
      2 ^ twoSteps w * O.value (n + p)
          = 3 ^ oddSteps w * O.value n + affineConst w := hrun
      _ ≤ 2 ^ twoSteps w * O.value n +
            p * 2 ^ twoSteps w :=
        Nat.add_le_add
          (Nat.mul_le_mul_right (O.value n) hcontract.le)
          hB'
      _ = 2 ^ twoSteps w * (O.value n + p) := by ring
  exact Nat.le_of_mul_le_mul_left hmain
    (Nat.pow_pos (by omega : 0 < (2 : ℕ)))

/-- Baker型gap入力からfirst-crossing終点も多項式で抑える。 -/
theorem futureMinimum_firstCrossing_endpoint_polynomial
    (hGap : TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ n p : ℕ,
        O.FutureMinimumAt n →
        FirstCrossingAt O n p →
        O.value (n + p) ≤ K * (p + 1) ^ A := by
  obtain ⟨K, A, hstart⟩ :=
    futureMinimum_firstCrossing_start_polynomial hGap
  refine ⟨K + 1, A + 1, ?_⟩
  intro O n p hmin hC
  have hs := hstart O n p hmin hC
  have he := firstCrossing_endpoint_le_start_add_length hC
  have hpowA : (p + 1) ^ A ≤ (p + 1) ^ (A + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hp : p ≤ (p + 1) ^ (A + 1) := by
    have hbase : p ≤ p + 1 := by omega
    exact hbase.trans
      (show p + 1 ≤ (p + 1) ^ (A + 1) by
        have h := Nat.pow_le_pow_right
          (by omega : 0 < p + 1)
          (by omega : 1 ≤ A + 1)
        simpa using h)
  calc
    O.value (n + p) ≤ O.value n + p := he
    _ ≤ K * (p + 1) ^ A + p := Nat.add_le_add hs le_rfl
    _ ≤ K * (p + 1) ^ (A + 1) +
          (p + 1) ^ (A + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left K hpowA) hp
    _ = (K + 1) * (p + 1) ^ (A + 1) := by ring

end CollatzSecondLayer2
