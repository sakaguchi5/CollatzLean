import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2CenteredDivisibility
import CollatzLean.Collatz.External.TwoThreeGap
import CollatzLean.Collatz.Word.ExponentSlope

/-!
# E2 ZERO centered trajectory の band reduction

divisibility kernel で得た

  `0 < c < 3*G`

の三帯域をさらに削る。

* effective 2-3 gap と slope を組み合わせると

    `3*m < 2*G`

  が全長で成立する。従って第3帯域 `2*G <= c` は不可能。

* 残る middle band `G <= c < 2*G` は

    `G < 3*m`

  という linearly-small 2-3 gap を強制する。

* Baker 型 polynomial gap を併用すると、この middle band は
  ある有限 cutoff 未満にしか存在できない。

また、whole crossing gap `G` と inner gap `g = 2^K-3^m`、
backward affine constant `B` の exact relation

  `B = c*g + 2*G*h_m`

を証明し、

  `gcd(G,B) = gcd(G,c)`

まで純整数論へ圧縮する。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero
namespace E2ZeroCenteredTrajectoryData

/-- inner word 自身の contracting gap `2^K - 3^m`。 -/
def centeredInnerGap
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  2 ^ D.totalExponent - 3 ^ D.length

/-- inner gap の subtraction-free equation。 -/
theorem centeredInnerGap_add_threePow
    (D : E2ZeroCenteredTrajectoryData) :
    D.centeredInnerGap + 3 ^ D.length =
      2 ^ D.totalExponent := by
  have hm : 0 < D.length := by
    have h7 := D.seven_le_length
    omega
  have hC :=
    D.suffix_contracting D.length hm le_rfl
  dsimp [centeredInnerGap]
  exact Nat.sub_add_cancel (Nat.le_of_lt hC)

/-- inner gap は正。 -/
theorem centeredInnerGap_pos
    (D : E2ZeroCenteredTrajectoryData) :
    0 < D.centeredInnerGap := by
  have hm : 0 < D.length := by
    have h7 := D.seven_le_length
    omega
  have hC :=
    D.suffix_contracting D.length hm le_rfl
  dsimp [centeredInnerGap]
  exact Nat.sub_pos_of_lt hC

/--
whole crossing gap と inner gap の exact relation

  `G + 3^m = 8*g`。
-/
theorem crossingGap_add_threePow_eq_eight_mul_centeredInnerGap
    (D : E2ZeroCenteredTrajectoryData) :
    D.crossingGap + 3 ^ D.length =
      8 * D.centeredInnerGap := by
  have hG := D.crossingGap_add_nine_threePow
  have hg := D.centeredInnerGap_add_threePow
  nlinarith

/-- 同値な relation `2^K + G = 9*g`。 -/
theorem twoPow_add_crossingGap_eq_nine_mul_centeredInnerGap
    (D : E2ZeroCenteredTrajectoryData) :
    2 ^ D.totalExponent + D.crossingGap =
      9 * D.centeredInnerGap := by
  have hG := D.crossingGap_add_nine_threePow
  have hg := D.centeredInnerGap_add_threePow
  nlinarith

/-- endpoint を defect と full half-gap だけで書く。 -/
theorem endpoint_eq_defect_add_sixteen_mul_fullHalfGap
    (D : E2ZeroCenteredTrajectoryData) :
    D.endpoint =
      D.endpointDefect + 16 * D.halfGap D.length := by
  have hbal := D.endpoint_balance
  have hdef := D.endpointDefect_add_five
  omega

/--
ZERO crossing balance を inner gap で解いた exact identity。

  `B = c*g + 2*G*h_m`。
-/
theorem backwardAffine_eq_defect_mul_innerGap_add_two_mul_crossingGap_mul_halfGap
    (D : E2ZeroCenteredTrajectoryData) :
    D.backwardAffine D.length =
      D.endpointDefect * D.centeredInnerGap +
        2 * D.crossingGap * D.halfGap D.length := by
  have hBal := D.crossingBalance
  have hT := D.endpoint_eq_defect_add_sixteen_mul_fullHalfGap
  have hCG :=
    D.crossingGap_add_threePow_eq_eight_mul_centeredInnerGap
  have hCGc :=
    congrArg
      (fun z : ℕ => D.endpointDefect * z)
      hCG
  rw [hT] at hBal
  ring_nf at hBal hCGc ⊢
  nlinarith

/-- `G` と inner gap `g` は互いに素。 -/
theorem crossingGap_coprime_centeredInnerGap
    (D : E2ZeroCenteredTrajectoryData) :
    Nat.Coprime D.crossingGap D.centeredInnerGap := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let k := Nat.gcd D.crossingGap D.centeredInnerGap
  have hkG : k ∣ D.crossingGap :=
    Nat.gcd_dvd_left _ _
  have hkg : k ∣ D.centeredInnerGap :=
    Nat.gcd_dvd_right _ _
  have hCG :=
    D.crossingGap_add_threePow_eq_eight_mul_centeredInnerGap
  have hkSum :
      k ∣ D.crossingGap + 3 ^ D.length := by
    rw [hCG]
    exact Nat.dvd_mul_left_of_dvd hkg 8
  have hkC : k ∣ 3 ^ D.length :=
    (Nat.dvd_add_iff_right hkG).mpr hkSum
  have hgA := D.centeredInnerGap_add_threePow
  have hkA : k ∣ 2 ^ D.totalExponent := by
    rw [← hgA]
    exact Nat.dvd_add hkg hkC
  have hAC :
      Nat.Coprime
        (2 ^ D.totalExponent)
        (3 ^ D.length) :=
    (by decide : Nat.Coprime 2 3).pow
      D.totalExponent D.length
  exact Nat.eq_one_of_dvd_coprimes hAC hkA hkC

/-- exact identity から `gcd(G,B)=gcd(G,c)`。 -/
theorem gcd_crossingGap_backwardAffine_eq_gcd_crossingGap_endpointDefect
    (D : E2ZeroCenteredTrajectoryData) :
    Nat.gcd D.crossingGap (D.backwardAffine D.length) =
      Nat.gcd D.crossingGap D.endpointDefect := by
  have hEq :=
    D.backwardAffine_eq_defect_mul_innerGap_add_two_mul_crossingGap_mul_halfGap
  have hCop := D.crossingGap_coprime_centeredInnerGap
  calc
    Nat.gcd D.crossingGap (D.backwardAffine D.length)
        =
      Nat.gcd D.crossingGap
        (D.endpointDefect * D.centeredInnerGap +
          2 * D.crossingGap * D.halfGap D.length) := by
            rw [hEq]
    _ =
      Nat.gcd D.crossingGap
        (D.endpointDefect * D.centeredInnerGap) := by
      have h :=
        Nat.gcd_add_mul_left_right
          D.crossingGap
          (D.endpointDefect * D.centeredInnerGap)
          (2 * D.halfGap D.length)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    _ = Nat.gcd D.crossingGap D.endpointDefect := by
      exact
        hCop.symm.gcd_mul_right_cancel_right D.endpointDefect

/-- 小指数箱で既に `3*m < 2*gap`。 -/
private theorem three_mul_length_lt_two_mul_gap_small_box :
    ∀ m : Fin 16,
    ∀ H : Fin 28,
      3 ^ (m.1 + 2) < 2 ^ H.1 →
        3 * m.1 <
          2 * (2 ^ H.1 - 3 ^ (m.1 + 2)) := by
  decide

/-- whole pair を通常の `3^p < 2^H` 形にする。 -/
theorem whole_threePow_lt_twoPow
    (D : E2ZeroCenteredTrajectoryData) :
    3 ^ (D.length + 2) <
      2 ^ (D.totalExponent + 3) := by
  calc
    3 ^ (D.length + 2)
        = 9 * 3 ^ D.length := by
            rw [pow_add]
            norm_num
            ring
    _ < 8 * 2 ^ D.totalExponent := by
          simpa [totalExponent] using D.whole_contracting
    _ = 2 ^ (D.totalExponent + 3) := by
          rw [pow_add]
          norm_num
          ring

/-- crossing gap を通常の power gap と同定する。 -/
theorem crossingGap_eq_twoPow_sub_threePow
    (D : E2ZeroCenteredTrajectoryData) :
    D.crossingGap =
      2 ^ (D.totalExponent + 3) -
        3 ^ (D.length + 2) := by
  dsimp [crossingGap]
  rw [pow_add, pow_add]
  norm_num
  ring_nf

/--
effective gap と slope を合わせると、実は全長で

  `3*m < 2*G`

まで強くなる。

`H<28` は有限箱、`H>=28` は Ellison `H<=G` と
`19*(m+2)<12*H` を使う。
-/
theorem three_mul_length_lt_two_mul_crossingGap
    (D : E2ZeroCenteredTrajectoryData)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    3 * D.length < 2 * D.crossingGap := by
  let H := D.totalExponent + 3
  have hContract : 3 ^ (D.length + 2) < 2 ^ H := by
    simpa [H] using D.whole_threePow_lt_twoPow
  by_cases hH : H < 28
  · have hp18 :
        D.length + 2 < 18 :=
      External.exponent_lt_eighteen_of_twoExponent_lt_28
        hH hContract
    have hm16 : D.length < 16 := by
      omega
    let mf : Fin 16 := ⟨D.length, hm16⟩
    let Hf : Fin 28 := ⟨H, hH⟩
    have hbox :=
      three_mul_length_lt_two_mul_gap_small_box mf Hf
        (by simpa [mf, Hf] using hContract)
    have hG := D.crossingGap_eq_twoPow_sub_threePow
    simpa [mf, Hf, H] using (by
      rw [hG]
      exact hbox)
  · have hH28 : 28 ≤ H := by omega
    have hEllison :
        H ≤ 2 ^ H - 3 ^ (D.length + 2) :=
      hEffective.ellison
        (D.length + 2) H hH28 hContract
    have hSlope :=
      Word.nineteen_mul_lt_twelve_mul_of_threePow_lt_twoPow
        (m := D.length + 2)
        (J := H)
        (by omega)
        hContract
    have hG := D.crossingGap_eq_twoPow_sub_threePow
    have hHG : H ≤ D.crossingGap := by
      rw [hG]
      exact hEllison
    omega

/-- 第3帯域 `2*G <= c` は完全に不可能。 -/
theorem endpointDefect_lt_two_mul_crossingGap
    (D : E2ZeroCenteredTrajectoryData)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    D.endpointDefect < 2 * D.crossingGap := by
  have hc := D.endpointDefect_lt_three_mul_length
  have hG :=
    D.three_mul_length_lt_two_mul_crossingGap hEffective
  omega

/--
三帯域は二帯域へ縮む。

  `c < G`
  または
  `G <= c < 2*G`。
-/
theorem endpointDefect_twoBand
    (D : E2ZeroCenteredTrajectoryData)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    D.endpointDefect < D.crossingGap ∨
      (D.crossingGap ≤ D.endpointDefect ∧
        D.endpointDefect < 2 * D.crossingGap) := by
  have h2 :=
    D.endpointDefect_lt_two_mul_crossingGap hEffective
  by_cases h0 : D.endpointDefect < D.crossingGap
  · exact Or.inl h0
  · exact Or.inr ⟨by omega, h2⟩

/-- 残る middle band。 -/
def MiddleBand (D : E2ZeroCenteredTrajectoryData) : Prop :=
  D.crossingGap ≤ D.endpointDefect

/-- middle band は linearly-small gap `G < 3*m` を強制する。 -/
theorem middleBand_forces_crossingGap_lt_three_mul_length
    (D : E2ZeroCenteredTrajectoryData)
    (hMiddle : D.MiddleBand) :
    D.crossingGap < 3 * D.length := by
  have hc := D.endpointDefect_lt_three_mul_length
  exact lt_of_le_of_lt hMiddle hc

/-- middle band は通常の exponent `p=m+2` に対して `G < 3*p`。 -/
theorem middleBand_forces_crossingGap_lt_three_mul_fullLength
    (D : E2ZeroCenteredTrajectoryData)
    (hMiddle : D.MiddleBand) :
    D.crossingGap < 3 * (D.length + 2) := by
  have h := D.middleBand_forces_crossingGap_lt_three_mul_length hMiddle
  omega

/--
Baker 型 polynomial gap があれば、middle band はある有限 length cutoff 未満にしか存在しない。
-/
theorem exists_middleBand_fullLength_cutoff
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ D : E2ZeroCenteredTrajectoryData,
        D.MiddleBand →
          D.length + 2 < N := by
  rcases hPoly with ⟨K, A, hKPos, hBaker⟩
  obtain ⟨N, hGrowth⟩ :=
    Arithmetic.polynomialBelowTwoMulThreePower
      (6 * K) (A + 1)
  refine ⟨N, ?_⟩
  intro D hMiddle
  let p := D.length + 2
  let H := D.totalExponent + 3
  have hpPos : 0 < p := by
    dsimp [p]
    omega
  have hContract : 3 ^ p < 2 ^ H := by
    simpa [p, H] using D.whole_threePow_lt_twoPow
  have hGapForm :
      D.crossingGap = 2 ^ H - 3 ^ p := by
    simpa [p, H] using D.crossingGap_eq_twoPow_sub_threePow
  have hGapSmall : D.crossingGap < 3 * p := by
    simpa [p] using
      D.middleBand_forces_crossingGap_lt_three_mul_fullLength hMiddle
  have hBaker' :
      3 ^ p ≤
        K * (p + 1) ^ A * D.crossingGap := by
    have h :=
      hBaker p H hpPos hContract
    rw [← hGapForm] at h
    exact h
  by_contra hnot
  have hN : N ≤ p := by
    omega
  have hGrowth' :=
    hGrowth p hN
  have hQPos :
      0 < K * (p + 1) ^ A := by
    exact Nat.mul_pos hKPos (Nat.pow_pos (by omega))
  have hBakerUpper :
      K * (p + 1) ^ A * D.crossingGap <
        K * (p + 1) ^ A * (3 * p) :=
    (Nat.mul_lt_mul_left hQPos).2 hGapSmall
  have hpLe : p ≤ p + 1 := by omega
  have hPolyUpper :
      K * (p + 1) ^ A * (3 * p) ≤
        3 * K * (p + 1) ^ (A + 1) := by
    have h :=
      Nat.mul_le_mul_left
        (3 * K * (p + 1) ^ A) hpLe
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using h
  have hExpLtPoly :
      3 ^ p < 3 * K * (p + 1) ^ (A + 1) :=
    lt_of_le_of_lt hBaker'
      (lt_of_lt_of_le hBakerUpper hPolyUpper)
  have hGrowthScaled :
      2 * (3 * K * (p + 1) ^ (A + 1)) <
        2 * 3 ^ p := by
    convert hGrowth' using 1
    ring
  have hPolyLtExp :
      3 * K * (p + 1) ^ (A + 1) < 3 ^ p := by
    omega
  omega

/--
effective gap + Baker gap のもとで三帯域は

* infinite side: `c < G`
* finite near-resonance side: `G <= c < 2G` かつ `m+2 < N`

の二つだけになる。
-/
theorem exists_endpointDefect_reducedBandCutoff
    (hEffective : External.TwoThreeEffectiveGapInput)
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ D : E2ZeroCenteredTrajectoryData,
        D.endpointDefect < D.crossingGap ∨
          (D.crossingGap ≤ D.endpointDefect ∧
            D.endpointDefect < 2 * D.crossingGap ∧
            D.length + 2 < N) := by
  obtain ⟨N, hN⟩ :=
    exists_middleBand_fullLength_cutoff hPoly
  refine ⟨N, ?_⟩
  intro D
  rcases D.endpointDefect_twoBand hEffective with hSmall | hMiddle
  · exact Or.inl hSmall
  · exact Or.inr
      ⟨hMiddle.1, hMiddle.2, hN D hMiddle.1⟩

end E2ZeroCenteredTrajectoryData
end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
