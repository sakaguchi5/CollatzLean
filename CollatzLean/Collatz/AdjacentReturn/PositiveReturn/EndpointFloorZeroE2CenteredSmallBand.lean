import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2CenteredBands

/-!
# E2 ZERO centered trajectory の small-band arithmetic

三帯域 reduction 後に残る本命

  `c < G`

を、return coordinate と centered full level で書き直す。

ここでは

  `L = h_m + n`
  `d = 2*n`

と置く。ZERO coordinate から

  `start + 5 = 18*L`
  `outerStart + 5 = 16*L`
  `endpoint = outerStart + d`

が pure arithmetic に再構成できる。

さらに backward affine exact identity

  `B = c*g + 2*G*h_m`

を

  `B + 5*g = 2*2^K*n + 2*G*L`

へ変形する。

all-suffix contracting を backward affine recurrence に直接入れると

  `3*B < m*2^K`

が有限語なしで再証明でき、そこから

  `6*G*L < (sigma+15)*2^K`

を得る。

最後に Baker 型 2-3 gap を whole pair へ適用して `2^K/G` を消去すると

  `48*L < (sigma+15)*(K0*(m+3)^A0+1)`

という pure polynomial bound になる。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero
namespace E2ZeroCenteredTrajectoryData

/-- `L = h_m + n`。 -/
def fullLevel
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  D.halfGap D.length + D.n

/-- outer `[1,2]` block の actual start。 -/
def outerStart
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  16 * D.fullLevel - 5

/-- outer first-crossing の return gap `2*n`。 -/
def centeredReturnGap
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  2 * D.n

/-- `m = 6*n + sigma`。 -/
theorem length_eq_six_mul_n_add_sigma
    (D : E2ZeroCenteredTrajectoryData) :
    D.length = 6 * D.n + D.sigma := by
  have h := D.six_mul_n_lt_length
  dsimp [sigma]
  omega

/-- full level は正。 -/
theorem fullLevel_pos
    (D : E2ZeroCenteredTrajectoryData) :
    0 < D.fullLevel := by
  have hh := D.full_halfGap_pos
  have hn := D.n_pos
  dsimp [fullLevel]
  omega

/--
最初の inner exponent `1` の integrality から
`L = h_m+n` は偶数。
-/
theorem fullLevel_even
    (D : E2ZeroCenteredTrajectoryData) :
    ∃ q : ℕ, D.fullLevel = q + q := by
  have hpen := D.penultimateHalfGap
  obtain ⟨q, hEven | hOdd⟩ := D.fullLevel.even_or_odd'
  · exact ⟨q, by simpa [two_mul] using hEven⟩
  · dsimp [fullLevel] at hOdd
    exfalso
    omega

/-- inner canonical start の coordinate `start+5=18*L`。 -/
theorem startValue_add_five_eq_eighteen_mul_fullLevel
    (D : E2ZeroCenteredTrajectoryData) :
    D.startValue + 5 = 18 * D.fullLevel := by
  simpa [fullLevel] using D.start_add_five_eq_eighteen_mul_fullLevel

/-- outer start は `outerStart+5=16*L`。 -/
theorem outerStart_add_five_eq_sixteen_mul_fullLevel
    (D : E2ZeroCenteredTrajectoryData) :
    D.outerStart + 5 = 16 * D.fullLevel := by
  have hL := D.fullLevel_pos
  dsimp [outerStart]
  omega

/-- endpoint coordinate `endpoint+5=16*L+2*n`。 -/
theorem endpoint_add_five_eq_sixteen_mul_fullLevel_add_two_mul_n
    (D : E2ZeroCenteredTrajectoryData) :
    D.endpoint + 5 =
      16 * D.fullLevel + 2 * D.n := by
  have h := D.endpoint_balance
  dsimp [fullLevel]
  omega

/-- outer actual return は exact に `2*n`。 -/
theorem endpoint_eq_outerStart_add_centeredReturnGap
    (D : E2ZeroCenteredTrajectoryData) :
    D.endpoint =
      D.outerStart + D.centeredReturnGap := by
  have hX := D.outerStart_add_five_eq_sixteen_mul_fullLevel
  have hT :=
    D.endpoint_add_five_eq_sixteen_mul_fullLevel_add_two_mul_n
  dsimp [centeredReturnGap]
  omega

/-- `[1,2]` head の exact affine relation `8*S = 9*X+5`。 -/
theorem eight_mul_startValue_eq_nine_mul_outerStart_add_five
    (D : E2ZeroCenteredTrajectoryData) :
    8 * D.startValue =
      9 * D.outerStart + 5 := by
  have hS := D.startValue_add_five_eq_eighteen_mul_fullLevel
  have hX := D.outerStart_add_five_eq_sixteen_mul_fullLevel
  omega

/-- outer return gap は正。 -/
theorem centeredReturnGap_pos
    (D : E2ZeroCenteredTrajectoryData) :
    0 < D.centeredReturnGap := by
  have hn := D.n_pos
  dsimp [centeredReturnGap]
  omega

/-- band reduction 後に残る small band `c<G`。 -/
def SmallBand
    (D : E2ZeroCenteredTrajectoryData) : Prop :=
  D.endpointDefect < D.crossingGap

/--
`c<G` は return gap で

  `9*(2*n) < G+5`

と同値。
-/
theorem smallBand_iff_nine_mul_returnGap_lt_crossingGap_add_five
    (D : E2ZeroCenteredTrajectoryData) :
    D.SmallBand ↔
      9 * D.centeredReturnGap < D.crossingGap + 5 := by
  have hdef := D.endpointDefect_add_five
  constructor
  · intro h
    dsimp [SmallBand, centeredReturnGap] at h ⊢
    omega
  · intro h
    dsimp [SmallBand, centeredReturnGap] at h ⊢
    omega

/-- inner gap は total two-power より真に小さい。 -/
theorem centeredInnerGap_lt_twoPow
    (D : E2ZeroCenteredTrajectoryData) :
    D.centeredInnerGap < 2 ^ D.totalExponent := by
  have hEq := D.centeredInnerGap_add_threePow
  have hC : 0 < 3 ^ D.length :=
    Nat.pow_pos (by omega)
  omega

/--
ZERO affine identity を full level で書き直す。

  `B + 5*g = 2*2^K*n + 2*G*L`。
-/
theorem backwardAffine_add_five_mul_innerGap_eq_levelBalance
    (D : E2ZeroCenteredTrajectoryData) :
    D.backwardAffine D.length +
        5 * D.centeredInnerGap =
      2 * 2 ^ D.totalExponent * D.n +
        2 * D.crossingGap * D.fullLevel := by
  have hB :=
    D.backwardAffine_eq_defect_mul_innerGap_add_two_mul_crossingGap_mul_halfGap
  have hdef := D.endpointDefect_add_five
  have hAg :=
    D.twoPow_add_crossingGap_eq_nine_mul_centeredInnerGap
  dsimp [fullLevel]
  ring_nf at hB hdef hAg ⊢
  nlinarith

/--
backward affine recurrence と全 suffix contracting だけから得る sharp bound。

  `3*B_r < r*2^K_r`。
-/
theorem three_mul_backwardAffine_lt
    (D : E2ZeroCenteredTrajectoryData)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ D.length) :
    3 * D.backwardAffine r <
      r * 2 ^ D.suffixExponent r := by
  induction r with
  | zero =>
      omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        have hC :=
          D.suffix_contracting 1 (by omega) (by omega)
        simpa using hC
      · have hrPos' : 0 < r := Nat.pos_of_ne_zero hr0
        have hrLt : r < D.length := by
          omega
        have hrLe' : r ≤ D.length := by
          omega
        have hih := ih hrPos' hrLe'
        have hK := D.suffixExponent_succ r hrLt
        have hC :=
          D.suffix_contracting (r + 1) (by omega) (by omega)
        have hC' :
            3 ^ (r + 1) <
              2 ^ (D.backwardExponent r + D.suffixExponent r) := by
          rw [← hK]
          exact hC
        have hpowPos : 0 < 2 ^ D.backwardExponent r :=
          Nat.pow_pos (by omega)
        have hscaled :
            2 ^ D.backwardExponent r *
                (3 * D.backwardAffine r) <
              2 ^ D.backwardExponent r *
                (r * 2 ^ D.suffixExponent r) :=
          (Nat.mul_lt_mul_left hpowPos).2 hih
        rw [D.backwardAffine_succ, hK]
        calc
          3 *
              (3 ^ r +
                2 ^ D.backwardExponent r * D.backwardAffine r)
              =
            3 ^ (r + 1) +
              2 ^ D.backwardExponent r *
                (3 * D.backwardAffine r) := by
                  rw [pow_succ]
                  ring
          _ <
            2 ^ (D.backwardExponent r + D.suffixExponent r) +
              2 ^ D.backwardExponent r *
                (r * 2 ^ D.suffixExponent r) :=
            Nat.add_lt_add hC' hscaled
          _ =
            (r + 1) *
              (2 ^ D.backwardExponent r *
                2 ^ D.suffixExponent r) := by
                  ring
          _ =
            (r + 1) *
              2 ^ (D.backwardExponent r + D.suffixExponent r) := by
                  rw [pow_add]

/-- full backward affine の pure sharp bound。 -/
theorem three_mul_fullBackwardAffine_lt
    (D : E2ZeroCenteredTrajectoryData) :
    3 * D.backwardAffine D.length <
      D.length * 2 ^ D.totalExponent := by
  have hm : 0 < D.length := by
    have h7 := D.seven_le_length
    omega
  simpa [totalExponent] using
    D.three_mul_backwardAffine_lt hm le_rfl

/--
full-level balance と sharp affine bound から

  `6*G*L < (sigma+15)*2^K`

を得る。
-/
theorem six_mul_crossingGap_mul_fullLevel_lt_sigmaBudget
    (D : E2ZeroCenteredTrajectoryData) :
    6 * D.crossingGap * D.fullLevel <
      (D.sigma + 15) * 2 ^ D.totalExponent := by
  have hEq :=
    D.backwardAffine_add_five_mul_innerGap_eq_levelBalance
  have hB := D.three_mul_fullBackwardAffine_lt
  have hg := D.centeredInnerGap_lt_twoPow
  have h15 :
      15 * D.centeredInnerGap <
        15 * 2 ^ D.totalExponent :=
    (Nat.mul_lt_mul_left (by omega : 0 < 15)).2 hg
  have hLen := D.length_eq_six_mul_n_add_sigma
  ring_nf at hEq hB h15 hLen ⊢
  nlinarith

/--
effective gap の `3*m < 2*G` を合わせると

  `9*m*L < (sigma+15)*2^K`。
-/
theorem nine_mul_length_mul_fullLevel_lt_sigmaBudget
    (D : E2ZeroCenteredTrajectoryData)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    9 * D.length * D.fullLevel <
      (D.sigma + 15) * 2 ^ D.totalExponent := by
  have hG :=
    D.three_mul_length_lt_two_mul_crossingGap hEffective
  have hL := D.fullLevel_pos
  have hscaled :
      (3 * D.length) * D.fullLevel <
        (2 * D.crossingGap) * D.fullLevel :=
    (Nat.mul_lt_mul_right hL).2 hG
  have hscaled3 :
      3 * ((3 * D.length) * D.fullLevel) <
        3 * ((2 * D.crossingGap) * D.fullLevel) :=
    (Nat.mul_lt_mul_left (by omega : 0 < 3)).2 hscaled
  have hBudget :=
    D.six_mul_crossingGap_mul_fullLevel_lt_sigmaBudget
  ring_nf at hscaled3 hBudget ⊢
  exact lt_trans hscaled3 hBudget

/--
Baker 型 whole gap を使って `2^K/G` を消去した full-level polynomial bound。

`48*L < (sigma+15)*(K0*(m+3)^A0+1)`。
-/
theorem exists_fullLevel_slack_polynomial_bound
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      0 < K ∧
      ∀ D : E2ZeroCenteredTrajectoryData,
        48 * D.fullLevel <
          (D.sigma + 15) *
            (K * (D.length + 3) ^ A + 1) := by
  rcases hPoly with ⟨K, A, hKPos, hBaker⟩
  refine ⟨K, A, hKPos, ?_⟩
  intro D
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
  have hBaker' :
      3 ^ p ≤
        K * (p + 1) ^ A * D.crossingGap := by
    have h := hBaker p H hpPos hContract
    rw [← hGapForm] at h
    exact h
  have hPowForm :
      8 * 2 ^ D.totalExponent =
        D.crossingGap + 3 ^ p := by
    have h := D.crossingGap_add_nine_threePow
    simpa [
      p,
      pow_add,
      Nat.mul_assoc,
      Nat.mul_comm,
      Nat.mul_left_comm
    ] using h.symm
  have hAupper :
      8 * 2 ^ D.totalExponent ≤
        (K * (D.length + 3) ^ A + 1) *
          D.crossingGap := by
    have hp1 : p + 1 = D.length + 3 := by
      dsimp [p]
    rw [hp1] at hBaker'
    calc
      8 * 2 ^ D.totalExponent
          =
        D.crossingGap + 3 ^ p := hPowForm
      _ ≤
        D.crossingGap +
          K * (D.length + 3) ^ A * D.crossingGap :=
        Nat.add_le_add_left hBaker' D.crossingGap
      _ =
        (K * (D.length + 3) ^ A + 1) *
          D.crossingGap := by
        ring
  have hLevel :=
    D.six_mul_crossingGap_mul_fullLevel_lt_sigmaBudget
  have h8 :
      8 * (6 * D.crossingGap * D.fullLevel) <
        8 * ((D.sigma + 15) * 2 ^ D.totalExponent) :=
    (Nat.mul_lt_mul_left (by omega : 0 < 8)).2 hLevel
  have hUpper :
      8 * ((D.sigma + 15) * 2 ^ D.totalExponent) ≤
        (D.sigma + 15) *
          ((K * (D.length + 3) ^ A + 1) *
            D.crossingGap) := by
    have h :=
      Nat.mul_le_mul_left (D.sigma + 15) hAupper
    simpa [
      Nat.mul_assoc,
      Nat.mul_comm,
      Nat.mul_left_comm
    ] using h
  have hCombined :
      D.crossingGap * (48 * D.fullLevel) <
        D.crossingGap *
          ((D.sigma + 15) *
            (K * (D.length + 3) ^ A + 1)) := by
    have h := lt_of_lt_of_le h8 hUpper
    calc
      D.crossingGap * (48 * D.fullLevel)
        =
        8 * (6 * D.crossingGap * D.fullLevel) := by
          ring
      _ <
        (D.sigma + 15) *
          ((K * (D.length + 3) ^ A + 1) *
           D.crossingGap) := h
      _ =
        D.crossingGap *
          ((D.sigma + 15) *
            (K * (D.length + 3) ^ A + 1)) := by
          ring
  exact
    (Nat.mul_lt_mul_left D.crossingGap_pos).1 hCombined

/--
second forward exponent の二枝は full level の residue を

- `e₂=1` なら `L = 4*q+2`
- `e₂=2` なら `L = 8*q`

へ固定する。
-/
theorem fullLevel_residue_of_secondStep :
    ∀ D : E2ZeroCenteredTrajectoryData,
      (∃ q : ℕ, D.fullLevel = 4 * q + 2) ∨
      (∃ q : ℕ, D.fullLevel = 8 * q) := by
  intro D
  rcases D.secondBackwardExponent_one_or_two with h1 | h2
  · left
    have h := D.secondStep_one_relation h1
    have hmodEq :=
      congrArg (fun x : ℕ => x % 4) h
    have hmod :
        (D.halfGap D.length + D.n) % 4 = 2 := by
      norm_num [Nat.add_mod, Nat.mul_mod] at hmodEq ⊢
      exact hmodEq.symm
    have hfullMod :
        D.fullLevel % 4 = 2 := by
      simpa [fullLevel] using hmod
    refine ⟨D.fullLevel / 4, ?_⟩
    have hdiv :=
      Nat.mod_add_div D.fullLevel 4
    rw [hfullMod] at hdiv
    omega
  · right
    have h := D.secondStep_two_relation h2
    have hmodEq :=
      congrArg (fun x : ℕ => x % 8) h
    have hmod :
        (D.halfGap D.length + D.n) % 8 = 0 := by
      norm_num [Nat.add_mod, Nat.mul_mod] at hmodEq ⊢
      exact hmodEq.symm
    have hfullMod :
        D.fullLevel % 8 = 0 := by
      simpa [fullLevel] using hmod
    refine ⟨D.fullLevel / 8, ?_⟩
    have hdiv :=
      Nat.mod_add_div D.fullLevel 8
    rw [hfullMod] at hdiv
    omega

end E2ZeroCenteredTrajectoryData
end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
