import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2CenteredTrajectory
import CollatzLean.Collatz.External.TwoThreeEffectiveGap

/-!
# E2 ZERO centered trajectory の divisibility kernel

`E2ZeroCenteredTrajectoryData` の backward recurrence を全長まで畳み、
有限語を参照せずに affine constant を再構成する。

末尾 `r` 段の affine constant を `backwardAffine r` とすると

  `3^r * (T + 2*h_r) + backwardAffine r = 2^K_r * T`

が pure arithmetic に成立する。

全長で

  `G = 8*2^K - 9*3^m`
  `c = 18*n - 5`

と置くと、ZERO endpoint balance から

  `G*T + c*3^m = 8*B`

を得る。従って `G` は右辺の residual を割る。
さらに effective 2-3 gap を入れると

  `m+2 <= G`, `0 < c < 3*G`

となり、defect は `G` に対して三つの帯域だけへ縮む。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero
namespace E2ZeroCenteredTrajectoryData

/-- backward exponent 列だけから再構成する末尾 affine constant。 -/
def backwardAffine
    (D : E2ZeroCenteredTrajectoryData) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      3 ^ r +
        2 ^ D.backwardExponent r * backwardAffine D r

@[simp] theorem backwardAffine_zero
    (D : E2ZeroCenteredTrajectoryData) :
    D.backwardAffine 0 = 0 := rfl

@[simp] theorem backwardAffine_succ
    (D : E2ZeroCenteredTrajectoryData)
    (r : ℕ) :
    D.backwardAffine (r + 1) =
      3 ^ r +
        2 ^ D.backwardExponent r * D.backwardAffine r := rfl

/-- suffix start を endpoint-centered value に戻す。 -/
def centeredValue
    (D : E2ZeroCenteredTrajectoryData)
    (r : ℕ) : ℕ :=
  D.endpoint + 2 * D.halfGap r

/-- full inner start。 -/
def startValue
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  D.centeredValue D.length

/-- full inner cumulative exponent。 -/
def totalExponent
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  D.suffixExponent D.length

/-- whole `[1,2]` crossing gap `8*2^K - 9*3^m`。 -/
def crossingGap
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  8 * 2 ^ D.totalExponent - 9 * 3 ^ D.length

/-- ZERO endpoint defect `18*n-5`。 -/
def endpointDefect
    (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  18 * D.n - 5

/-- endpoint defect の subtraction-free form。 -/
theorem endpointDefect_add_five
    (D : E2ZeroCenteredTrajectoryData) :
    D.endpointDefect + 5 = 18 * D.n := by
  have hn := D.n_pos
  dsimp [endpointDefect]
  omega

/-- endpoint defect は正。 -/
theorem endpointDefect_pos
    (D : E2ZeroCenteredTrajectoryData) :
    0 < D.endpointDefect := by
  have hn := D.n_pos
  have h := D.endpointDefect_add_five
  omega

/-- full start と endpoint の ZERO defect identity。 -/
theorem eight_mul_start_add_defect_eq_nine_mul_endpoint
    (D : E2ZeroCenteredTrajectoryData) :
    8 * D.startValue + D.endpointDefect =
      9 * D.endpoint := by
  have hbal := D.endpoint_balance
  have hdef := D.endpointDefect_add_five
  dsimp [startValue, centeredValue] at *
  omega

/-- `start+5 = 18*(h_m+n)`。 -/
theorem start_add_five_eq_eighteen_mul_fullLevel
    (D : E2ZeroCenteredTrajectoryData) :
    D.startValue + 5 =
      18 * (D.halfGap D.length + D.n) := by
  have hbal := D.endpoint_balance
  dsimp [startValue, centeredValue]
  omega

/--
backward recurrence を `r` 段畳んだ exact affine equation。
-/
theorem backwardAffine_realization
    (D : E2ZeroCenteredTrajectoryData)
    {r : ℕ}
    (hr : r ≤ D.length) :
    3 ^ r * D.centeredValue r + D.backwardAffine r =
      2 ^ D.suffixExponent r * D.endpoint := by
  revert hr
  induction r with
  | zero =>
      intro _hr
      simp [centeredValue, D.halfGap_zero, D.suffixExponent_zero]
  | succ r ih =>
      intro hr
      have hrLt : r < D.length := by
        omega
      have hrLe : r ≤ D.length := by
        omega
      have hi := ih hrLe
      have hrec := D.step_recurrence r hrLt
      rw [pow_succ] at hrec
      have hK := D.suffixExponent_succ r hrLt
      have hstep :
          3 * D.centeredValue (r + 1) + 1 =
            2 ^ D.backwardExponent r * D.centeredValue r := by
        dsimp [centeredValue]
        nlinarith [hrec]
      rw [D.backwardAffine_succ, hK, pow_add]
      rw [pow_succ]
      calc
        (3 ^ r * 3) * D.centeredValue (r + 1) +
            (3 ^ r +
              2 ^ D.backwardExponent r * D.backwardAffine r)
            =
            3 ^ r *
                (3 * D.centeredValue (r + 1) + 1) +
              2 ^ D.backwardExponent r * D.backwardAffine r := by
          ring
        _ =
            3 ^ r *
                (2 ^ D.backwardExponent r *
                  D.centeredValue r) +
              2 ^ D.backwardExponent r * D.backwardAffine r := by
          rw [hstep]
        _ =
            2 ^ D.backwardExponent r *
              (3 ^ r * D.centeredValue r +
                D.backwardAffine r) := by
          ring
        _ =
            2 ^ D.backwardExponent r *
              (2 ^ D.suffixExponent r * D.endpoint) := by
          rw [hi]
        _ =
            (2 ^ D.backwardExponent r *
              2 ^ D.suffixExponent r) * D.endpoint := by
          ring
        _ =
            2 ^ (D.backwardExponent r + D.suffixExponent r) *
              D.endpoint := by
          rw [pow_add]

/-- full inner affine equation。 -/
theorem full_backwardAffine_realization
    (D : E2ZeroCenteredTrajectoryData) :
    3 ^ D.length * D.startValue +
        D.backwardAffine D.length =
      2 ^ D.totalExponent * D.endpoint := by
  simpa [startValue, totalExponent] using
    D.backwardAffine_realization (r := D.length) le_rfl

/-- crossing gap は正。 -/
theorem crossingGap_pos
    (D : E2ZeroCenteredTrajectoryData) :
    0 < D.crossingGap := by
  dsimp [crossingGap, totalExponent]
  exact Nat.sub_pos_of_lt D.whole_contracting

/-- crossing gap の subtraction-free equation。 -/
theorem crossingGap_add_nine_threePow
    (D : E2ZeroCenteredTrajectoryData) :
    D.crossingGap + 9 * 3 ^ D.length =
      8 * 2 ^ D.totalExponent := by
  dsimp [crossingGap]
  exact Nat.sub_add_cancel (Nat.le_of_lt D.whole_contracting)

/--
recurrence の全長 exact divisibility kernel。

`G*T + (18*n-5)*3^m = 8*B`。
-/
theorem crossingBalance
    (D : E2ZeroCenteredTrajectoryData) :
    D.crossingGap * D.endpoint +
        D.endpointDefect * 3 ^ D.length =
      8 * D.backwardAffine D.length := by
  have hReal := D.full_backwardAffine_realization
  have hGap := D.crossingGap_add_nine_threePow
  have hDef :=
    D.eight_mul_start_add_defect_eq_nine_mul_endpoint
  have hReal8 :=
    congrArg (fun z : ℕ => 8 * z) hReal
  have hGapT :=
    congrArg (fun z : ℕ => z * D.endpoint) hGap
  have hDefPow :=
    congrArg (fun z : ℕ => 3 ^ D.length * z) hDef
  ring_nf at hReal8 hGapT hDefPow ⊢
  nlinarith

/-- crossing residual は正。 -/
theorem endpointDefect_threePow_lt_eight_mul_backwardAffine
    (D : E2ZeroCenteredTrajectoryData) :
    D.endpointDefect * 3 ^ D.length <
      8 * D.backwardAffine D.length := by
  have hG := D.crossingGap_pos
  have hT := D.endpoint_pos
  have hGT : 0 < D.crossingGap * D.endpoint :=
    Nat.mul_pos hG hT
  have h := D.crossingBalance
  omega

/-- `G` は affine residual を割る。 -/
theorem crossingGap_dvd_affineResidual
    (D : E2ZeroCenteredTrajectoryData) :
    D.crossingGap ∣
      8 * D.backwardAffine D.length -
        D.endpointDefect * 3 ^ D.length := by
  refine ⟨D.endpoint, ?_⟩
  have h := D.crossingBalance
  omega

/-- endpoint defect は `3*m` より小さい。 -/
theorem endpointDefect_lt_three_mul_length
    (D : E2ZeroCenteredTrajectoryData) :
    D.endpointDefect < 3 * D.length := by
  have hn := D.six_mul_n_lt_length
  have hdef := D.endpointDefect_add_five
  omega

/--
effective 2-3 gap のもとで whole crossing gap は `m+2` 以上。
-/
theorem length_add_two_le_crossingGap
    (D : E2ZeroCenteredTrajectoryData)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    D.length + 2 ≤ D.crossingGap := by
  have hContract :
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
  have h :=
    External.twoThreeGap_ge_exponent
      hEffective hContract
  simpa [crossingGap, pow_add, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

/-- effective gap のもとでは defect は `3*G` 未満。 -/
theorem endpointDefect_lt_three_mul_crossingGap
    (D : E2ZeroCenteredTrajectoryData)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    D.endpointDefect < 3 * D.crossingGap := by
  have hc := D.endpointDefect_lt_three_mul_length
  have hG := D.length_add_two_le_crossingGap hEffective
  have hmG : D.length < D.crossingGap := by
    omega
  have hscaled : 3 * D.length < 3 * D.crossingGap :=
    (Nat.mul_lt_mul_left (by omega : 0 < 3)).2 hmG
  omega

/--
endpoint defect は crossing gap に対して三帯域のどれかに入る。
これが divisibility kernel 後の有限分岐。
-/
theorem endpointDefect_threeBand
    (D : E2ZeroCenteredTrajectoryData)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    D.endpointDefect < D.crossingGap ∨
      (D.crossingGap ≤ D.endpointDefect ∧
        D.endpointDefect < 2 * D.crossingGap) ∨
      (2 * D.crossingGap ≤ D.endpointDefect ∧
        D.endpointDefect < 3 * D.crossingGap) := by
  have hlt := D.endpointDefect_lt_three_mul_crossingGap hEffective
  by_cases h0 : D.endpointDefect < D.crossingGap
  · exact Or.inl h0
  · by_cases h1 : D.endpointDefect < 2 * D.crossingGap
    · exact Or.inr (Or.inl ⟨by omega, h1⟩)
    · exact Or.inr (Or.inr ⟨by omega, hlt⟩)

end E2ZeroCenteredTrajectoryData
end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
