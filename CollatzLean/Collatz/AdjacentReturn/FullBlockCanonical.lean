import CollatzLean.Collatz.AdjacentReturn.StrongContractingTail
import CollatzLean.Collatz.AdjacentReturn.Bounds
import CollatzLean.Collatz.AdjacentReturn.FirstCrossingBridge
import CollatzLean.Collatz.Canonical.Replay

/-!
# contracting full block の sharp arithmetic と eventual canonical 化

first crossing だけでなく adjacent contracting block 全体に対して
値差 slack と Baker 型 bound を使い、十分長い block の actual start/end が
canonical start/end そのものになることを示す。
-/

namespace Collatz
namespace AdjacentReturn

namespace State

/-- contracting full block では adjacent 値差も `3*Δ < length`。 -/
theorem three_mul_valueGap_lt_length
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    3 * R.valueGap < R.length := by
  have hdelta :=
    R.twoPow_totalExponent_mul_valueGap_lt_affineConstant hC
  have hsharp :=
    R.three_mul_affineConstant_lt_length_mul_twoPow hC
  have hscaled :
      3 * (2 ^ R.totalExponent * R.valueGap) <
        3 * R.affineConstant :=
    (Nat.mul_lt_mul_left (by omega : 0 < (3 : ℕ))).2 hdelta
  have hchain :
      (3 * R.valueGap) * 2 ^ R.totalExponent <
        R.length * 2 ^ R.totalExponent := by
    calc
      (3 * R.valueGap) * 2 ^ R.totalExponent
          = 3 * (2 ^ R.totalExponent * R.valueGap) := by ring
      _ < 3 * R.affineConstant := hscaled
      _ < R.length * 2 ^ R.totalExponent := hsharp
  exact
    (Nat.mul_lt_mul_right
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))).mp hchain

/-- full block return slack `length - 3*valueGap`。 -/
def fullReturnSlack {O : OddOrbit} (R : State O) : ℕ :=
  R.length - 3 * R.valueGap

/-- contracting full block の full slack は正。 -/
theorem fullReturnSlack_pos
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    0 < R.fullReturnSlack := by
  unfold fullReturnSlack
  exact Nat.sub_pos_of_lt (R.three_mul_valueGap_lt_length hC)

/--
contracting identity と all-suffix sharp bound から
`3*g*start < slack*2^H`。
-/
theorem three_mul_contractingGap_mul_start_lt_slack_twoPow
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    3 * R.contractingGap * R.startValue <
      R.fullReturnSlack * 2 ^ R.totalExponent := by
  have hid := R.contractingIdentity hC
  have hsharp :=
    R.three_mul_affineConstant_lt_length_mul_twoPow hC
  have hlen :
      R.length = 3 * R.valueGap + R.fullReturnSlack := by
    unfold fullReturnSlack
    have h := R.three_mul_valueGap_lt_length hC
    omega
  have hlhs :
      3 * R.affineConstant =
        (3 * R.valueGap) * 2 ^ R.totalExponent +
          3 * R.contractingGap * R.startValue := by
    rw [hid]
    ring
  have hrhs :
      R.length * 2 ^ R.totalExponent =
        (3 * R.valueGap) * 2 ^ R.totalExponent +
          R.fullReturnSlack * 2 ^ R.totalExponent := by
    rw [hlen]
    ring
  rw [hlhs, hrhs] at hsharp
  omega

/-- Baker 入力から full block start の polynomial bound を得る。 -/
theorem startValue_polynomial_bound
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
        R.IsContracting →
        3 * R.startValue < K * (R.length + 1) ^ A := by
  rcases hGap with ⟨K, A, hK, hBaker⟩
  refine ⟨K + 1, A + 1, ?_⟩
  intro O R hC
  have hcontract :
      3 ^ R.length < 2 ^ R.totalExponent := by
    simpa [IsContracting, Word.Contracting,
      State.totalExponent, R.oddSteps_word] using hC
  have hg : 0 < R.contractingGap := by
    unfold contractingGap
    omega
  have hBaker' :
      3 ^ R.length ≤
        K * (R.length + 1) ^ A * R.contractingGap := by
    simpa [contractingGap] using
      hBaker R.length R.totalExponent R.length_pos hcontract
  have htwo :
      2 ^ R.totalExponent =
        3 ^ R.length + R.contractingGap := by
    unfold contractingGap
    omega
  have htwoBound :
      2 ^ R.totalExponent ≤
        (K * (R.length + 1) ^ A + 1) * R.contractingGap := by
    rw [htwo]
    calc
      3 ^ R.length + R.contractingGap
          ≤ K * (R.length + 1) ^ A * R.contractingGap +
              R.contractingGap :=
        Nat.add_le_add_right hBaker' R.contractingGap
      _ = (K * (R.length + 1) ^ A + 1) *
            R.contractingGap := by ring
  have hslack :=
    R.three_mul_contractingGap_mul_start_lt_slack_twoPow hC
  have hwithGap :
      R.contractingGap * (3 * R.startValue) <
        R.contractingGap *
          (R.fullReturnSlack *
            (K * (R.length + 1) ^ A + 1)) := by
    calc
      R.contractingGap * (3 * R.startValue)
          = 3 * R.contractingGap * R.startValue := by ring
      _ < R.fullReturnSlack * 2 ^ R.totalExponent := hslack
      _ ≤ R.fullReturnSlack *
            ((K * (R.length + 1) ^ A + 1) *
              R.contractingGap) :=
        Nat.mul_le_mul_left R.fullReturnSlack htwoBound
      _ = R.contractingGap *
          (R.fullReturnSlack *
            (K * (R.length + 1) ^ A + 1)) := by ring
  have hraw :
      3 * R.startValue <
        R.fullReturnSlack *
          (K * (R.length + 1) ^ A + 1) :=
    (Nat.mul_lt_mul_left hg).mp hwithGap
  have hslackLe : R.fullReturnSlack ≤ R.length := by
    unfold fullReturnSlack
    omega
  have hpowPos : 0 < (R.length + 1) ^ A :=
    Nat.pow_pos (by omega)
  have hpowOne : 1 ≤ (R.length + 1) ^ A := by
    omega
  have hinner :
      K * (R.length + 1) ^ A + 1 ≤
        (K + 1) * (R.length + 1) ^ A := by
    calc
      K * (R.length + 1) ^ A + 1
          ≤ K * (R.length + 1) ^ A +
              (R.length + 1) ^ A :=
        Nat.add_le_add_left hpowOne _
      _ = (K + 1) * (R.length + 1) ^ A := by ring
  have hcoarse :
      R.fullReturnSlack *
          (K * (R.length + 1) ^ A + 1) ≤
        (K + 1) * (R.length + 1) ^ (A + 1) := by
    calc
      R.fullReturnSlack *
          (K * (R.length + 1) ^ A + 1)
          ≤ R.length *
              ((K + 1) * (R.length + 1) ^ A) :=
        Nat.mul_le_mul hslackLe hinner
      _ ≤ (R.length + 1) *
              ((K + 1) * (R.length + 1) ^ A) := by
        exact Nat.mul_le_mul_right
          ((K + 1) * (R.length + 1) ^ A)
          (by omega)
      _ = (K + 1) * (R.length + 1) ^ (A + 1) := by
        rw [pow_succ]
        ring
  exact lt_of_lt_of_le hraw hcoarse

/-- sufficiently long contracting full block has start below its canonical modulus. -/
theorem startValue_lt_residueModulus_eventually_by_length
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
        R.IsContracting →
        N ≤ R.length →
          R.startValue < R.word.residueModulus := by
  obtain ⟨K, A, hpoly⟩ := startValue_polynomial_bound hGap
  obtain ⟨N, hN⟩ := Arithmetic.polynomialBelowTwoPower K A
  refine ⟨N, ?_⟩
  intro O R hC hlen
  have hbound := hpoly O R hC
  have hdom := hN R.length hlen
  have hstartPow : R.startValue < 2 ^ (R.length + 1) := by
    have hxPos : 0 < R.startValue := O.value_pos R.startIndex
    omega
  have hrH :
      R.length ≤ R.totalExponent := by
    have h :=
      Word.oddSteps_le_twoSteps R.word_valid
    rw [R.oddSteps_word] at h
    simpa [State.totalExponent] using h
  have hpowLe :
      2 ^ (R.length + 1) ≤ 2 ^ (R.totalExponent + 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
  calc
    R.startValue < 2 ^ (R.length + 1) := hstartPow
    _ ≤ 2 ^ (R.totalExponent + 1) := hpowLe
    _ = R.word.residueModulus := by
      simp [Word.residueModulus, State.totalExponent]

/-- sufficiently long contracting full block starts at its canonical start. -/
theorem startValue_eq_canonicalStart_eventually_by_length
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
        R.IsContracting →
        N ≤ R.length →
          R.startValue = R.word.canonicalStart := by
  obtain ⟨N, hN⟩ :=
    startValue_lt_residueModulus_eventually_by_length hGap
  refine ⟨N, ?_⟩
  intro O R hC hlen
  exact R.realizes.eq_canonicalStart_of_lt_modulus
    (O.value_odd R.nextIndex) (hN O R hC hlen)

/-- sufficiently long contracting full block also ends at its canonical end. -/
theorem nextValue_eq_canonicalEnd_eventually_by_length
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
        R.IsContracting →
        N ≤ R.length →
          R.nextValue = R.word.canonicalEnd := by
  obtain ⟨N, hN⟩ :=
    startValue_eq_canonicalStart_eventually_by_length hGap
  refine ⟨N, ?_⟩
  intro O R hC hlen
  let C : Word.ReplayCoordinate R.word R.startValue R.nextValue :=
    Word.ReplayCoordinate.ofRealization R.realizes (O.value_odd R.nextIndex)
  have hstart : R.startValue = R.word.canonicalStart :=
    hN O R hC hlen
  have hq : C.quotient = 0 :=
    C.quotient_eq_zero_of_start_eq_canonical hstart
  have hfinish := C.finish_eq
  rw [hq] at hfinish
  simpa using hfinish

/-- contracting adjacent future minima satisfy a strict multiplicative corridor. -/
theorem two_mul_nextValue_add_one_lt_three_mul_startValue_add_one
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    2 * (R.nextValue + 1) < 3 * (R.startValue + 1) := by
  have hgap := R.three_mul_valueGap_lt_length hC
  have hdelta := R.four_le_valueGap
  have hlenTwo : 1 < R.length := by
    omega
  have hindex : R.startIndex + 1 < R.nextIndex := by
    rw [R.nextIndex_eq_startIndex_add_length]
    omega
  have hle :
      R.nextValue ≤ O.value (R.startIndex + 1) :=
    R.nextValue_le_positiveEndpoint 1 (by omega)
  have hne :
      R.nextValue ≠ O.value (R.startIndex + 1) := by
    unfold State.nextValue
    exact (O.value_ne_of_lt_of_unbounded R.unbounded hindex).symm
  have hlt :
      R.nextValue < O.value (R.startIndex + 1) := by
    omega
  have hstep :
      2 * O.value (R.startIndex + 1) =
        3 * R.startValue + 1 := by
    have h := O.step R.startIndex
    rw [R.startExponent_eq_one] at h
    simpa [State.startValue] using h
  have hscaled :
      2 * R.nextValue < 3 * R.startValue + 1 := by
    calc
      2 * R.nextValue < 2 * O.value (R.startIndex + 1) :=
        (Nat.mul_lt_mul_left (by omega : 0 < (2 : ℕ))).2 hlt
      _ = 3 * R.startValue + 1 := hstep
  omega

end State

/-- eventually canonical な contracting block のまとめ。 -/
structure CanonicalContractingBlockData
    {O : OddOrbit} (R : State O) : Prop where
  contracting : R.IsContracting
  startCanonical : R.startValue = R.word.canonicalStart
  endCanonical : R.nextValue = R.word.canonicalEnd
  allSuffixesContracting : R.word.AllSuffixesContracting
  gapBound : 3 * R.valueGap < R.length

namespace EventuallyContractingTailData

/-- eventually contracting tail の full block lengths は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {O : OddOrbit} (D : EventuallyContractingTailData O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      M < (D.state n).length := by
  intro M
  classical
  let T : ContractingTower O := D.toContractingTower
  let F : ContractingFirstCrossingTower T :=
    Classical.choice T.existsFirstCrossingTower
  obtain ⟨J, hJ⟩ := F.lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro n hn
  have hcross : M < (F.tower_at n).length := hJ n hn
  have hle : (F.tower_at n).length ≤ (T.tower_at n).length :=
    (F.tower_at n).le_adjacent
  have hfull : M < (T.tower_at n).length :=
    lt_of_lt_of_le hcross hle
  simpa [T] using hfull

/-- Baker 入力のもと tail の全 sufficiently late full block は canonical。 -/
theorem blocks_eventually_canonical
    {O : OddOrbit} (D : EventuallyContractingTailData O)
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      CanonicalContractingBlockData (D.state n) := by
  obtain ⟨N₁, hStart⟩ :=
    State.startValue_eq_canonicalStart_eventually_by_length hGap
  obtain ⟨N₂, hEnd⟩ :=
    State.nextValue_eq_canonicalEnd_eventually_by_length hGap
  let N := max N₁ N₂
  obtain ⟨J, hJ⟩ := D.lengths_tend_to_infinity N
  refine ⟨J, ?_⟩
  intro n hn
  have hlen : N < (D.state n).length := hJ n hn
  have hC := D.state_contracting n
  refine {
    contracting := hC
    startCanonical := hStart O (D.state n) hC (by
      dsimp [N] at hlen
      omega)
    endCanonical := hEnd O (D.state n) hC (by
      dsimp [N] at hlen
      omega)
    allSuffixesContracting := (D.state n).allSuffixesContracting hC
    gapBound := (D.state n).three_mul_valueGap_lt_length hC
  }

end EventuallyContractingTailData

end AdjacentReturn
end Collatz
