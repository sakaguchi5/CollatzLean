import CollatzLean.CollatzSecondLayer3.PolynomialCrossing
import CollatzLean.CollatzWindowCore.Normalization
import CollatzLean.CollatzWindowCore.Synchronization
import CollatzLean.CollatzSecondLayer3.AlternativeExclusion


/-!
# first-crossing全体からの標準polynomial prepared family

future-minimumからfirst-crossing終点までの正差を完全2進分解し、
最小同期境界まで進める。Baker型gapで開始値を多項式化し、
同期境界が消費できる深さを`first-crossing length`で抑えることで、
準備後のq-window終点も同じ長さの固定多項式以下にする。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- k段後の値に1を足したものは`4^k`倍で粗く抑えられる。 -/
theorem value_add_one_le_fourPow_mul
    (O : OddOrbit) (i k : ℕ) :
    O.value (i + k) + 1 ≤ 4 ^ k * (O.value i + 1) := by
  induction k generalizing i with
  | zero =>
      simp
  | succ k ih =>
      have hpow : 1 ≤ 2 ^ O.exponent i := by
        exact Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.pow_pos (by omega)))
      have hnext :
          O.value (i + 1) ≤ 3 * O.value i + 1 := by
        calc
          O.value (i + 1)
              ≤ 2 ^ O.exponent i * O.value (i + 1) := by
                simpa using
                  Nat.mul_le_mul_right (O.value (i + 1)) hpow
          _ = 3 * O.value i + 1 :=
            O.step i
      have hstep :
          O.value (i + 1) + 1 ≤ 4 * (O.value i + 1) := by
        omega
      have htail :
          O.value ((i + 1) + k) + 1 ≤
            4 ^ k * (O.value (i + 1) + 1) :=
        ih (i := i + 1)
      calc
        O.value (i + (k + 1)) + 1
            ≤ 4 ^ k * (O.value (i + 1) + 1) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using htail
        _ ≤ 4 ^ k * (4 * (O.value i + 1)) :=
          Nat.mul_le_mul_left _ hstep
        _ = 4 ^ (k + 1) * (O.value i + 1) := by
          rw [pow_succ]
          ring

end OddOrbit

/-- moving first-crossingの第j項に対応するfull-window差分。 -/
noncomputable def movingFullWindowDifference
    {O : OddOrbit} (F : MovingFirstCrossingData O) (j : ℕ) :
    O.WindowDifferenceData
      (F.minima.index j) (F.crossingLength j) := by
  let n := F.minima.index j
  let p := F.crossingLength j
  have hp : 0 < p := (F.crossing j).length_pos
  have hle : O.value n ≤ O.value (n + p) :=
    F.minima.futureMinimum j (n + p) (by omega)
  have hne : O.value n ≠ O.value (n + p) := by
    apply O.value_ne_of_lt_of_unbounded F.unbounded
    omega
  have hlt : O.value n < O.value (n + p) := by omega
  exact O.windowDifferenceData_of_lt hlt

/-- full-windowを最小同期境界まで準備する。 -/
noncomputable def movingFullWindowPreparation
    {O : OddOrbit} (F : MovingFirstCrossingData O) (j : ℕ) :
    O.SynchronizedPreparationData
      (F.minima.index j) (F.crossingLength j) :=
  O.prepareWindow
    (movingFullWindowDifference F j)
    (F.crossing j).length_pos

/-- full-window差分の2冪部分はfirst-crossing長以下。 -/
theorem movingFullWindow_pow_depth_le_length
    {O : OddOrbit} (F : MovingFirstCrossingData O) (j : ℕ) :
    2 ^ (movingFullWindowDifference F j).depth ≤
      F.crossingLength j := by
  let n := F.minima.index j
  let p := F.crossingLength j
  let D := movingFullWindowDifference F j
  have hend := firstCrossing_endpoint_le_start_add_length (F.crossing j)
  have hu : 0 < D.oddPart := by
    rcases D.oddPart_odd with ⟨u, hu⟩
    omega
  have hdiff : 2 ^ D.depth * D.oddPart ≤ p := by
    have hd := D.difference
    dsimp [D, n, p] at hd ⊢
    omega
  have huone : 1 ≤ D.oddPart := Nat.succ_le_iff.mpr hu
  calc
    2 ^ D.depth = 2 ^ D.depth * 1 := by simp
    _ ≤ 2 ^ D.depth * D.oddPart :=
      Nat.mul_le_mul_left _ huone
    _ ≤ p := hdiff

/-- 同期境界長に対応する`4^k`はfirst-crossing長の二乗以下。 -/
theorem movingFullWindow_fourPow_boundary_le_sq
    {O : OddOrbit} (F : MovingFirstCrossingData O) (j : ℕ) :
    4 ^ (movingFullWindowPreparation F j).boundaryLength ≤
      (F.crossingLength j) ^ 2 := by
  let n := F.minima.index j
  let p := F.crossingLength j
  let D := movingFullWindowDifference F j
  let k := OddOrbit.synchronizationBoundaryLength D
  change 4 ^ k ≤ p ^ 2
  have hvalid : Valid (O.segmentWord n k) :=
    (O.runs_segment n k).valid
  have hksteps : k ≤ O.windowTwoSteps n k := by
    have h := oddSteps_le_twoSteps hvalid
    simpa [OddOrbit.windowTwoSteps, oddSteps] using h
  have hconsumed : O.windowTwoSteps n k < D.depth := by
    simpa [k, n] using
      OddOrbit.synchronizationBoundaryLength_consumed_lt D
  have hkd : k ≤ D.depth := by omega
  have hpowkd : 4 ^ k ≤ 4 ^ D.depth :=
    Nat.pow_le_pow_right (by omega) hkd
  have htwo : 2 ^ D.depth ≤ p := by
    simpa [D, p] using movingFullWindow_pow_depth_le_length F j
  calc
    4 ^ k ≤ 4 ^ D.depth := hpowkd
    _ = 2 ^ D.depth * 2 ^ D.depth := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    _ ≤ p * p := Nat.mul_le_mul htwo htwo
    _ = p ^ 2 := by ring

/-- first-crossing全体から自動構成されるpolynomial prepared family。 -/
structure PolynomialPreparedFullWindowFamily
    {O : OddOrbit} (F : MovingFirstCrossingData O) where
  offset : ℕ → ℕ
  packet : ∀ j : ℕ,
    O.PreparedWindowPacket
      (F.minima.index j + offset j)
      (F.crossingLength j)
  K : ℕ
  A : ℕ
  endpointBound : ∀ j : ℕ,
    O.value
        (F.minima.index j + offset j + F.crossingLength j) ≤
      K * (F.crossingLength j + 1) ^ A

/--
first crossing始点のpolynomial boundから、
first crossing終点の`+1`を一段大きいpolynomialへ吸収する。
-/
private theorem firstCrossing_endpoint_add_one_polynomial
    {O : OddOrbit}
    {F : MovingFirstCrossingData O}
    {K A j : ℕ}
    (hstartj :
      O.value (F.minima.index j) ≤
        K * (F.crossingLength j + 1) ^ A) :
    O.value (F.minima.index j + F.crossingLength j) + 1 ≤
      (K + 1) * (F.crossingLength j + 1) ^ (A + 1) := by
  let n := F.minima.index j
  let p := F.crossingLength j
  have hend :
      O.value (n + p) ≤ O.value n + p :=
    firstCrossing_endpoint_le_start_add_length (F.crossing j)
  have hpowA :
      (p + 1) ^ A ≤ (p + 1) ^ (A + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hpbase :
      p + 1 ≤ (p + 1) ^ (A + 1) := by
    have h :=
      Nat.pow_le_pow_right
        (by omega : 0 < p + 1)
        (by omega : 1 ≤ A + 1)
    simpa using h
  calc
    O.value (n + p) + 1
        ≤ O.value n + p + 1 := by
            omega
    _ ≤ K * (p + 1) ^ A + (p + 1) := by
          simpa [n, p, Nat.add_assoc] using
            Nat.add_le_add_right hstartj (p + 1)
    _ ≤ K * (p + 1) ^ (A + 1) +
          (p + 1) ^ (A + 1) := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_left K hpowA)
            hpbase
    _ = (K + 1) * (p + 1) ^ (A + 1) := by
          ring

/--
moving full-window preparationのboundary終点値を、
`4^boundaryLength`倍のfirst crossing終点値で評価する。
-/
private theorem movingFullWindow_endpoint_le_fourPow_mul
    {O : OddOrbit}
    (F : MovingFirstCrossingData O)
    (j : ℕ) :
    O.value
        (F.minima.index j +
          (movingFullWindowPreparation F j).boundaryLength +
          F.crossingLength j)
      ≤
        4 ^ (movingFullWindowPreparation F j).boundaryLength *
          (O.value (F.minima.index j + F.crossingLength j) + 1) := by
  let n := F.minima.index j
  let p := F.crossingLength j
  let S := movingFullWindowPreparation F j
  let k := S.boundaryLength
  have htail :=
    OddOrbit.value_add_one_le_fourPow_mul O (n + p) k
  have hindex :
      F.minima.index j +
            (movingFullWindowPreparation F j).boundaryLength +
            F.crossingLength j =
        n + p + k := by
    dsimp [n, p, k, S]
    omega
  rw [hindex]
  calc
    O.value (n + p + k)
        ≤ O.value (n + p + k) + 1 := by
            omega
    _ ≤ 4 ^ k * (O.value (n + p) + 1) := by
          simpa [Nat.add_assoc] using htail

/--
boundaryの二次上界とfirst crossing終点のpolynomial boundを合成し、
prepared endpointを指数`A+3`のpolynomialで評価する。
-/
private theorem movingFullWindow_endpoint_polynomial
    {O : OddOrbit}
    (F : MovingFirstCrossingData O)
    (j K A : ℕ)
    (hy :
      O.value (F.minima.index j + F.crossingLength j) + 1 ≤
        (K + 1) * (F.crossingLength j + 1) ^ (A + 1)) :
    O.value
        (F.minima.index j +
          (movingFullWindowPreparation F j).boundaryLength +
          F.crossingLength j)
      ≤
        (K + 1) * (F.crossingLength j + 1) ^ (A + 3) := by
  let p := F.crossingLength j
  let S := movingFullWindowPreparation F j
  let k := S.boundaryLength
  have htransport :=
    movingFullWindow_endpoint_le_fourPow_mul F j
  have hfour : 4 ^ k ≤ p ^ 2 := by
    simpa [k, p, S] using
      movingFullWindow_fourPow_boundary_le_sq F j
  have hp2 : p ^ 2 ≤ (p + 1) ^ 2 := by
    ring_nf
    nlinarith
  calc
    O.value
        (F.minima.index j +
          (movingFullWindowPreparation F j).boundaryLength +
          F.crossingLength j)
        ≤ 4 ^ k *
            (O.value (F.minima.index j + F.crossingLength j) + 1) := by
              simpa [k, p, S] using htransport
    _ ≤ p ^ 2 *
          ((K + 1) * (p + 1) ^ (A + 1)) :=
      Nat.mul_le_mul hfour (by simpa [p] using hy)
    _ ≤ (p + 1) ^ 2 *
          ((K + 1) * (p + 1) ^ (A + 1)) :=
      Nat.mul_le_mul_right _ hp2
    _ = (K + 1) * (p + 1) ^ (A + 3) := by
      rw [show A + 3 = 2 + (A + 1) by omega, pow_add]
      ring

/-- Baker型gap入力から標準polynomial prepared familyを構成する。 -/
noncomputable def polynomialPreparedFullWindowFamily
    {O : OddOrbit}
    (hGap : TwoThreeGapPolynomialBound)
    (F : MovingFirstCrossingData O) :
    PolynomialPreparedFullWindowFamily F := by
  classical
  let hex :=
    futureMinimum_firstCrossing_start_polynomial hGap
  let K := Classical.choose hex
  let hexA := Classical.choose_spec hex
  let A := Classical.choose hexA
  have hstart := Classical.choose_spec hexA
  refine
    { offset := fun j =>
        (movingFullWindowPreparation F j).boundaryLength
      packet := fun j =>
        (movingFullWindowPreparation F j).packet
      K := K + 1
      A := A + 3
      endpointBound := ?_ }
  intro j
  have hstartj :
      O.value (F.minima.index j) ≤
        K * (F.crossingLength j + 1) ^ A :=
    hstart
      O
      (F.minima.index j)
      (F.crossingLength j)
      (F.minima.futureMinimum j)
      (F.crossing j)
  have hy :
      O.value
          (F.minima.index j + F.crossingLength j) + 1
        ≤
          (K + 1) *
            (F.crossingLength j + 1) ^ (A + 1) :=
    firstCrossing_endpoint_add_one_polynomial hstartj
  exact movingFullWindow_endpoint_polynomial F j K A hy

namespace PolynomialPreparedFullWindowFamily

/-- familyの第j項におけるactual開始位置。 -/
def start
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) (j : ℕ) : ℕ :=
  F.minima.index j + P.offset j

/-- 十分後にはlower natural replayが存在しない。 -/
theorem eventually_no_lowerNaturalReplay
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ¬ Nonempty
        (LowerNaturalRunReplayData
          (O.segmentWord (P.start j) (F.crossingLength j))
          (O.value (P.start j))
          (O.value (P.start j + F.crossingLength j))) := by
  obtain ⟨N, hN⟩ :=
    polynomialBelowTwoMulThreePower P.K P.A
  obtain ⟨J, hJ⟩ := F.lengths_tend_to_infinity N
  refine ⟨J, ?_⟩
  intro j hj hReplay
  rcases hReplay with ⟨L⟩
  have hlen :
      N ≤ F.crossingLength j :=
    (hJ j hj).le
  have hlarge :
      2 * 3 ^ F.crossingLength j <
        O.value (P.start j + F.crossingLength j) :=
    OddOrbit.PreparedWindowAlternative.endpoint_gt_two_mul_threePow_of_lowerReplay
      (P.packet j) L
  have hsmall :
      O.value (P.start j + F.crossingLength j) <
        2 * 3 ^ F.crossingLength j := by
    exact lt_of_le_of_lt
      (P.endpointBound j)
      (hN (F.crossingLength j) (by omega))
  omega

/-- 十分後にはpositive predecessor shadowが存在しない。 -/
theorem eventually_no_positivePredecessorShadow
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ¬ ((P.packet j).replayCoordinate.quotient = 0 ∧
        0 < predecessorShadow
          (O.segmentWord (P.start j) (F.crossingLength j))) := by
  obtain ⟨N, hN⟩ :=
    polynomialBelowTwoMulThreePower P.K P.A
  obtain ⟨J, hJ⟩ := F.lengths_tend_to_infinity N
  refine ⟨J, ?_⟩
  intro j hj hPositive
  rcases hPositive with ⟨hq, hshadow⟩
  have hlen :
      N ≤ F.crossingLength j :=
    (hJ j hj).le
  have hlarge :
      2 * 3 ^ F.crossingLength j <
        O.value (P.start j + F.crossingLength j) :=
    OddOrbit.PreparedWindowAlternative.endpoint_gt_two_mul_threePow_of_positiveShadow
      (P.packet j) hq hshadow
  have hsmall :
      O.value (P.start j + F.crossingLength j) <
        2 * 3 ^ F.crossingLength j := by
    exact lt_of_le_of_lt
      (P.endpointBound j)
      (hN (F.crossingLength j) (by omega))
  omega

/-- 十分後の各標準prepared full-windowはcaptureまたはSpecial C3。 -/
theorem eventually_capture_or_specialC3
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      Nonempty
        (O.CapturedWindowAt (P.start j) (F.crossingLength j) ⊕
          SpecialC3At O (P.start j) (F.crossingLength j)) := by
  obtain ⟨J₁, hLower⟩ := P.eventually_no_lowerNaturalReplay
  obtain ⟨J₂, hPositive⟩ := P.eventually_no_positivePredecessorShadow
  refine ⟨max J₁ J₂, ?_⟩
  intro j hj
  have hj₁ : J₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj₂ : J₂ ≤ j := le_trans (le_max_right _ _) hj
  rcases
      OddOrbit.preparedWindowAnalysis_nonempty (P.packet j) with
    ⟨hAlt | hSpecial⟩
  · cases hAlt with
    | captured hcap =>
        exact ⟨Sum.inl hcap⟩
    | lowerNaturalReplay hReplay =>
        exact False.elim (hLower j hj₁ ⟨hReplay⟩)
    | positivePredecessorShadow hq hshadow =>
        exact False.elim (hPositive j hj₂ ⟨hq, hshadow⟩)
  · exact ⟨Sum.inr hSpecial⟩

end PolynomialPreparedFullWindowFamily
end CollatzSecondLayer3
