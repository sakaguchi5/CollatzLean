import CollatzLean.CollatzSecondLayer2.Arithmetic
import CollatzLean.CollatzSecondLayer2.WindowAnalysis



/-!
# polynomial-small prepared window列のalternative排除

endpointがwindow長に対して一様に多項式小なら、lower natural replayと
positive predecessor shadowは十分後には起こらない。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- 一様多項式上界を持つprepared q-window列。 -/
structure PolynomialPreparedWindowSequence (O : OddOrbit) where
  start : ℕ → ℕ
  length : ℕ → ℕ
  start_strict : StrictMono start
  packet : ∀ j : ℕ, PreparedWindowPacket O (start j) (length j)
  K : ℕ
  A : ℕ
  endpointBound : ∀ j : ℕ,
    O.value (start j + length j) ≤
      K * (length j + 1) ^ A
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < length j

namespace PolynomialPreparedWindowSequence

/-- 十分長い項ではlower natural replayは存在しない。 -/
theorem eventually_no_lowerNaturalReplay
    {O : OddOrbit}
    (S : PolynomialPreparedWindowSequence O) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ¬ Nonempty
        (LowerNaturalRunReplayData
          (O.segmentWord (S.start j) (S.length j))
          (O.value (S.start j))
          (O.value (S.start j + S.length j))) := by
  obtain ⟨N, hN⟩ := polynomialBelowTwoMulThreePower S.K S.A
  obtain ⟨J, hJ⟩ := S.lengths_tend_to_infinity N
  refine ⟨J, ?_⟩
  intro j hj hReplay
  rcases hReplay with ⟨L⟩
  have hlen : N ≤ S.length j :=
    Nat.le_of_lt (hJ j hj)
  have hlarge :
      2 * 3 ^ S.length j < O.value (S.start j + S.length j) :=
    PreparedWindowAlternative.endpoint_gt_two_mul_threePow_of_lowerReplay
      (S.packet j) L
  have hsmall :
      O.value (S.start j + S.length j) < 2 * 3 ^ S.length j := by
    exact lt_of_le_of_lt (S.endpointBound j)
      (hN (S.length j) (by omega))
  omega

/-- 十分長い項ではcanonical positive predecessor shadowは存在しない。 -/
theorem eventually_no_positivePredecessorShadow
    {O : OddOrbit}
    (S : PolynomialPreparedWindowSequence O) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ¬ ((S.packet j).replayCoordinate.quotient = 0 ∧
        0 < predecessorShadow
          (O.segmentWord (S.start j) (S.length j))) := by
  obtain ⟨N, hN⟩ := polynomialBelowTwoMulThreePower S.K S.A
  obtain ⟨J, hJ⟩ := S.lengths_tend_to_infinity N
  refine ⟨J, ?_⟩
  intro j hj hPositive
  rcases hPositive with ⟨hq, hshadow⟩
  have hlen : N ≤ S.length j :=
    Nat.le_of_lt (hJ j hj)
  have hlarge :
      2 * 3 ^ S.length j < O.value (S.start j + S.length j) :=
    PreparedWindowAlternative.endpoint_gt_two_mul_threePow_of_positiveShadow
      (S.packet j) hq hshadow
  have hsmall :
      O.value (S.start j + S.length j) < 2 * 3 ^ S.length j := by
    exact lt_of_le_of_lt (S.endpointBound j)
      (hN (S.length j) (by omega))
  omega

/--
十分後の各項はcaptured carryまたはSpecial C3のどちらかへ落ちる。
-/
theorem eventually_capture_or_specialC3
    {O : OddOrbit}
    (S : PolynomialPreparedWindowSequence O) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      Nonempty
        (CapturedWindowAt O (S.start j) (S.length j) ⊕
          SpecialC3At O (S.start j) (S.length j)) := by
  obtain ⟨J₁, hLower⟩ := S.eventually_no_lowerNaturalReplay
  obtain ⟨J₂, hPositive⟩ := S.eventually_no_positivePredecessorShadow
  refine ⟨max J₁ J₂, ?_⟩
  intro j hj
  have hj₁ : J₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj₂ : J₂ ≤ j := le_trans (le_max_right _ _) hj
  rcases preparedWindowAnalysis_nonempty (S.packet j) with ⟨hAlt | hSpecial⟩
  · cases hAlt with
    | captured hcap => exact ⟨Sum.inl hcap⟩
    | lowerNaturalReplay hReplay =>
        exact False.elim (hLower j hj₁ ⟨hReplay⟩)
    | positivePredecessorShadow hq hshadow =>
        exact False.elim (hPositive j hj₂ ⟨hq, hshadow⟩)
  · exact ⟨Sum.inr hSpecial⟩

end PolynomialPreparedWindowSequence
end OddOrbit
end CollatzSecondLayer2
