import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ExtraDepthFerrersTransport
import CollatzLean.Collatz2.CSTMicro.BeattyPositions

/-!
# Critical boundary has zero odd-only extra depth

standard critical Sturmian boundary の odd positions は `beattyIndex k` であり、
odd-only rank geometry の critical roof は `Word.criticalHeight k` である。
この二つを exact power inequalities だけで同定する。

さらに run encoder の k-th checkpoint が「次の odd の位置」であることを一般補題として証明し、
critical boundary の odd-only encoding では

  prefixTwoDepth(k) = beattyIndex k = Word.criticalHeight k

を得る。従って全 proper odd cut で `extraDepth = 0`。
-/

namespace Collatz2
namespace CSTMicro

/--
run encoder の k-th checkpoint の直後まで読むと odd count は `k+1`。
`k < oddSteps` は次の odd が実際に存在することを表す。
-/
theorem prefixOddCount_succ_exponent_checkpoint
    (v : ParityWord)
    {k : ℕ}
    (hk : k < Collatz2.Word.oddSteps (exponentWordOfParity v)) :
    prefixOddCount v
        (leadingEvenCount v +
          Collatz2.Word.twoSteps ((exponentWordOfParity v).take k) + 1) =
      k + 1 := by
  induction v generalizing k with
  | nil =>
      simp at hk
  | cons b v ih =>
      cases b with
      | false =>
          have hk' :
              k < Collatz2.Word.oddSteps (exponentWordOfParity v) := by
            simpa using hk
          have hih := ih hk'
          have htime :
              leadingEvenCount v + 1 +
                    Collatz2.Word.twoSteps
                      ((exponentWordOfParity v).take k) + 1 =
                (leadingEvenCount v +
                    Collatz2.Word.twoSteps
                      ((exponentWordOfParity v).take k) + 1) + 1 := by
            omega
          simp only [
            leadingEvenCount_false_cons,
            exponentWordOfParity_false_cons
          ]
          rw [htime, prefixOddCount_cons_succ]
          simp [bitNat, hih]
      | true =>
          by_cases hk0 : k = 0
          · subst k
            simp [prefixOddCount, oddCount, bitNat]
          · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
            have hj :
                j < Collatz2.Word.oddSteps (exponentWordOfParity v) := by
              simp only [
                exponentWordOfParity_true_cons,
                Collatz2.Word.oddSteps_cons
              ] at hk
              omega
            have hih := ih hj
            have htime :
                leadingEvenCount v + 1 +
                      Collatz2.Word.twoSteps
                        ((exponentWordOfParity v).take j) + 1 =
                  (leadingEvenCount v +
                      Collatz2.Word.twoSteps
                        ((exponentWordOfParity v).take j) + 1) + 1 := by
              omega
            simp only [
              leadingEvenCount_true_cons,
              exponentWordOfParity_true_cons,
              List.take_succ_cons,
              Collatz2.Word.twoSteps_cons,
              zero_add
            ]
            rw [htime, prefixOddCount_cons_succ]
            simp [bitNat, hih]
            ac_rfl

/--
CST Beatty position と odd-only rank critical roof は同じ integer。

  beattyIndex k = Word.criticalHeight k   (k>0)
-/
theorem beattyIndex_eq_wordCriticalHeight
    {k : ℕ}
    (hk : 0 < k) :
    beattyIndex k = Collatz2.Word.criticalHeight k := by
  have hBeattyLow := beattyIndex_lower_strict_of_pos hk
  have hLe : beattyIndex k ≤ Collatz2.Word.criticalHeight k :=
    Collatz2.Word.le_criticalHeight_of_twoPow_lt_threePow hBeattyLow
  have hCritPow := Collatz2.Word.criticalHeight_pow_lt_threePow hk
  have hBeattyUp := beattyIndex_upper k
  have hGe : Collatz2.Word.criticalHeight k ≤ beattyIndex k := by
    by_contra hnot
    have hSucc : beattyIndex k + 1 ≤ Collatz2.Word.criticalHeight k := by
      omega
    have hPowLe :
        2 ^ (beattyIndex k + 1) ≤
          2 ^ Collatz2.Word.criticalHeight k :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hSucc
    omega
  omega

/--
critical boundary の odd-only encoding checkpoint は Beatty position そのもの。
-/
theorem criticalBoundaryWord_prefixTwoDepth_eq_beattyIndex
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k : ℕ}
    (hkLt :
      k < Collatz2.Word.oddSteps
        (exponentWordOfParity (criticalBoundaryWord v.length))) :
    Collatz2.Word.prefixTwoDepth
        (exponentWordOfParity (criticalBoundaryWord v.length)) k =
      beattyIndex k := by
  by_cases hk0 : k = 0
  · subst k
    simp [Collatz2.Word.prefixTwoDepth]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    let b : ParityWord := criticalBoundaryWord v.length
    let w : Collatz2.Word := exponentWordOfParity b
    let t : ℕ := Collatz2.Word.twoSteps (w.take k)
    have hBFP : IsFirstPassageWord b := by
      simpa [b] using criticalBoundaryWord_isFirstPassage hFP
    have hBLen : 1 < b.length := by
      simpa [b] using hLen
    have hLead : leadingEvenCount b = 0 :=
      hBFP.leadingEvenCount_eq_zero_of_one_lt_length hBLen
    have hkLe : k ≤ Collatz2.Word.oddSteps w := Nat.le_of_lt hkLt
    have hCountRaw :=
      prefixOddCount_at_exponent_checkpoint b k (by simpa [w] using hkLe)
    have hCount : prefixOddCount b t = k := by
      rw [hLead, zero_add] at hCountRaw
      simpa [t, w] using hCountRaw
    have hSuccRaw :=
      prefixOddCount_succ_exponent_checkpoint b (by simpa [w] using hkLt)
    have hSucc : prefixOddCount b (t + 1) = k + 1 := by
      rw [hLead, zero_add] at hSuccRaw
      simpa [t, w, Nat.add_assoc] using hSuccRaw
    have htPos : 0 < t := by
      by_contra hnot
      have ht0 : t = 0 :=
        Nat.eq_zero_of_not_pos hnot
      have hkZero : k = 0 := by
        rw [ht0] at hCount
        simpa [prefixOddCount, oddCount] using hCount.symm
      exact hk0 hkZero
    have hValid : Collatz2.Word.Valid w := by
      simpa [w] using exponentWordOfParity_valid b
    have htLtWord :
        Collatz2.Word.twoSteps (w.take k) < Collatz2.Word.twoSteps w :=
      twoSteps_take_lt_of_valid hValid hkLt
    have hTotal : Collatz2.Word.twoSteps w = b.length := by
      simpa [w] using hBFP.twoSteps_exponentWordOfParity_eq_length hBLen
    have htLt : t < b.length := by
      dsimp [t]
      rw [hTotal] at htLtWord
      exact htLtWord
    have hVPos : 0 < v.length := by omega
    have hPredLt : v.length - 1 < v.length := by omega
    have hLastPrefix0 :=
      criticalBoundaryWord_prefixOddCount
        (k := v.length) (j := v.length - 1) hVPos hPredLt
    have hLastPrefix :
        prefixOddCount b (v.length - 1) =
          criticalPrefixHeight (v.length - 1) := by
      simpa [b] using hLastPrefix0
    have hEndpoint0 := endpointOddCount_eq_criticalPrefixHeight_pred hBFP
    have hEndpoint :
        oddCount b = criticalPrefixHeight (v.length - 1) := by
      simpa [b] using hEndpoint0
    have hLast : prefixOddCount b (v.length - 1) = oddCount b :=
      hLastPrefix.trans hEndpoint.symm
    have hkOdd : k < oddCount b := by
      rw [← oddSteps_exponentWordOfParity b]
      simpa [w] using hkLt
    have htNeLast : t ≠ v.length - 1 := by
      intro htEq
      have hkEq : k = oddCount b := by
        calc
          k = prefixOddCount b t := hCount.symm
          _ = prefixOddCount b (v.length - 1) := by rw [htEq]
          _ = oddCount b := hLast
      omega
    have hBLenEq : b.length = v.length := by simp [b]
    have htLtV : t < v.length := by simpa [hBLenEq] using htLt
    have htLtPred : t < v.length - 1 := by omega
    have htSuccLt : t + 1 < v.length := by omega
    have hCritT0 :=
      criticalBoundaryWord_prefixOddCount
        (k := v.length) (j := t) hVPos htLtV
    have hCritT1_0 :=
      criticalBoundaryWord_prefixOddCount
        (k := v.length) (j := t + 1) hVPos htSuccLt
    have hCritT : criticalPrefixHeight t = k := by
      change prefixOddCount b t = criticalPrefixHeight t at hCritT0
      rw [hCount] at hCritT0
      exact hCritT0.symm
    have hCritT1 : criticalPrefixHeight (t + 1) = k + 1 := by
      change prefixOddCount b (t + 1) = criticalPrefixHeight (t + 1) at hCritT1_0
      rw [hSucc] at hCritT1_0
      exact hCritT1_0.symm
    have hBit : criticalSturmianBit t = true := by
      apply (criticalSturmianBit_eq_true_iff t).2
      rw [hCritT, hCritT1]
    have hPosEq := critical_true_position_eq_beattyIndex hBit
    rw [hCritT] at hPosEq
    unfold Collatz2.Word.prefixTwoDepth
    change t = beattyIndex k
    exact hPosEq

/--
critical boundary は odd-only critical roof に exact に乗るため、proper cut extra-depth は zero。
-/
theorem criticalBoundaryWord_extraDepth_eq_zero
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k : ℕ}
    (hkLt :
      k < Collatz2.Word.oddSteps
        (exponentWordOfParity (criticalBoundaryWord v.length))) :
    Collatz2.Word.extraDepth
        (exponentWordOfParity (criticalBoundaryWord v.length)) k = 0 := by
  by_cases hk0 : k = 0
  · subst k
    simp [
      Collatz2.Word.extraDepth,
      Collatz2.Word.prefixTwoDepth,
      Collatz2.Word.criticalHeight
    ]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hCheckpoint :=
      criticalBoundaryWord_prefixTwoDepth_eq_beattyIndex hFP hLen hkLt
    have hBeatty := beattyIndex_eq_wordCriticalHeight hkPos
    unfold Collatz2.Word.extraDepth
    rw [hCheckpoint, hBeatty]
    simp

/-- endpoint-style alias。 -/
theorem criticalBoundaryWord_parityExtraDepth_eq_zero
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k : ℕ}
    (hkLt :
      k < Collatz2.Word.oddSteps
        (exponentWordOfParity (criticalBoundaryWord v.length))) :
    parityExtraDepth (criticalBoundaryWord v.length) k = 0 := by
  exact criticalBoundaryWord_extraDepth_eq_zero hFP hLen hkLt

end CSTMicro
end Collatz2
