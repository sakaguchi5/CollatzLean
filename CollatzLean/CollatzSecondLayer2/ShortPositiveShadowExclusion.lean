import CollatzLean.CollatzSecondLayer2.FirstCriticalTerminalRefinement

/-!
# short positive-shadow terminalの排除

自然数上のactual runをcanonical replay幅だけ整数方向へ一段下げる。
開始値が負なら各odd-only stepは負値を負値へ送るため、終点側の
predecessor shadowも必ず負になる。

したがって、canonical terminalでpredecessor shadowが正になる
short positive-shadow枝は存在しない。
-/

namespace CollatzFirstLayer
namespace ExpWord
namespace Runs

/--
actual runを整数方向へ`k`段下げたとき、下げた開始値が負なら
対応する下げた終点も負である。

中間値を明示的な型として保存せず、自然数runに沿った帰納で符号だけを輸送する。
-/
theorem signedReplay_finish_neg
    {w : ExpWord} {X Y : ℕ}
    (h : Runs w X Y)
    (k : ℤ)
    (hk : 0 < k)
    (hstart :
      (X : ℤ) - (residueModulus w : ℤ) * k < 0) :
    (Y : ℤ) -
        2 * (3 : ℤ) ^ oddSteps w * k < 0 := by
  induction h generalizing k with
  | nil x =>
      simpa [residueModulus, twoSteps, oddSteps] using hstart
  | @cons e w x y z he hstep hy htail ih =>
      have hstepZ :
          (2 : ℤ) ^ e * (y : ℤ) =
            3 * (x : ℤ) + 1 := by
        exact_mod_cast hstep
      have hmodulus :
          (residueModulus (e :: w) : ℤ) =
            (2 : ℤ) ^ e * (residueModulus w : ℤ) := by
        exact_mod_cast (residueModulus_cons_eq e w)
      have hshiftedStep :
          (2 : ℤ) ^ e *
              ((y : ℤ) - (residueModulus w : ℤ) * (3 * k)) =
            3 *
                ((x : ℤ) -
                  (residueModulus (e :: w) : ℤ) * k) +
              1 := by
        calc
          (2 : ℤ) ^ e *
                ((y : ℤ) - (residueModulus w : ℤ) * (3 * k))
              =
            (2 : ℤ) ^ e * (y : ℤ) -
              3 *
                ((2 : ℤ) ^ e *
                  (residueModulus w : ℤ) * k) := by
                    ring
          _ =
            (3 * (x : ℤ) + 1) -
              3 *
                ((2 : ℤ) ^ e *
                  (residueModulus w : ℤ) * k) := by
                    rw [hstepZ]
          _ =
            3 *
                ((x : ℤ) -
                  (residueModulus (e :: w) : ℤ) * k) +
              1 := by
                    rw [hmodulus]
                    ring
      have hshiftedStart_le :
          (x : ℤ) -
              (residueModulus (e :: w) : ℤ) * k ≤ -1 := by
        omega
      have hrightNeg :
          3 *
                ((x : ℤ) -
                  (residueModulus (e :: w) : ℤ) * k) +
              1 < 0 := by
        omega
      have hproductNeg :
          (2 : ℤ) ^ e *
              ((y : ℤ) - (residueModulus w : ℤ) * (3 * k)) < 0 := by
        rw [hshiftedStep]
        exact hrightNeg
      have hpowPos : 0 < (2 : ℤ) ^ e := by
        positivity
      have hmiddleNeg :
          (y : ℤ) - (residueModulus w : ℤ) * (3 * k) < 0 := by
        by_contra hnot
        have hmiddleNonneg :
            0 ≤ (y : ℤ) - (residueModulus w : ℤ) * (3 * k) :=
          le_of_not_gt hnot
        have hproductNonneg :
            0 ≤ (2 : ℤ) ^ e *
              ((y : ℤ) - (residueModulus w : ℤ) * (3 * k)) :=
          mul_nonneg hpowPos.le hmiddleNonneg
        exact (not_lt_of_ge hproductNonneg) hproductNeg
      have hkTail : 0 < 3 * k := by
        nlinarith
      have htailNeg := ih (3 * k) hkTail hmiddleNeg
      have hwidth :
          2 * (3 : ℤ) ^ oddSteps (e :: w) * k =
            2 * (3 : ℤ) ^ oddSteps w * (3 * k) := by
        simp only [oddSteps_cons, pow_succ]
        ring
      rw [hwidth]
      exact htailNeg

/--
canonical開始値からcanonical終点へactualに走れる語では、
一段下のpredecessor shadowは必ず負。
-/
theorem predecessorShadow_neg_of_canonical_run
    {w : ExpWord}
    (h : Runs w (canonicalStart w) (canonicalEnd w)) :
    predecessorShadow w < 0 := by
  have hstart :
      (canonicalStart w : ℤ) -
          (residueModulus w : ℤ) * (1 : ℤ) < 0 := by
    simpa [predecessorStart] using predecessorStart_neg w
  have hfinish :=
    signedReplay_finish_neg h (1 : ℤ) (by norm_num) hstart
  simpa [predecessorShadow] using hfinish

end Runs
end ExpWord
end CollatzFirstLayer

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FirstCriticalTransitionTowerData

/-- short positive-shadow terminalはsigned replayの符号保存に反する。 -/
theorem shortPositiveShadowTerminalAt_impossible
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (S : ShortPositiveShadowTerminalAt R j) :
    False := by
  let P := R.terminalPacket j
  let C := P.replayCoordinate
  have hq0 : C.quotient = 0 := by
    simpa [C, P, terminalReplayQuotient] using S.canonicalBoundary
  have hstart :
      O.value (R.terminalStart j) =
        canonicalStart (R.terminalWord j) := by
    simpa [C, P, terminalWord] using
      C.start_eq_canonical_of_quotient_eq_zero hq0
  have hend :
      O.value (R.terminalStart j + R.windowLength j) =
        canonicalEnd (R.terminalWord j) := by
    have h := C.finish_eq
    rw [hq0] at h
    simpa [terminalWord] using h
  have hrun0 := P.run
  rw [hstart, hend] at hrun0
  have hrun :
      Runs
        (R.terminalWord j)
        (canonicalStart (R.terminalWord j))
        (canonicalEnd (R.terminalWord j)) := by
    simpa [terminalWord] using hrun0
  have hneg : predecessorShadow (R.terminalWord j) < 0 :=
    Runs.predecessorShadow_neg_of_canonical_run hrun
  have hpos : 0 < predecessorShadow (R.terminalWord j) := by
    simpa [terminalPredecessorShadow] using S.positiveShadow
  omega

/-- q>=5の局所三分岐からpositive-shadow枝を除いた局所二分岐。 -/
theorem terminal_dichotomy_at
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (hq : 5 ≤ R.windowLength j) :
    Nonempty (DeepLowerReplayTerminalAt R j) ∨
      R.TerminalSpecialC3At j := by
  rcases R.terminal_trichotomy_at j hq with hDeep | hPositive | hSpecial
  · exact Or.inl hDeep
  · exact False.elim
      (R.shortPositiveShadowTerminalAt_impossible
        j (Classical.choice hPositive))
  · exact Or.inr hSpecial

end FirstCriticalTransitionTowerData

/-- short positive-shadow terminal towerは存在しない。 -/
theorem shortPositiveShadowTerminalTower_impossible
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : ShortPositiveShadowTerminalTowerData hGap O) :
    False :=
  T.source.shortPositiveShadowTerminalAt_impossible
    (T.select 0) (T.shortPositive 0)

/-- first-critical towerの最終二分岐。 -/
theorem firstCriticalTerminal_dichotomy
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (DeepLowerReplayTerminalTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  rcases firstCriticalTerminal_classification R with
    hDeep | hPositive | hSpecial
  · exact Or.inl hDeep
  · exact False.elim
      (shortPositiveShadowTerminalTower_impossible
        (Classical.choice hPositive))
  · exact Or.inr hSpecial

/-- short positive-shadowを除いたfirst-critical terminal outcome。 -/
inductive FirstCriticalReducedTerminalOutcomeTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) : Type
  | deepLowerReplay
      (data : DeepLowerReplayTerminalTowerData hGap O)
  | terminalSpecialC3
      (data : TerminalSpecialC3TransitionTowerData hGap O)

/-- reduced terminal outcomeを一つ選べる。 -/
theorem firstCriticalReducedTerminal_outcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (FirstCriticalReducedTerminalOutcomeTowerData hGap O) := by
  rcases firstCriticalTerminal_dichotomy R with hDeep | hSpecial
  · exact ⟨.deepLowerReplay (Classical.choice hDeep)⟩
  · exact ⟨.terminalSpecialC3 (Classical.choice hSpecial)⟩

end CollatzSecondLayer2
