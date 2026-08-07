import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalFirstCarry
import CollatzLean.CollatzFirstLayer.SignedReplay

/-!
# Constant terminal nested pairのsuffix輸送

Constant terminalでは長いSpecial C3 wordが短いwordへactual suffixをappendした形になる。
短いword終端で得た長いnegative transport magnitudeは、suffix開始のactual正値と
`2^(suffixTwoSteps+1) * 3^shortLength`だけ離れている。

この深いmixed-sign alignmentと一段の完全2進分解一意性から、長い輸送状態の
最初のnegative-shadow指数はactual suffix先頭指数にexactに一致する。
さらにsigned replayをsuffix全体へ適用し、長い輸送状態が同じsuffix wordを
長いSpecial C3 predecessor shadowまで実現することを示す。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData
namespace ConstantTerminalNestedAlignmentData

/-- nested列のn番目のendpoint位置。 -/
def endpointPosition
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  D.fixedStart + D.selectedLength n

/-- nested列のn番目のendpoint値。 -/
def endpointValue
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  O.value (D.endpointPosition n)

/-- nested列のn番目のendpointから出るactual指数。 -/
def endpointExponent
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  O.exponent (D.endpointPosition n)

/-- 連続二seedのlengthは短長とsuffix長の和。 -/
theorem selectedLength_succ_eq_add_suffix
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.selectedLength (n + 1) =
      D.selectedLength n + D.suffixLength n := by
  have hle :
      D.selectedLength n ≤ D.selectedLength (n + 1) :=
    Nat.le_of_lt (D.selectedLength_strict (Nat.lt_succ_self n))
  unfold suffixLength
  omega

/-- suffix開始位置は短いseed endpoint位置。 -/
theorem suffixStart_eq_endpointPosition
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.fixedStart + D.selectedLength n = D.endpointPosition n :=
  rfl

/-- suffix終端位置は長いseed endpoint位置。 -/
theorem suffixEnd_eq_nextEndpointPosition
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.endpointPosition n + D.suffixLength n =
      D.endpointPosition (n + 1) := by
  unfold endpointPosition
  rw [D.selectedLength_succ_eq_add_suffix n]
  omega

/-- 短いshadow magnitudeとactual endpointの和は`2*3^q`。 -/
theorem shortMagnitude_add_endpointValue
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.shortMagnitude n + D.endpointValue n =
      2 * 3 ^ D.selectedLength n := by
  let j := D.selectedIndex n
  have hStart :
      R.start j = D.fixedStart := by
    simpa [j] using
      D.selectedStart_eq_fixedStart n
  have hlt :=
    (R.special j).endpoint_lt_two_mul_threePow
  change
    O.value (R.start j + R.length j) <
      2 * 3 ^ R.length j
    at hlt
  have hltFixed :
      O.value (D.fixedStart + R.length j) <
        2 * 3 ^ R.length j := by
    simpa [hStart] using hlt
  unfold shortMagnitude
    SpecialC3At.shadowMagnitude
    endpointValue
    endpointPosition
  change
    2 * 3 ^ R.length j -
          O.value (R.start j + R.length j) +
        O.value (D.fixedStart + R.length j) =
      2 * 3 ^ R.length j
  rw [hStart]
  exact Nat.sub_add_cancel (Nat.le_of_lt hltFixed)

/-- center kernelへ1を戻すとsuffixの純粋2冪になる。 -/
theorem centerKernel_add_one
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.centerKernel n + 1 = 2 ^ twoSteps (D.suffixWord n) := by
  unfold centerKernel
  have hOne : 1 ≤ 2 ^ twoSteps (D.suffixWord n) := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.pow_pos (by omega)))
  omega

/-- 短いselected wordのodd step数はselected length。 -/
theorem selectedWord_oddSteps_eq_length
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    oddSteps (D.selectedWord n) = D.selectedLength n := by
  change
    oddSteps (R.word (D.terminal.select n)) =
      R.length (D.terminal.select n)
  unfold word length
  simp [oddSteps]

/--
actual endpointと長い輸送magnitudeの和は、suffix residue modulusに
`3^shortLength`を掛けたexact alignment量。
-/
theorem endpoint_add_longTransportMagnitude_exact
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.endpointValue n + D.longTransportMagnitude n =
      2 ^ (twoSteps (D.suffixWord n) + 1) *
        3 ^ D.selectedLength n := by
  have hShort := D.shortMagnitude_add_endpointValue n
  have hKernel := D.centerKernel_add_one n
  have hOdd := D.selectedWord_oddSteps_eq_length n
  unfold longTransportMagnitude finishKernel
  rw [hOdd]
  calc
    D.endpointValue n +
        (D.shortMagnitude n +
          2 * (3 ^ D.selectedLength n * D.centerKernel n))
        =
      (D.shortMagnitude n + D.endpointValue n) +
        2 * (3 ^ D.selectedLength n * D.centerKernel n) := by ring
    _ =
      2 * 3 ^ D.selectedLength n +
        2 * (3 ^ D.selectedLength n * D.centerKernel n) := by
          rw [hShort]
    _ =
      2 * 3 ^ D.selectedLength n * (D.centerKernel n + 1) := by
          ring
    _ =
      2 * 3 ^ D.selectedLength n *
        2 ^ twoSteps (D.suffixWord n) := by
          rw [hKernel]
    _ =
      2 ^ (twoSteps (D.suffixWord n) + 1) *
        3 ^ D.selectedLength n := by
          rw [pow_succ]
          ring

/-- suffix先頭actual指数はsuffix総2進depth以下。 -/
theorem endpointExponent_le_suffixTwoSteps
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.endpointExponent n ≤ twoSteps (D.suffixWord n) := by
  obtain ⟨m, hm⟩ :
      ∃ m : ℕ, D.suffixLength n = m + 1 := by
    exact ⟨D.suffixLength n - 1, by
      have hpos := D.suffixLength_pos n
      omega⟩
  unfold endpointExponent suffixWord
  rw [hm]
  rw [OddOrbit.segmentWord_succ]
  rw [twoSteps_cons]
  exact Nat.le_add_right _ _

/-- suffix先頭actual指数にはalignment depth `H+1`に対する余裕がある。 -/
theorem endpointExponent_lt_suffixAlignmentDepth
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.endpointExponent n < twoSteps (D.suffixWord n) + 1 := by
  exact Nat.lt_succ_of_le (D.endpointExponent_le_suffixTwoSteps n)

/--
正のactual状態`a`と負のmagnitude`b`が深さ`M`でexactに向かい合い、
両者の次stepが奇数部分を持つとする。actual側指数`e`が`M`未満なら、
negative側指数`f`はexactに`e`へ一致する。
-/
private theorem positiveNegativeStep_exponent_eq_of_exact_alignment
    {a b a' b' e f M k : ℕ}
    (haOdd : Odd a')
    (hbOdd : Odd b')
    (hkOdd : Odd k)
    (hA : 2 ^ e * a' = 3 * a + 1)
    (hB : 2 ^ f * b' + 1 = 3 * b)
    (hAlign : a + b = 2 ^ M * k)
    (heM : e < M) :
    e = f := by
  have hsumPlus :
      2 ^ e * a' + 2 ^ f * b' + 1 = 3 * (a + b) + 1 := by
    calc
      2 ^ e * a' + 2 ^ f * b' + 1
          = 2 ^ e * a' + (2 ^ f * b' + 1) := by ring
      _ = (3 * a + 1) + 3 * b := by rw [hA, hB]
      _ = 3 * (a + b) + 1 := by ring
  have hsum :
      2 ^ e * a' + 2 ^ f * b' = 3 * (a + b) := by
    omega
  rcases lt_trichotomy e f with hef | hef | hfe
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, f = e + r :=
      ⟨f - e, by omega⟩
    have hrPos : 0 < r := by omega
    have hCandidateOdd : Odd (a' + 2 ^ r * b') := by
      rcases haOdd with ⟨u, hu⟩
      obtain ⟨r0, hr0⟩ : ∃ r0 : ℕ, r = r0 + 1 :=
        ⟨r - 1, by omega⟩
      refine ⟨u + 2 ^ r0 * b', ?_⟩
      rw [hu, hr0, pow_succ]
      ring
    have hCandidateEq :
        3 * (a + b) = 2 ^ e * (a' + 2 ^ r * b') := by
      rw [← hsum, hr, pow_add]
      ring
    have hCandidate :
        ExactTwoFactor (3 * (a + b)) e (a' + 2 ^ r * b') :=
      ⟨hCandidateEq, hCandidateOdd⟩
    have hDeep :
        ExactTwoFactor (3 * (a + b)) M (3 * k) := by
      refine ⟨?_, (show Odd (3 : ℕ) by decide).mul hkOdd⟩
      rw [hAlign]
      ring
    have hEq := exactTwoFactor_exponent_unique hCandidate hDeep
    omega
  · exact hef
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, e = f + r :=
      ⟨e - f, by omega⟩
    have hrPos : 0 < r := by omega
    have hCandidateOdd : Odd (2 ^ r * a' + b') := by
      rcases hbOdd with ⟨u, hu⟩
      obtain ⟨r0, hr0⟩ : ∃ r0 : ℕ, r = r0 + 1 :=
        ⟨r - 1, by omega⟩
      refine ⟨2 ^ r0 * a' + u, ?_⟩
      rw [hu, hr0, pow_succ]
      ring
    have hCandidateEq :
        3 * (a + b) = 2 ^ f * (2 ^ r * a' + b') := by
      rw [← hsum, hr, pow_add]
      ring
    have hCandidate :
        ExactTwoFactor (3 * (a + b)) f (2 ^ r * a' + b') :=
      ⟨hCandidateEq, hCandidateOdd⟩
    have hDeep :
        ExactTwoFactor (3 * (a + b)) M (3 * k) := by
      refine ⟨?_, (show Odd (3 : ℕ) by decide).mul hkOdd⟩
      rw [hAlign]
      ring
    have hEq := exactTwoFactor_exponent_unique hCandidate hDeep
    omega

/--
`longTransportExponent_eq_actualSuffixExponent`:
長いcenterを短word終端まで輸送したnegative stateの次指数は、
actual suffix先頭指数にexactに一致する。
-/
theorem longTransportExponent_eq_actualSuffixExponent
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.longTransportExponent n = D.endpointExponent n := by
  have hActual :
      2 ^ D.endpointExponent n *
          O.value (D.endpointPosition n + 1) =
        3 * D.endpointValue n + 1 := by
    simpa [endpointExponent, endpointPosition, endpointValue] using
      O.step (D.endpointPosition n)
  have hNegative := D.longTransportStep_equation n
  have hAlign := D.endpoint_add_longTransportMagnitude_exact n
  have hEq :=
    positiveNegativeStep_exponent_eq_of_exact_alignment
      (O.value_odd (D.endpointPosition n + 1))
      (D.longTransportNextMagnitude_odd n)
      (show Odd (3 ^ D.selectedLength n) by
        exact (show Odd (3 : ℕ) by decide).pow)
      hActual
      hNegative
      hAlign
      (D.endpointExponent_lt_suffixAlignmentDepth n)
  exact hEq.symm

/-- suffix actual run。 -/
theorem suffix_run
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Runs
      (D.suffixWord n)
      (D.endpointValue n)
      (D.endpointValue (n + 1)) := by
  have h := O.runs_segment (D.endpointPosition n) (D.suffixLength n)
  have hEnd := D.suffixEnd_eq_nextEndpointPosition n
  rw [hEnd] at h
  simpa [suffixWord, endpointPosition, endpointValue] using h

/-- long transportをsuffix全体へ通したsigned finish。 -/
def longTransportSuffixFinish
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℤ :=
  (D.endpointValue (n + 1) : ℤ) -
    2 * (3 : ℤ) ^ D.selectedLength (n + 1)

/--
`longTransport_follows_entire_suffix`:
長い輸送negative stateはactual suffixと同じsuffix wordを整数上で実現し、
長いseedの一段下shadowに対応するfinishまで到達する。
-/
theorem longTransport_follows_entire_suffix
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    RealizesInt
      (D.suffixWord n)
      (-(D.longTransportMagnitude n : ℤ))
      (D.longTransportSuffixFinish n) := by
  have hReplay :=
    realizesInt_sub_replay
      (D.suffix_run n).realizes.toInt
      ((3 : ℤ) ^ D.selectedLength n)
  have hAlign := D.endpoint_add_longTransportMagnitude_exact n
  have hMod :
      (residueModulus (D.suffixWord n) : ℤ) =
        (2 : ℤ) ^ (twoSteps (D.suffixWord n) + 1) :=
    residueModulus_int_cast (D.suffixWord n)
  have hStart :
      (D.endpointValue n : ℤ) -
          (residueModulus (D.suffixWord n) : ℤ) *
            (3 : ℤ) ^ D.selectedLength n =
        -(D.longTransportMagnitude n : ℤ) := by
    rw [hMod]
    have hAlignZ :
        (D.endpointValue n : ℤ) +
            (D.longTransportMagnitude n : ℤ) =
          (2 : ℤ) ^ (twoSteps (D.suffixWord n) + 1) *
            (3 : ℤ) ^ D.selectedLength n := by
      exact_mod_cast hAlign
    omega
  have hOddSuffix :
      oddSteps (D.suffixWord n) = D.suffixLength n := by
    simp [suffixWord, oddSteps]
  have hLen := D.selectedLength_succ_eq_add_suffix n
  have hFinish :
      (D.endpointValue (n + 1) : ℤ) -
          2 * (3 : ℤ) ^ oddSteps (D.suffixWord n) *
            (3 : ℤ) ^ D.selectedLength n =
        D.longTransportSuffixFinish n := by
    unfold longTransportSuffixFinish
    rw [hOddSuffix, hLen, pow_add]
    ring
  rw [hStart, hFinish] at hReplay
  exact hReplay

/-- suffix signed finishは長いselected wordのpredecessor shadowそのもの。 -/
theorem longTransportSuffixFinish_eq_longPredecessorShadow
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.longTransportSuffixFinish n =
      predecessorShadow (D.selectedWord (n + 1)) := by
  have hCanon := (R.special (D.selectedIndex (n + 1))).canonicalEnd_eq
  have hOdd := D.selectedWord_oddSteps_eq_length (n + 1)
  have hStart := D.selectedStart_eq_fixedStart (n + 1)
  unfold longTransportSuffixFinish predecessorShadow endpointValue endpointPosition
  rw [hOdd]
  have hCanon := (R.special (D.selectedIndex (n + 1))).canonicalEnd_eq
  have hOdd := D.selectedWord_oddSteps_eq_length (n + 1)
  have hStart := D.selectedStart_eq_fixedStart (n + 1)
  have hCanonBase :
      O.value
          (R.start (D.selectedIndex (n + 1)) +
            R.length (D.selectedIndex (n + 1))) =
        canonicalEnd
          (R.word (D.selectedIndex (n + 1))) := by
    change
      O.value
          (R.anchor +
            (R.normalization (D.selectedIndex (n + 1))).terminalTime +
            (R.select (D.selectedIndex (n + 1)) + 1)) =
        canonicalEnd
          (O.segmentWord
            (R.anchor +
              (R.normalization (D.selectedIndex (n + 1))).terminalTime)
            (R.select (D.selectedIndex (n + 1)) + 1))
    exact hCanon
  have hCanon' :
      O.value
          (D.fixedStart + D.selectedLength (n + 1)) =
        canonicalEnd (D.selectedWord (n + 1)) := by
    rw [← hStart]
    simpa [selectedWord, selectedLength] using hCanonBase
  rw [hCanon']

/-- long transportはsuffix全体を通って長いSpecial C3 predecessor shadowへ到達する。 -/
theorem longTransport_follows_entire_suffix_to_predecessorShadow
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    RealizesInt
      (D.suffixWord n)
      (-(D.longTransportMagnitude n : ℤ))
      (predecessorShadow (D.selectedWord (n + 1))) := by
  rw [← D.longTransportSuffixFinish_eq_longPredecessorShadow n]
  exact D.longTransport_follows_entire_suffix n

/-- fixed offsetでは十分大きなnested shiftがactual値を必ず上回る。 -/
theorem constantTerminal_eventually_ordered_at_fixedOffset
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (r : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      O.value (D.fixedStart + r) <
        O.value (D.fixedStart + D.selectedLength n + r) := by
  obtain ⟨N, hN⟩ :=
    O.escapesToInfinity_of_unbounded R.unbounded
      (O.value (D.fixedStart + r))
  refine ⟨N, ?_⟩
  intro n hn
  have hindex : n ≤ D.selectedLength n :=
    nat_le_strictMono_apply D.selectedLength D.selectedLength_strict n
  apply hN
  omega

end ConstantTerminalNestedAlignmentData
end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
