import CollatzLean.CollatzSecondLayer3.SpecialC3IntervalSubsequence
import CollatzLean.CollatzSecondLayer3.SpecialC3TransportedCollision
import CollatzLean.CollatzSecondLayer3.ContractingWindowBounds
import CollatzLean.CollatzFirstLayer.SignedCommonWordDivisibility
import CollatzLean.CollatzFirstLayer.NegativeShadowAlignment

/-!
# Constant terminal Special C3のnested alignment

terminal timeがcofinalに一定となる枝では、全Special C3 seedのactual startが同じで、
lengthだけが狭義増加する。したがってseed wordは同一軌道上のnested prefix列になる。

この固定start構造から、連続二seedについて

* 長いword = 短いword ++ 非空suffix
* center差 = `2^(H+1) * odd`
* 短いwordで輸送後の差 = `2 * odd`
* canonical startは固定値そのもの
* endpointには固定係数discounted bound

を得る。
-/


namespace CollatzCore.SpecialC3At

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- Special C3 predecessor shadowのmagnitudeは奇数。 -/
theorem shadowMagnitude_odd
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    Odd S.shadowMagnitude := by
  rcases O.value_odd (start + length) with ⟨a, ha⟩
  have hlt := S.endpoint_lt_two_mul_threePow
  have haLt : a < 3 ^ length := by
    rw [ha] at hlt
    omega
  refine ⟨3 ^ length - a - 1, ?_⟩
  unfold shadowMagnitude
  rw [ha]
  omega

end CollatzCore.SpecialC3At

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/-- Constant terminal枝を、nested解析用の正対象として束ねる。 -/
structure ConstantTerminalNestedAlignmentData
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) where
  terminal : ConstantNatSubsequenceData R.terminalTime

namespace ConstantTerminalNestedAlignmentData

/-- Constant terminal部分列からnested alignment dataを構成する。 -/
def ofConstant
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : ConstantNatSubsequenceData R.terminalTime) :
    ConstantTerminalNestedAlignmentData R :=
  ⟨S⟩

/-- nested列の元tower添字。 -/
def selectedIndex
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  D.terminal.select n

/-- 全seedに共通するactual start。 -/
def fixedStart
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) : ℕ :=
  R.anchor + D.terminal.value

/-- nested列のn番目のseed長。 -/
def selectedLength
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  R.length (D.selectedIndex n)

/-- nested列のn番目のseed word。 -/
def selectedWord
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ExpWord :=
  R.word (D.selectedIndex n)

/-- nested列のn番目のnegative center。 -/
def selectedCenter
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℤ :=
  R.center (D.selectedIndex n)

/-- 全selected seedのactual startは`fixedStart`に一致する。 -/
theorem selectedStart_eq_fixedStart
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    R.start (D.selectedIndex n) = D.fixedStart := by
  exact R.start_eq_on_constantTerminalSubsequence D.terminal n

/-- nested列のlengthは狭義増加する。 -/
theorem selectedLength_strict
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) :
    StrictMono D.selectedLength := by
  change StrictMono
    (fun n => R.length (D.terminal.select n))
  exact
    R.length_strict_on_constantTerminalSubsequence
      D.terminal

/-- 連続二seedのlength差。 -/
def suffixLength
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  D.selectedLength (n + 1) - D.selectedLength n

/-- 短いseed終端から長いseed終端までのactual suffix word。 -/
def suffixWord
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ExpWord :=
  O.segmentWord
    (D.fixedStart + D.selectedLength n)
    (D.suffixLength n)

/-- 連続二seed間のsuffix長は正。 -/
theorem suffixLength_pos
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    0 < D.suffixLength n := by
  have h :
      D.selectedLength n <
        D.selectedLength (n + 1) := by
    simpa using
      D.selectedLength_strict (Nat.lt_succ_self n)
  unfold suffixLength
  exact Nat.sub_pos_of_lt h

/-- nested seed wordを共通fixed startから直接書く。 -/
theorem selectedWord_eq_segmentWord_fixedStart
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.selectedWord n =
      O.segmentWord D.fixedStart (D.selectedLength n) := by
  unfold selectedWord FutureMinimumSpecialC3TowerData.word
  rw [D.selectedStart_eq_fixedStart n]
  rfl

/-- 長いseed wordは短いseed wordと非空suffixの連結。 -/
theorem selectedWord_succ_eq_append_suffix
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.selectedWord (n + 1) =
      D.selectedWord n ++ D.suffixWord n := by
  have hlt := D.selectedLength_strict (Nat.lt_succ_self n)
  have hlt :
      D.selectedLength n <
        D.selectedLength (n + 1) := by
    simpa using
      D.selectedLength_strict (Nat.lt_succ_self n)
  have hlen :
      D.selectedLength (n + 1) =
        D.selectedLength n + D.suffixLength n := by
    have hle :
        D.selectedLength n ≤
          D.selectedLength (n + 1) :=
      Nat.le_of_lt hlt
    have hsub :
        D.selectedLength (n + 1) - D.selectedLength n +
            D.selectedLength n =
          D.selectedLength (n + 1) :=
      Nat.sub_add_cancel hle
    unfold suffixLength
    calc
      D.selectedLength (n + 1)
          =
        (D.selectedLength (n + 1) - D.selectedLength n) +
          D.selectedLength n := hsub.symm
      _ =
        D.selectedLength n +
          (D.selectedLength (n + 1) - D.selectedLength n) := by
            exact Nat.add_comm _ _
  rw [D.selectedWord_eq_segmentWord_fixedStart (n + 1)]
  rw [D.selectedWord_eq_segmentWord_fixedStart n]
  unfold suffixWord
  rw [hlen]
  exact O.segmentWord_add D.fixedStart (D.selectedLength n) (D.suffixLength n)

/--
`nestedWord_prefix`:
長いSpecial C3 wordの先頭を短いlengthだけ取ると短いwordそのものになる。
-/
theorem nestedWord_prefix
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    (D.selectedWord (n + 1)).take (D.selectedLength n) =
      D.selectedWord n := by
  rw [D.selectedWord_eq_segmentWord_fixedStart (n + 1)]
  rw [D.selectedWord_eq_segmentWord_fixedStart n]
  exact
    O.segmentWord_take_of_le
      (Nat.le_of_lt (D.selectedLength_strict (Nat.lt_succ_self n)))

/-- suffix wordはactual orbitから得られるvalidな正指数語。 -/
theorem suffixWord_valid
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Valid (D.suffixWord n) := by
  unfold suffixWord
  exact
    (O.runs_segment
      (D.fixedStart + D.selectedLength n)
      (D.suffixLength n)).valid

/-- suffix wordは非空。 -/
theorem suffixWord_ne_nil
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.suffixWord n ≠ [] := by
  intro hNil
  have hLength := congrArg List.length hNil
  have hPos := D.suffixLength_pos n
  simp [suffixWord] at hLength
  omega

/-- suffixが消費する総2進depthは正。 -/
theorem suffixTwoSteps_pos
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    0 < twoSteps (D.suffixWord n) := by
  exact
    twoSteps_pos_of_valid_nonempty
      (D.suffixWord_valid n)
      (D.suffixWord_ne_nil n)

/-- 長いwordの総2進depthは短いwordとsuffixの和。 -/
theorem selectedWord_twoSteps_succ
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    twoSteps (D.selectedWord (n + 1)) =
      twoSteps (D.selectedWord n) + twoSteps (D.suffixWord n) := by
  rw [D.selectedWord_succ_eq_append_suffix n]
  rw [twoSteps_append]

/-- center差に現れる自然数odd kernel。 -/
def centerKernel
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  2 ^ twoSteps (D.suffixWord n) - 1

/-- 正の2冪から1を引いたcenter kernelは奇数。 -/
theorem centerKernel_odd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Odd (D.centerKernel n) := by
  have hPos := D.suffixTwoSteps_pos n
  obtain ⟨r, hr⟩ :
      ∃ r : ℕ, twoSteps (D.suffixWord n) = r + 1 :=
    ⟨twoSteps (D.suffixWord n) - 1, by omega⟩
  have hpowPos : 0 < 2 ^ r := Nat.pow_pos (by omega)
  refine ⟨2 ^ r - 1, ?_⟩
  unfold centerKernel
  rw [hr, pow_succ]
  omega

/-- center kernelの整数cast。 -/
theorem centerKernel_intCast
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    (D.centerKernel n : ℤ) =
      (2 : ℤ) ^ twoSteps (D.suffixWord n) - 1 := by
  unfold centerKernel
  have hOne : 1 ≤ 2 ^ twoSteps (D.suffixWord n) := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.pow_pos (by omega)))
  rw [Nat.cast_sub hOne]
  push_cast
  rfl

/--
`centerDifference_exact`:
同じfixed startを持つ連続二seedのcenter差は、
短いwordのresidue depth `H+1` と奇数kernelへexact分解される。
-/
theorem centerDifference_exact
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.selectedCenter n - D.selectedCenter (n + 1) =
      (2 : ℤ) ^ (twoSteps (D.selectedWord n) + 1) *
        (D.centerKernel n : ℤ) := by
  have hShort0 := R.center_eq_actual_sub_twoPow (D.selectedIndex n)
  have hLong0 := R.center_eq_actual_sub_twoPow (D.selectedIndex (n + 1))
  have hShort :
      D.selectedCenter n =
        (O.value D.fixedStart : ℤ) -
          (2 : ℤ) ^ (twoSteps (D.selectedWord n) + 1) := by
    rw [D.selectedStart_eq_fixedStart n] at hShort0
    simpa [selectedCenter, selectedWord, selectedIndex] using hShort0
  have hLong :
      D.selectedCenter (n + 1) =
        (O.value D.fixedStart : ℤ) -
          (2 : ℤ) ^ (twoSteps (D.selectedWord (n + 1)) + 1) := by
    rw [D.selectedStart_eq_fixedStart (n + 1)] at hLong0
    simpa [selectedCenter, selectedWord, selectedIndex] using hLong0
  have hSplit := D.selectedWord_twoSteps_succ n
  have hKernel := D.centerKernel_intCast n
  rw [hShort, hLong, hSplit, hKernel]
  rw [show
    twoSteps (D.selectedWord n) +
          twoSteps (D.suffixWord n) + 1 =
      (twoSteps (D.selectedWord n) + 1) +
        twoSteps (D.suffixWord n) by omega]
  rw [pow_add]
  ring

/-- fixed startは各nested wordのcanonical startそのもの。 -/
theorem fixedStart_canonicalEq
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    canonicalStart (D.selectedWord n) = O.value D.fixedStart := by
  have h := (R.special (D.selectedIndex n)).canonicalStart_eq
  have h' :
      O.value (R.start (D.selectedIndex n)) =
        canonicalStart (R.word (D.selectedIndex n)) := by
    simpa [
      FutureMinimumSpecialC3TowerData.word,
      FutureMinimumSpecialC3TowerData.start,
      FutureMinimumSpecialC3TowerData.length,
      FutureMinimumSpecialC3TowerData.terminalTime
    ] using h
  rw [D.selectedStart_eq_fixedStart n] at h'
  simpa [selectedWord, selectedIndex] using h'.symm

/--
`fixedStart_canonicalBound`:
Constant枝ではcanonical residueは多項式小より強く、固定定数で一様に抑えられる。
-/
theorem fixedStart_canonicalBound
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    canonicalStart (D.selectedWord n) ≤ O.value D.fixedStart := by
  rw [D.fixedStart_canonicalEq n]

/--
`fixedStart_discountedBound`:
固定startからの一般odd-only成長評価により、各endpointは固定係数のdiscounted boundを持つ。
-/
theorem fixedStart_discountedBound
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    2 ^ D.selectedLength n *
        O.value (D.fixedStart + D.selectedLength n) ≤
      3 ^ D.selectedLength n * (O.value D.fixedStart + 1) := by
  have h :=
    OddOrbit.twoPow_mul_value_add_one_le_threePow
      O D.fixedStart (D.selectedLength n)
  calc
    2 ^ D.selectedLength n *
        O.value (D.fixedStart + D.selectedLength n)
        ≤
      2 ^ D.selectedLength n *
        (O.value (D.fixedStart + D.selectedLength n) + 1) := by
          exact Nat.mul_le_mul_left _ (Nat.le_succ _)
    _ ≤ 3 ^ D.selectedLength n * (O.value D.fixedStart + 1) := h

/-- 短いseedのpredecessor shadow magnitude。 -/
def shortMagnitude
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  (R.special (D.selectedIndex n)).shadowMagnitude

/-- 共通短word輸送後の差のodd kernel。 -/
def finishKernel
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  3 ^ oddSteps (D.selectedWord n) * D.centerKernel n

/-- finish側kernelは奇数。 -/
theorem finishKernel_odd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Odd (D.finishKernel n) := by
  unfold finishKernel
  exact
    ((show Odd (3 : ℕ) by decide).pow).mul (D.centerKernel_odd n)

/-- 長いcenterを短いwordだけ輸送したsigned終点。 -/
def transportedFinishFromLong
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℤ :=
  predecessorShadow (D.selectedWord n) -
    2 * (3 : ℤ) ^ oddSteps (D.selectedWord n) *
      (D.centerKernel n : ℤ)

/-- 長いcenterは短いwordを`transportedFinishFromLong`までsigned実現する。 -/
theorem transportedFinishFromLong_realizesInt
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    RealizesInt
      (D.selectedWord n)
      (D.selectedCenter (n + 1))
      (D.transportedFinishFromLong n) := by
  have hReplay :=
    realizesInt_sub_replay
      (predecessorShadow_realizes (D.selectedWord n))
      (D.centerKernel n : ℤ)
  have hCenter := D.centerDifference_exact n
  have hMod := residueModulus_int_cast (D.selectedWord n)
  have hStart :
      D.selectedCenter (n + 1) =
        predecessorStart (D.selectedWord n) -
          (residueModulus (D.selectedWord n) : ℤ) *
            (D.centerKernel n : ℤ) := by
    rw [hMod]
    have hShortCenter :
        D.selectedCenter n = predecessorStart (D.selectedWord n) := by
      rfl
    rw [← hShortCenter]
    omega
  rw [hStart]
  simpa [transportedFinishFromLong] using hReplay

/--
`transportedFinishDifference_exact_one_bit`:
短いpredecessor shadowと長いcenterの短word輸送終点の差はexactに`2 * odd`。
-/
theorem transportedFinishDifference_exact_one_bit
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    predecessorShadow (D.selectedWord n) -
          D.transportedFinishFromLong n =
        2 * (D.finishKernel n : ℤ) ∧
      Odd (D.finishKernel n) := by
  constructor
  · unfold transportedFinishFromLong finishKernel
    push_cast
    ring
  · exact D.finishKernel_odd n

/-- 長い輸送状態の正のmagnitude。 -/
def longTransportMagnitude
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  D.shortMagnitude n + 2 * D.finishKernel n

/-- 長い輸送magnitudeは正。 -/
theorem longTransportMagnitude_pos
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    0 < D.longTransportMagnitude n := by
  have hPos := (R.special (D.selectedIndex n)).shadowMagnitude_pos
  unfold longTransportMagnitude shortMagnitude
  omega

/-- 短いseedのpredecessor shadow magnitudeは奇数。 -/
theorem shortMagnitude_odd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Odd (D.shortMagnitude n) := by
  exact (R.special (D.selectedIndex n)).shadowMagnitude_odd

/-- 長い輸送magnitudeは奇数。 -/
theorem longTransportMagnitude_odd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Odd (D.longTransportMagnitude n) := by
  rcases D.shortMagnitude_odd n with ⟨a, ha⟩
  refine ⟨a + D.finishKernel n, ?_⟩
  unfold longTransportMagnitude
  rw [ha]
  ring

/-- 長い輸送signed終点は上記magnitudeの負値。 -/
theorem transportedFinishFromLong_eq_neg_magnitude
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.transportedFinishFromLong n =
      -(D.longTransportMagnitude n : ℤ) := by
  have hShadow :=
    (R.special (D.selectedIndex n)).predecessorShadow_eq_neg_shadowMagnitude
  change
    predecessorShadow (D.selectedWord n) =
      -((R.special (D.selectedIndex n)).shadowMagnitude : ℤ)
    at hShadow
  unfold transportedFinishFromLong
    longTransportMagnitude
    shortMagnitude
    finishKernel
  rw [hShadow]
  push_cast
  ring

/-- finish地点の二magnitudeはdepth 1まで方向付きalignmentを持つ。 -/
theorem finishMagnitude_orderedAlignment_one
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    OrderedMagnitudeAlignedToDepth
      (D.shortMagnitude n)
      (D.longTransportMagnitude n)
      1 := by
  refine ⟨D.finishKernel n, ?_⟩
  unfold longTransportMagnitude
  norm_num

/--
任意の狭義増加再選択後もConstant terminal nested構造を保つ。
carry pattern固定部分列へ移るためのAPI。
-/
def refine
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (select : ℕ → ℕ)
    (hselect : StrictMono select) :
    ConstantTerminalNestedAlignmentData R where
  terminal :=
    { value := D.terminal.value
      select := fun n => D.terminal.select (select n)
      select_strict := D.terminal.select_strict.comp hselect
      value_eq := fun n => D.terminal.value_eq (select n) }

end ConstantTerminalNestedAlignmentData
end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
