import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.FirstCrossing
import CollatzLean.Collatz.AdjacentReturn.StrongContractingTail
import CollatzLean.Collatz.AdjacentReturn.FullBlockCanonical
import CollatzLean.Collatz.AdjacentReturn.FirstCrossingBridge
import CollatzLean.Collatz.Selection.Cofinal

/-!
# contracting 側の純算術 chain

最終的に全 adjacent return が contracting になる tail から、
block の sharp 算術、valuation coherence、first-crossing 長の発散を
一つの整数列 package にまとめる。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/-- contracting adjacent block の純算術 package。 -/
structure ContractingBlockArithmetic where
  base : BlockArithmeticData
  contracting : base.word.Contracting
  allSuffixesContracting : base.word.AllSuffixesContracting
  contractingIdentity :
    base.affineConstant =
      (2 ^ base.totalExponent - 3 ^ base.length) * base.startValue +
        2 ^ base.totalExponent * base.valueGap
  twoPowGap_lt_affine :
    2 ^ base.totalExponent * base.valueGap < base.affineConstant
  twoPowLengthGap_lt_threePow :
    2 ^ base.length * base.valueGap < 3 ^ base.length
  threeAffine_lt_lengthTwoPow :
    3 * base.affineConstant <
      base.length * 2 ^ base.totalExponent
  threeGap_lt_length :
    3 * base.valueGap < base.length
  thirteen_le_length : 13 ≤ base.length
  corridor :
    2 * (base.startValue + base.valueGap + 1) <
      3 * (base.startValue + 1)

namespace ContractingBlockArithmetic

/-- actual contracting state から純算術 package を作る。 -/
def ofState
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    ContractingBlockArithmetic := by
  let B := BlockArithmeticData.ofState R
  refine {
    base := B
    contracting := ?_
    allSuffixesContracting := ?_
    contractingIdentity := ?_
    twoPowGap_lt_affine := ?_
    twoPowLengthGap_lt_threePow := ?_
    threeAffine_lt_lengthTwoPow := ?_
    threeGap_lt_length := ?_
    thirteen_le_length := ?_
    corridor := ?_
  }
  · change R.word.Contracting
    exact hC
  · change R.word.AllSuffixesContracting
    exact R.allSuffixesContracting hC
  · change
      R.affineConstant =
        (2 ^ R.totalExponent - 3 ^ R.length) * R.startValue +
          2 ^ R.totalExponent * R.valueGap
    simpa [State.contractingGap] using R.contractingIdentity hC
  · change 2 ^ R.totalExponent * R.valueGap < R.affineConstant
    exact R.twoPow_totalExponent_mul_valueGap_lt_affineConstant hC
  · change 2 ^ R.length * R.valueGap < 3 ^ R.length
    exact R.twoPow_length_mul_valueGap_lt_threePow hC
  · change 3 * R.affineConstant < R.length * 2 ^ R.totalExponent
    exact R.three_mul_affineConstant_lt_length_mul_twoPow hC
  · change 3 * R.valueGap < R.length
    exact R.three_mul_valueGap_lt_length hC
  · change 13 ≤ R.length
    have hgap : 4 ≤ R.valueGap := R.four_le_valueGap
    have hsharp := R.three_mul_valueGap_lt_length hC
    omega
  · change
      2 * (R.startValue + R.valueGap + 1) <
        3 * (R.startValue + 1)
    rw [← R.nextValue_eq_startValue_add_valueGap]
    exact R.two_mul_nextValue_add_one_lt_three_mul_startValue_add_one hC

end ContractingBlockArithmetic

/--
最終 contracting tail を軌道から切り離した連続整数 chain。
valuation triangle と first-crossing 長の発散も保持する。
-/
structure ContractingIntegerChain where
  block : ℕ → ContractingBlockArithmetic
  connects :
    ∀ n : ℕ,
      (block n).base.startValue + (block n).base.valueGap =
        (block (n + 1)).base.startValue
  startDepth : ℕ → ℕ
  startOddPart : ℕ → ℕ
  nextDepth : ℕ → ℕ
  nextOddPart : ℕ → ℕ
  gapDepth : ℕ → ℕ
  gapOddPart : ℕ → ℕ
  startFactor :
    ∀ n : ℕ,
      TwoAdic.ExactFactor
        ((block n).base.startValue + 1)
        (startDepth n) (startOddPart n)
  nextFactor :
    ∀ n : ℕ,
      TwoAdic.ExactFactor
        ((block n).base.startValue + (block n).base.valueGap + 1)
        (nextDepth n) (nextOddPart n)
  gapFactor :
    ∀ n : ℕ,
      TwoAdic.ExactFactor
        ((block n).base.valueGap)
        (gapDepth n) (gapOddPart n)
  depth_coherent :
    ∀ n : ℕ, nextDepth n = startDepth (n + 1)
  startDepth_two_le : ∀ n : ℕ, 2 ≤ startDepth n
  gapDepth_two_le : ∀ n : ℕ, 2 ≤ gapDepth n
  rise_gap_eq :
    ∀ n : ℕ,
      startDepth n < startDepth (n + 1) →
        gapDepth n = startDepth n
  fall_gap_eq :
    ∀ n : ℕ,
      startDepth (n + 1) < startDepth n →
        gapDepth n = startDepth (n + 1)
  equal_lt_gap :
    ∀ n : ℕ,
      startDepth n = startDepth (n + 1) →
        startDepth n < gapDepth n
  firstCrossing :
    ∀ n : ℕ,
      FirstCrossingArithmeticData ((block n).base)
  firstCrossing_lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      M < (firstCrossing n).length

namespace ContractingIntegerChain

/-- eventually-all-contracting tail から純算術 chain を作る。 -/
noncomputable def ofEventuallyContractingTail
    {O : OddOrbit} (D : EventuallyContractingTailData O) :
    ContractingIntegerChain := by
  classical
  let V : ∀ n : ℕ, State.ValuationData (D.state n) :=
    fun n => Classical.choice ((D.state n).existsValuationData)
  let T : ContractingTower O := D.toContractingTower
  let G : ∀ n : ℕ, FirstCrossingData (D.state n) :=
    fun n => Classical.choice
      ((D.state n).existsFirstCrossingData (D.state_contracting n))
  let F : ContractingFirstCrossingTower T := {
    crossing := by
      intro n
      simpa [T] using G n
  }
  refine {
    block := fun n =>
      ContractingBlockArithmetic.ofState
        (D.state n) (D.state_contracting n)
    connects := ?_
    startDepth := fun n => (V n).startDepth
    startOddPart := fun n => (V n).startOddPart
    nextDepth := fun n => (V n).nextDepth
    nextOddPart := fun n => (V n).nextOddPart
    gapDepth := fun n => (V n).gapDepth
    gapOddPart := fun n => (V n).gapOddPart
    startFactor := ?_
    nextFactor := ?_
    gapFactor := ?_
    depth_coherent := ?_
    startDepth_two_le := ?_
    gapDepth_two_le := ?_
    rise_gap_eq := ?_
    fall_gap_eq := ?_
    equal_lt_gap := ?_
    firstCrossing := ?_
    firstCrossing_lengths_tend_to_infinity := ?_
  }
  · intro n
    change
      (D.state n).startValue + (D.state n).valueGap =
        (D.state (n + 1)).startValue
    rw [← (D.state n).nextValue_eq_startValue_add_valueGap]
    exact D.nextValue_eq_next_startValue n
  · intro n
    change
      TwoAdic.ExactFactor
        ((D.state n).startValue + 1)
        (V n).startDepth (V n).startOddPart
    exact (V n).startFactor
  · intro n
    change
      TwoAdic.ExactFactor
        ((D.state n).startValue + (D.state n).valueGap + 1)
        (V n).nextDepth (V n).nextOddPart
    rw [← (D.state n).nextValue_eq_startValue_add_valueGap]
    exact (V n).nextFactor
  · intro n
    change
      TwoAdic.ExactFactor
        (D.state n).valueGap
        (V n).gapDepth (V n).gapOddPart
    exact (V n).gapFactor
  · intro n
    exact D.valuation_nextDepth_eq_next_startDepth n (V n) (V (n + 1))
  · intro n
    exact (V n).startDepth_two_le
  · intro n
    exact (V n).gapDepth_two_le
  · intro n hRise
    have hcoh := D.valuation_nextDepth_eq_next_startDepth n (V n) (V (n + 1))
    have hlocal : (V n).startDepth < (V n).nextDepth := by
      rw [hcoh]
      exact hRise
    exact (V n).gapDepth_eq_startDepth_of_lt hlocal
  · intro n hFall
    have hcoh := D.valuation_nextDepth_eq_next_startDepth n (V n) (V (n + 1))
    have hlocal : (V n).nextDepth < (V n).startDepth := by
      rw [hcoh]
      exact hFall
    have h := (V n).gapDepth_eq_nextDepth_of_lt hlocal
    rw [hcoh] at h
    exact h
  · intro n hEq
    have hcoh := D.valuation_nextDepth_eq_next_startDepth n (V n) (V (n + 1))
    have hlocal : (V n).startDepth = (V n).nextDepth := by
      rw [hcoh]
      exact hEq
    exact (V n).startDepth_lt_gapDepth_of_eq hlocal
  · intro n
    change
      FirstCrossingArithmeticData
        (BlockArithmeticData.ofState (D.state n))
    exact FirstCrossingArithmeticData.ofFirstCrossing (G n)
  · intro M
    obtain ⟨J, hJ⟩ := F.lengths_tend_to_infinity M
    refine ⟨J, ?_⟩
    intro n hn
    have h := hJ n hn
    change M < (G n).length at h
    exact h

/-- gap depth `D` から full block 長への指数下界 `3*2^D < r`。 -/
theorem three_mul_twoPow_gapDepth_lt_length
    (C : ContractingIntegerChain) (n : ℕ) :
    3 * 2 ^ C.gapDepth n < (C.block n).base.length := by
  have hfactor := C.gapFactor n
  have hoddPos : 0 < C.gapOddPart n := by
    rcases hfactor.2 with ⟨k, hk⟩
    omega
  have hpowLe :
      2 ^ C.gapDepth n ≤
        2 ^ C.gapDepth n * C.gapOddPart n := by
    have hone : 1 ≤ C.gapOddPart n := by omega
    simpa using Nat.mul_le_mul_left (2 ^ C.gapDepth n) hone
  have hgapLe :
      2 ^ C.gapDepth n ≤ (C.block n).base.valueGap := by
    rw [hfactor.1]
    exact hpowLe
  have hthree := Nat.mul_le_mul_left 3 hgapLe
  exact lt_of_le_of_lt hthree (C.block n).threeGap_lt_length

/--
depth が上昇する step では odd part は強く縮み、
`4*u_(n+1) < 3*u_n` を満たす。
-/
theorem four_mul_nextOddPart_lt_three_mul_startOddPart_of_rise
    (C : ContractingIntegerChain) (n : ℕ)
    (hRise : C.startDepth n < C.startDepth (n + 1)) :
    4 * C.startOddPart (n + 1) <
      3 * C.startOddPart n := by
  have hA : C.startDepth n + 1 ≤ C.startDepth (n + 1) := by
    omega
  have hpowLe :
      2 ^ (C.startDepth n + 1) ≤
        2 ^ C.startDepth (n + 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hA
  have hcorr := (C.block n).corridor
  rw [C.connects n] at hcorr
  have hN := C.startFactor n
  have hNext := C.startFactor (n + 1)
  rw [hN.1, hNext.1] at hcorr
  have hlower :
      2 ^ C.startDepth n *
          (4 * C.startOddPart (n + 1)) ≤
        2 *
          (2 ^ C.startDepth (n + 1) *
            C.startOddPart (n + 1)) := by
    have hmul :=
      Nat.mul_le_mul_right (C.startOddPart (n + 1)) hpowLe
    rw [pow_succ] at hmul
    calc
      2 ^ C.startDepth n *
          (4 * C.startOddPart (n + 1))
          = 2 *
              ((2 ^ C.startDepth n * 2) *
                C.startOddPart (n + 1)) := by ring
      _ ≤ 2 *
          (2 ^ C.startDepth (n + 1) *
            C.startOddPart (n + 1)) :=
        Nat.mul_le_mul_left 2 hmul
  have hupper :
      2 ^ C.startDepth n *
          (4 * C.startOddPart (n + 1)) <
        2 ^ C.startDepth n *
          (3 * C.startOddPart n) := by
    calc
      2 ^ C.startDepth n *
          (4 * C.startOddPart (n + 1))
          ≤ 2 *
              (2 ^ C.startDepth (n + 1) *
                C.startOddPart (n + 1)) := hlower
      _ < 3 *
              (2 ^ C.startDepth n * C.startOddPart n) := hcorr
      _ = 2 ^ C.startDepth n *
          (3 * C.startOddPart n) := by ring
  exact
    (Nat.mul_lt_mul_left
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))).mp hupper

/--
depth が等しい step では odd part は増加しつつ `3/2` corridor 内に残る。
-/
theorem oddPart_growth_corridor_of_equalDepth
    (C : ContractingIntegerChain) (n : ℕ)
    (hEq : C.startDepth n = C.startDepth (n + 1)) :
    C.startOddPart n < C.startOddPart (n + 1) ∧
      2 * C.startOddPart (n + 1) <
        3 * C.startOddPart n := by
  have hcur := C.startFactor n
  have hnext := C.startFactor (n + 1)
  have hvalueLt :
      (C.block n).base.startValue + 1 <
        (C.block (n + 1)).base.startValue + 1 := by
    have hgap := (C.block n).base.valueGap_pos
    rw [← C.connects n]
    omega
  rw [hcur.1, hnext.1, ← hEq] at hvalueLt
  have hoddLt :
      C.startOddPart n < C.startOddPart (n + 1) :=
    (Nat.mul_lt_mul_left
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))).mp hvalueLt
  have hcorr := (C.block n).corridor
  rw [C.connects n] at hcorr
  rw [hcur.1, hnext.1, ← hEq] at hcorr
  have hcorr' :
      2 ^ C.startDepth n *
          (2 * C.startOddPart (n + 1)) <
        2 ^ C.startDepth n *
          (3 * C.startOddPart n) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcorr
  have hoddCorr :
      2 * C.startOddPart (n + 1) <
        3 * C.startOddPart n :=
    (Nat.mul_lt_mul_left
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))).mp hcorr'
  exact ⟨hoddLt, hoddCorr⟩

/-- depth 上昇が cofinal に起こること。 -/
def CofinalRise (C : ContractingIntegerChain) : Prop :=
  Selection.Cofinal (fun n => C.startDepth n < C.startDepth (n + 1))

/-- start depth が最終的に一定。 -/
def EventuallyConstantDepth (C : ContractingIntegerChain) : Prop :=
  ∃ N A : ℕ, ∀ n : ℕ, N ≤ n → C.startDepth n = A

private theorem nonincreasing_tail_le
    (A : ℕ → ℕ) {N n k : ℕ}
    (hstep : ∀ m : ℕ, N ≤ m → A (m + 1) ≤ A m)
    (hn : N ≤ n) :
    A (n + k) ≤ A n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := hstep (n + k) (by omega)
      have hik := ih
      have hindex : n + (k + 1) = n + k + 1 := by omega
      rw [hindex]
      exact le_trans hs hik

/--
自然数 depth 列の大域二分法：
rise が cofinal、または depth は最終的に一定。
-/
theorem cofinalRise_or_eventuallyConstantDepth
    (C : ContractingIntegerChain) :
    C.CofinalRise ∨ C.EventuallyConstantDepth := by
  classical
  by_cases hRise : C.CofinalRise
  · exact Or.inl hRise
  · right
    obtain ⟨N, hN⟩ :=
      Selection.Cofinal.eventually_not_of_not
        (fun n => C.startDepth n < C.startDepth (n + 1)) hRise
    have hstep :
        ∀ n : ℕ, N ≤ n →
          C.startDepth (n + 1) ≤ C.startDepth n := by
      intro n hn
      have hnot := hN n hn
      omega
    let P : ℕ → Prop :=
      fun a => ∃ n : ℕ, N ≤ n ∧ C.startDepth n = a
    have hP : ∃ a : ℕ, P a := by
      exact ⟨C.startDepth N, N, le_rfl, rfl⟩
    let A : ℕ := Nat.find hP
    obtain ⟨n₀, hn₀N, hn₀A⟩ := Nat.find_spec hP
    refine ⟨n₀, A, ?_⟩
    intro n hn
    have hle : C.startDepth n ≤ C.startDepth n₀ := by
      let k := n - n₀
      have hnk : n₀ + k = n := by
        dsimp [k]
        exact Nat.add_sub_of_le hn
      have h := nonincreasing_tail_le C.startDepth hstep hn₀N (n := n₀) (k := k)
      rw [hnk] at h
      exact h
    have hmin : A ≤ C.startDepth n := by
      apply Nat.find_min' hP
      exact ⟨n, le_trans hn₀N hn, rfl⟩
    rw [hn₀A] at hle
    omega

end ContractingIntegerChain
end IntegerObstruction
end AdjacentReturn
end Collatz
