import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Expanding
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Late
import CollatzLean.Collatz.AdjacentReturn.StrongContractingTail

/-!
# contracting 整数問題の Exact / Late 完全分解

`ContractingIntegerChain` の各 first crossing を Exact / Late に完全分解する。
さらに actual eventually-contracting tail から得られる整数 chain については、
Late の各項に対応する `LateBlockArithmeticData` と actual endpoint floor を
同一 witness 上で必ず供給する。

これにより

P_C
  -> Exact または Late
  -> Late なら exact commutator data + endpoint floor
  -> primitive / 2-adic refinement

という圧縮線の Exact / Late 接続部分を非空虚に固定する。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

namespace ContractingIntegerChain

/-- first crossing が adjacent block 全長と一致する Exact 項。 -/
def ExactAt (C : ContractingIntegerChain) (n : ℕ) : Prop :=
  (C.firstCrossing n).length = (C.block n).base.length

/-- first crossing が adjacent block 終端より手前で終わる Late 項。 -/
def LateAt (C : ContractingIntegerChain) (n : ℕ) : Prop :=
  (C.firstCrossing n).length < (C.block n).base.length

/-- 各 contracting 整数 block は Exact または Late。 -/
theorem exact_or_late
    (C : ContractingIntegerChain) (n : ℕ) :
    C.ExactAt n ∨ C.LateAt n := by
  have hle := (C.firstCrossing n).le_block
  unfold ExactAt LateAt
  omega

end ContractingIntegerChain

namespace LateBlockArithmeticData

/--
actual Late first crossing から純整数 `LateBlockArithmeticData` を作る。

actual orbit はこの constructor の境界でのみ使用し、生成後の対象は
`ContractingBlockArithmetic` と有限 word の算術だけを保持する。
-/
def ofActualFirstCrossing
    {O : OddOrbit} {R : State O}
    (hC : R.IsContracting)
    (F : FirstCrossingData R)
    (hLate : F.IsLate) :
    LateBlockArithmeticData (ContractingBlockArithmetic.ofState R hC) := by
  let S : Collatz.Word :=
    O.segment
      (R.startIndex + F.length)
      (R.length - F.length)
  have hword :
      R.word = R.word.take F.length ++ S := by
    have h := R.word_eq_prefix_append_suffix F.le_adjacent
    simpa [S, F.word_eq_segment] using h
  have hsuffixNonempty : S ≠ [] := by
    apply List.ne_nil_of_length_pos
    have hlen : S.length = R.length - F.length := by
      simp [S]
    rw [hlen]
    exact Nat.sub_pos_of_lt hLate
  have hsuffixAll : S.AllSuffixesContracting := by
    change
      (O.segment
        (R.startIndex + F.length)
        (R.length - F.length)).AllSuffixesContracting
    exact
      R.properSuffix_allSuffixesContracting
        F.length_pos hLate
  have hgapLt : R.valueGap < F.returnGap := by
    have hnextLePeak : R.nextValue ≤ F.endpointValue := by
      simpa [FirstCrossingData.endpointValue] using
        R.nextValue_le_positiveEndpoint
          F.length F.length_pos
    have hindexLt :
        R.startIndex + F.length < R.nextIndex := by
      rw [R.nextIndex_eq_startIndex_add_length]
      exact Nat.add_lt_add_left hLate R.startIndex
    have hnePeak : F.endpointValue ≠ R.nextValue := by
      unfold FirstCrossingData.endpointValue State.nextValue
      exact O.value_ne_of_lt_of_unbounded R.unbounded hindexLt
    have hnextLtPeak : R.nextValue < F.endpointValue :=
      lt_of_le_of_ne hnextLePeak (Ne.symm hnePeak)
    rw [
      R.nextValue_eq_startValue_add_valueGap,
      F.endpointValue_eq_startValue_add_returnGap
    ] at hnextLtPeak
    omega
  have htotalSplit :
      R.totalExponent = F.totalExponent + S.twoSteps := by
    change
      Word.twoSteps R.word =
        Word.twoSteps (R.word.take F.length) + Word.twoSteps S
    calc
      Word.twoSteps R.word =
          Word.twoSteps (R.word.take F.length ++ S) := by
        exact congrArg Word.twoSteps hword
      _ =
          Word.twoSteps (R.word.take F.length) +
            Word.twoSteps S := by
        rw [Word.twoSteps_append]
  have hsuffixScaled :
      2 ^ S.twoSteps * (R.startValue + R.valueGap) =
        3 ^ S.length * F.endpointValue + S.affineConst := by
    have hreal0 :=
      O.realizesSegment
        (R.startIndex + F.length)
        (R.length - F.length)
    have hlengthLe : F.length ≤ R.length := by
      exact Nat.le_of_lt hLate
    have hindex :
        R.startIndex + F.length + (R.length - F.length) =
          R.nextIndex := by
      rw [R.nextIndex_eq_startIndex_add_length]
      omega
    have hreal :
        Word.Realizes S F.endpointValue R.nextValue := by
      simpa [
        S,
        FirstCrossingData.endpointValue,
        State.nextValue,
        hindex
      ] using hreal0
    unfold Word.Realizes at hreal
    rw [R.nextValue_eq_startValue_add_valueGap] at hreal
    simpa [Word.oddSteps] using hreal
  refine {
    crossing := FirstCrossingArithmeticData.ofFirstCrossing F
    late := ?_
    valueGap_lt_returnGap := ?_
    suffix := S
    word_eq_crossing_append_suffix := ?_
    suffix_nonempty := hsuffixNonempty
    suffix_allSuffixesContracting := hsuffixAll
    suffix_length := ?_
    totalExponent_split := ?_
    suffixScaledEquation := ?_
  }
  · change F.length < R.length
    exact hLate
  · change R.valueGap < F.returnGap
    exact hgapLt
  · change R.word = R.word.take F.length ++ S
    exact hword
  · change S.length = R.length - F.length
    simp [S]
  · change R.totalExponent = F.totalExponent + S.twoSteps
    exact htotalSplit
  · change
      2 ^ S.twoSteps * (R.startValue + R.valueGap) =
        3 ^ S.length * F.endpointValue + S.affineConst
    exact hsuffixScaled

end LateBlockArithmeticData

namespace LateSuffixEndpointFloorData

/--
actual Late first crossing から suffix の future-minimum floor を純有限データへ移す。
この constructor の外では `OddOrbit` を保持しない。
-/
theorem ofActualFirstCrossing
    {O : OddOrbit} {R : State O}
    (hC : R.IsContracting)
    (F : FirstCrossingData R)
    (hLate : F.IsLate) :
    LateSuffixEndpointFloorData
      (LateBlockArithmeticData.ofActualFirstCrossing hC F hLate) := by
  let L : LateBlockArithmeticData
      (ContractingBlockArithmetic.ofState R hC) :=
    LateBlockArithmeticData.ofActualFirstCrossing hC F hLate
  change LateSuffixEndpointFloorData L
  refine {
    peak_odd := ?_
    prefixFloor := ?_
  }
  · change Odd F.endpointValue
    unfold FirstCrossingData.endpointValue
    exact O.value_odd _
  · intro k hkPos hkLe
    let S : Collatz.Word :=
      O.segment
        (R.startIndex + F.length)
        (R.length - F.length)
    have hSuffix : L.suffix = S := by
      rfl
    have hkLeS : k ≤ S.length := by
      simpa [hSuffix] using hkLe
    have hkLeQ : k ≤ R.length - F.length := by
      simpa [S] using hkLeS
    have htake :
        S.take k =
          O.segment (R.startIndex + F.length) k := by
      exact O.segment_take_of_le hkLeQ
    let y : ℕ :=
      O.value (R.startIndex + F.length + k)
    refine ⟨y, ?_, ?_⟩
    · rw [hSuffix, htake]
      change
        Word.Runs
          (O.segment (R.startIndex + F.length) k)
          F.endpointValue
          y
      simpa [y, FirstCrossingData.endpointValue, Nat.add_assoc] using
        O.runsSegment (R.startIndex + F.length) k
    · change R.startValue + R.valueGap ≤ y
      rw [← R.nextValue_eq_startValue_add_valueGap]
      have hfloor :=
        R.nextValue_le_positiveEndpoint
          (F.length + k) (by omega)
      simpa [y, Nat.add_assoc] using hfloor

end LateSuffixEndpointFloorData

/--
Late 項の arithmetic data と actual future-minimum floor を
同一の finite witness 上で保持する。
-/
structure LateArithmeticWitness
    (C : ContractingBlockArithmetic)
    (F : FirstCrossingArithmeticData C.base) where
  data : LateBlockArithmeticData C
  crossing_eq : data.crossing = F
  floor : LateSuffixEndpointFloorData data

namespace LateArithmeticWitness

/-- witness の return gap は actual floor により少なくとも6。 -/
theorem six_le_returnGap
    {C : ContractingBlockArithmetic}
    {F : FirstCrossingArithmeticData C.base}
    (W : LateArithmeticWitness C F) :
    6 ≤ W.data.crossing.returnGap :=
  W.floor.six_le_returnGap

/-- witness の first-crossing length は少なくとも19。 -/
theorem nineteen_le_crossingLength
    {C : ContractingBlockArithmetic}
    {F : FirstCrossingArithmeticData C.base}
    (W : LateArithmeticWitness C F) :
    19 ≤ W.data.crossing.length :=
  W.floor.nineteen_le_crossingLength

end LateArithmeticWitness

/--
P_C の Exact / Late 情報を非空虚にした純整数 obstruction。

`core` は従来の contracting 整数 chain。
`lateWitness` により Late 項では対応する finite suffix arithmetic と
actual future-minimum endpoint floor が同一 witness 上で必ず存在する。
-/
structure ExactLateContractingIntegerChain where
  core : ContractingIntegerChain
  lateWitness :
    ∀ n : ℕ,
      core.LateAt n →
        LateArithmeticWitness
          (core.block n)
          (core.firstCrossing n)

namespace ExactLateContractingIntegerChain

/--
従来 API 互換の Late data accessor。
内部では floor 付き `lateWitness` を正本とする。
-/
theorem lateData
    (C : ExactLateContractingIntegerChain)
    (n : ℕ)
    (hLate : C.core.LateAt n) :
    ∃ L : LateBlockArithmeticData (C.core.block n),
      L.crossing = C.core.firstCrossing n := by
  let W := C.lateWitness n hLate
  exact ⟨W.data, W.crossing_eq⟩

/-- Late 項では同じ arithmetic witness 上で endpoint floor も得られる。 -/
theorem lateFloorData
    (C : ExactLateContractingIntegerChain)
    (n : ℕ)
    (hLate : C.core.LateAt n) :
    ∃ L : LateBlockArithmeticData (C.core.block n),
      L.crossing = C.core.firstCrossing n ∧
        LateSuffixEndpointFloorData L := by
  let W := C.lateWitness n hLate
  exact ⟨W.data, W.crossing_eq, W.floor⟩

/-- Exact/Late 完備 obstruction から従来の contracting core を忘却する。 -/
theorem has_core
    (C : ExactLateContractingIntegerChain) :
    Nonempty ContractingIntegerChain :=
  ⟨C.core⟩

/-- Exact 項または、実データを伴う Late 項への完全分解。 -/
theorem exact_or_lateData
    (C : ExactLateContractingIntegerChain) (n : ℕ) :
    C.core.ExactAt n ∨
      ∃ L : LateBlockArithmeticData (C.core.block n),
        L.crossing = C.core.firstCrossing n := by
  rcases C.core.exact_or_late n with hExact | hLate
  · exact Or.inl hExact
  · exact Or.inr (C.lateData n hLate)

/-- Exact 項または、floor 付き Late witness への完全分解。 -/
theorem exact_or_lateFloorData
    (C : ExactLateContractingIntegerChain) (n : ℕ) :
    C.core.ExactAt n ∨
      ∃ L : LateBlockArithmeticData (C.core.block n),
        L.crossing = C.core.firstCrossing n ∧
          LateSuffixEndpointFloorData L := by
  rcases C.core.exact_or_late n with hExact | hLate
  · exact Or.inl hExact
  · exact Or.inr (C.lateFloorData n hLate)

/-- Late 項では actual floor により return gap は少なくとも6。 -/
theorem late_six_le_returnGap
    (C : ExactLateContractingIntegerChain)
    (n : ℕ)
    (hLate : C.core.LateAt n) :
    6 ≤ (C.core.firstCrossing n).returnGap := by
  let W := C.lateWitness n hLate
  rw [← W.crossing_eq]
  exact W.floor.six_le_returnGap

/-- Late 項では first-crossing length は少なくとも19。 -/
theorem late_nineteen_le_crossingLength
    (C : ExactLateContractingIntegerChain)
    (n : ℕ)
    (hLate : C.core.LateAt n) :
    19 ≤ (C.core.firstCrossing n).length := by
  let W := C.lateWitness n hLate
  rw [← W.crossing_eq]
  exact W.floor.nineteen_le_crossingLength

/-- Late 項では exact commutator identity を持つ有限データが必ず存在する。 -/
theorem late_has_commutator
    (C : ExactLateContractingIntegerChain) (n : ℕ)
    (hLate : C.core.LateAt n) :
    ∃ L : LateBlockArithmeticData (C.core.block n),
      L.crossing = C.core.firstCrossing n ∧
      L.suffixGap * L.crossing.affine =
        L.crossing.multiplicativeGap * L.suffix.affineConst +
          L.commutatorCore := by
  obtain ⟨L, hL⟩ := C.lateData n hLate
  exact ⟨L, hL, L.commutator_balance⟩

/-- Late 項では floor と commutator identity を同じ有限データ上で得る。 -/
theorem late_has_floor_and_commutator
    (C : ExactLateContractingIntegerChain) (n : ℕ)
    (hLate : C.core.LateAt n) :
    ∃ L : LateBlockArithmeticData (C.core.block n),
      L.crossing = C.core.firstCrossing n ∧
      LateSuffixEndpointFloorData L ∧
      L.suffixGap * L.crossing.affine =
        L.crossing.multiplicativeGap * L.suffix.affineConst +
          L.commutatorCore := by
  let W := C.lateWitness n hLate
  exact
    ⟨W.data, W.crossing_eq, W.floor, W.data.commutator_balance⟩

/-- Late 条件は Late data の存在と同値。 -/
theorem lateAt_iff_exists_lateData
    (C : ExactLateContractingIntegerChain) (n : ℕ) :
    C.core.LateAt n ↔
      ∃ L : LateBlockArithmeticData (C.core.block n),
        L.crossing = C.core.firstCrossing n := by
  constructor
  · exact C.lateData n
  · rintro ⟨L, hL⟩
    unfold ContractingIntegerChain.LateAt
    rw [← hL]
    exact L.late

/--
eventually-all-contracting actual tail から Exact/Late 完備の純整数 chain を作る。
-/
noncomputable def ofEventuallyContractingTail
    {O : OddOrbit} (D : EventuallyContractingTailData O) :
    ExactLateContractingIntegerChain := by
  classical
  let G : ∀ n : ℕ, FirstCrossingData (D.state n) :=
    fun n => Classical.choice
      ((D.state n).existsFirstCrossingData (D.state_contracting n))
  let C : ContractingIntegerChain :=
    ContractingIntegerChain.ofEventuallyContractingTail D
  refine {
    core := C
    lateWitness := ?_
  }
  intro n hLate
  have hCrossingLength :
      (C.firstCrossing n).length = (G n).length := by
    rfl
  have hBlockLength :
      (C.block n).base.length = (D.state n).length := by
    rfl
  have hLateActual : (G n).IsLate := by
    unfold ContractingIntegerChain.LateAt at hLate
    rw [hCrossingLength, hBlockLength] at hLate
    exact hLate
  let L : LateBlockArithmeticData (C.block n) := by
    change
      LateBlockArithmeticData
        (ContractingBlockArithmetic.ofState
          (D.state n) (D.state_contracting n))
    exact
      LateBlockArithmeticData.ofActualFirstCrossing
        (D.state_contracting n) (G n) hLateActual
  refine {
    data := L
    crossing_eq := ?_
    floor := ?_
  }
  · change
      FirstCrossingArithmeticData.ofFirstCrossing (G n) =
        C.firstCrossing n
    rfl
  · change
      LateSuffixEndpointFloorData
        (LateBlockArithmeticData.ofActualFirstCrossing
          (D.state_contracting n) (G n) hLateActual)
    exact
      LateSuffixEndpointFloorData.ofActualFirstCrossing
        (D.state_contracting n) (G n) hLateActual

end ExactLateContractingIntegerChain

/-- Exact/Late 完備の contracting 整数 obstruction が存在する。 -/
def HasExactLateContractingIntegerChain : Prop :=
  Nonempty ExactLateContractingIntegerChain

/--
非有界 odd 軌道は、expanding cofinal obstruction か、
Exact/Late 完備の contracting 整数 obstruction のどちらかを与える。
-/
theorem unbounded_to_expanding_or_exactLateContracting :
    HasUnboundedOddOrbit →
      Nonempty ExpandingIntegerTower ∨
        HasExactLateContractingIntegerChain := by
  rintro ⟨O, hU⟩
  rcases dichotomy_on_strong O hU with hE | hC
  · rcases hE with ⟨T⟩
    exact Or.inl ⟨ExpandingIntegerTower.ofTower T⟩
  · rcases hC with ⟨D⟩
    exact
      Or.inr
        ⟨ExactLateContractingIntegerChain.ofEventuallyContractingTail D⟩

/--
Expanding obstruction と Exact/Late 完備 contracting obstruction の双方を排除すれば、
非有界反例は存在しない。
-/
theorem no_unbounded_of_no_exactLate_integer_obstructions
    (hE : ¬ Nonempty ExpandingIntegerTower)
    (hC : ¬ HasExactLateContractingIntegerChain) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_to_expanding_or_exactLateContracting hU with hExp | hCon
  · exact hE hExp
  · exact hC hCon

end IntegerObstruction
end AdjacentReturn
end Collatz
