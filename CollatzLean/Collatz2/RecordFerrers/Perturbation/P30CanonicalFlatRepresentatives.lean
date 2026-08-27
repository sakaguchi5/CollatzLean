import CollatzLean.Collatz2.RecordFerrers.Perturbation.P29BooleanCoarsening
import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedPotential

/-!
# Record–Ferrers 摂動理論 30: 粗視化骨格の標準平坦代表

P29 では、標準 Record 境界を残す / 消す Boolean pattern ごとに、
同じ fixed chord 内の FirstCrossing 実現が存在することを示した。
ただし、その実現は存在定理から選ばれたものであり、FiberPoint 自体は標準的ではなかった。

本ファイルでは、粗視化後の length skeleton だけから Ferrers profile を直接定める。
各 RecordBlock の内部では excess を左端 critical roof の高さに固定し、
次の Record 境界でだけ新しい critical roof へ上がる階段形を使う。

この構成は RecordChain の proof object をデータとして読み出さない。
`RecordChain : Prop` のまま、proof は単調性・境界条件・RecordBlock 性の確認だけに使う。

主結果は次の二点である。

* 各 Boolean 粗視化 pattern は choice-free な標準平坦 FiberPoint を持ち、
  その canonical RecordDecomposition は P29 の `coarsenedLengthsFor` と exact に一致する。
* 同じ canonical length skeleton を持つ全 FiberPoint の中で、標準平坦代表は
  Ferrers inclusion に関する一意な最小元である。

Boolean pattern 間の順序と Ferrers inclusion の完全な順序同値、join 保存、
一境界削除の可換図式は、ここで得る最小代表 API の次段で扱う。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. length skeleton から作る平坦 excess -/

/--
`start` から始まる length skeleton を、各 block 内で左端 critical excess に
平坦化した自然数 profile。

`j < start` では 0 とする。cut 1 から使う場合、これは column 0 を 0 に固定する。
-/
def flatExcessForSkeleton (start : ℕ) : List ℕ → ℕ → ℕ
  | [], j =>
      if j < start then 0 else criticalExcess start
  | len :: rest, j =>
      if j < start then
        0
      else if j < start + len then
        criticalExcess start
      else
        flatExcessForSkeleton (start + len) rest j

@[simp] theorem flatExcessForSkeleton_of_before_start
    (start : ℕ)
    (lengths : List ℕ)
    {j : ℕ}
    (hj : j < start) :
    flatExcessForSkeleton start lengths j = 0 := by
  cases lengths <;> simp [flatExcessForSkeleton, hj]

@[simp] theorem flatExcessForSkeleton_of_head
    (start len : ℕ)
    (rest : List ℕ)
    {j : ℕ}
    (hsj : start ≤ j)
    (hj : j < start + len) :
    flatExcessForSkeleton start (len :: rest) j =
      criticalExcess start := by
  simp [flatExcessForSkeleton, not_lt.mpr hsj, hj]

@[simp] theorem flatExcessForSkeleton_of_after_head
    (start len : ℕ)
    (rest : List ℕ)
    {j : ℕ}
    (hj : start + len ≤ j) :
    flatExcessForSkeleton start (len :: rest) j =
      flatExcessForSkeleton (start + len) rest j := by
  have hStart : ¬ j < start := by omega
  have hHead : ¬ j < start + len := by omega
  simp [flatExcessForSkeleton, hStart, hHead]

/-- genuine RecordChain の左端では平坦 profile が exact に critical roof を取る。 -/
theorem flatExcessForSkeleton_at_start_of_chain
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    flatExcessForSkeleton start lengths start =
      criticalExcess start := by
  cases C with
  | @last start len B hTerminal =>
      exact flatExcessForSkeleton_of_head
        start len [] le_rfl
        (Nat.lt_add_of_pos_right B.length_pos)
  | @cons start len rest B hInterior T =>
      exact flatExcessForSkeleton_of_head
        start len rest le_rfl
        (Nat.lt_add_of_pos_right B.length_pos)

/--
RecordChain の範囲では、start 以後の平坦 profile は少なくとも
start の critical excess 以上にある。
-/
theorem criticalExcess_le_flatExcessForSkeleton_of_chain
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths)
    {j : ℕ}
    (hsj : start ≤ j)
    (hjp : j < p) :
    criticalExcess start ≤ flatExcessForSkeleton start lengths j := by
  induction C with
  | @last start len B hTerminal =>
      have hjHead : j < start + len := by omega
      rw [flatExcessForSkeleton_of_head start len [] hsj hjHead]
  | @cons start len rest B hInterior T ih =>
      by_cases hjHead : j < start + len
      · rw [flatExcessForSkeleton_of_head start len rest hsj hjHead]
      · have hEndJ : start + len ≤ j := by omega
        rw [flatExcessForSkeleton_of_after_head start len rest hEndJ]
        have hQ : criticalExcess start ≤ criticalExcess (start + len) :=
          criticalExcess_mono (by omega)
        exact hQ.trans (ih hEndJ)

/-- genuine RecordChain から作った平坦 profile は proper cuts 上で非減少。 -/
theorem flatExcessForSkeleton_mono_of_chain
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths)
    {i j : ℕ}
    (hij : i ≤ j)
    (hjp : j < p) :
    flatExcessForSkeleton start lengths i ≤
      flatExcessForSkeleton start lengths j := by
  induction C with
  | @last start len B hTerminal =>
      by_cases hjStart : j < start
      · have hiStart : i < start := by omega
        simp [flatExcessForSkeleton_of_before_start, hiStart, hjStart]
      · have hsj : start ≤ j := by omega
        have hjHead : j < start + len := by omega
        by_cases hiStart : i < start
        · rw [flatExcessForSkeleton_of_before_start start [len] hiStart]
          rw [flatExcessForSkeleton_of_head start len [] hsj hjHead]
          omega
        · have hsi : start ≤ i := by omega
          have hiHead : i < start + len := lt_of_le_of_lt hij hjHead
          rw [flatExcessForSkeleton_of_head start len [] hsi hiHead,
              flatExcessForSkeleton_of_head start len [] hsj hjHead]
  | @cons start len rest B hInterior T ih =>
      by_cases hjStart : j < start
      · have hiStart : i < start := by omega
        simp [flatExcessForSkeleton_of_before_start, hiStart, hjStart]
      · have hsj : start ≤ j := by omega
        by_cases hjHead : j < start + len
        · by_cases hiStart : i < start
          · rw [flatExcessForSkeleton_of_before_start start (len :: rest) hiStart]
            rw [flatExcessForSkeleton_of_head start len rest hsj hjHead]
            omega
          · have hsi : start ≤ i := by omega
            have hiHead : i < start + len := lt_of_le_of_lt hij hjHead
            rw [flatExcessForSkeleton_of_head start len rest hsi hiHead,
                flatExcessForSkeleton_of_head start len rest hsj hjHead]
        · have hEndJ : start + len ≤ j := by omega
          rw [flatExcessForSkeleton_of_after_head start len rest hEndJ]
          by_cases hiEnd : i < start + len
          · by_cases hiStart : i < start
            · rw [flatExcessForSkeleton_of_before_start start (len :: rest) hiStart]
              omega
            · have hsi : start ≤ i := by omega
              rw [flatExcessForSkeleton_of_head start len rest hsi hiEnd]
              have hLower :=
                criticalExcess_le_flatExcessForSkeleton_of_chain
                  T hEndJ hjp
              exact
                (criticalExcess_mono (by omega : start ≤ start + len)).trans hLower
          · have hEndI : start + len ≤ i := by omega
            rw [flatExcessForSkeleton_of_after_head start len rest hEndI]
            exact ih

/--
平坦 profile は、同じ RecordChain を持つ source profile 以下にある。
各 block 内では source excess の単調性だけを使う。
-/
theorem flatExcessForSkeleton_le_source_of_chain
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths)
    {j : ℕ}
    (hjp : j < p) :
    flatExcessForSkeleton start lengths j ≤ x.excessAt j := by
  induction C with
  | @last start len B hTerminal =>
      by_cases hjStart : j < start
      · rw [flatExcessForSkeleton_of_before_start start [len] hjStart]
        omega
      · have hsj : start ≤ j := by omega
        have hjHead : j < start + len := by omega
        rw [flatExcessForSkeleton_of_head start len [] hsj hjHead]
        have hRoof : x.excessAt start = criticalExcess start :=
          excessAt_eq_criticalExcess_of_roof B.start_roof
        have hMono := x.excess_mono hsj (Nat.le_of_lt hjp)
        rw [hRoof] at hMono
        exact hMono
  | @cons start len rest B hInterior T ih =>
      by_cases hjStart : j < start
      · rw [flatExcessForSkeleton_of_before_start start (len :: rest) hjStart]
        omega
      · have hsj : start ≤ j := by omega
        by_cases hjHead : j < start + len
        · rw [flatExcessForSkeleton_of_head start len rest hsj hjHead]
          have hRoof : x.excessAt start = criticalExcess start :=
            excessAt_eq_criticalExcess_of_roof B.start_roof
          have hMono := x.excess_mono hsj (Nat.le_of_lt hjp)
          rw [hRoof] at hMono
          exact hMono
        · have hEndJ : start + len ≤ j := by omega
          rw [flatExcessForSkeleton_of_after_head start len rest hEndJ]
          exact ih

/-! ## 2. 同じ block length を平坦 profile 上へ移す -/

/--
source の genuine RecordBlock と同じ endpoints を持ち、target が block 内で
左端 critical excess に平坦なら、target 上でも同じ長さが genuine RecordBlock になる。
-/
theorem recordBlock_of_flat_same_length
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {x y : FiberPoint P.oddCount P.twoDepth}
    {start len : ℕ}
    (B : RecordBlock x start len)
    (hStartPos : 0 < start)
    (hFlatStart : y.excessAt start = criticalExcess start)
    (hFlatInside :
      ∀ j : ℕ,
        0 < j →
        j < len →
        y.excessAt (start + j) = criticalExcess start)
    (hFlatEnd :
      start + len < P.oddCount →
        y.excessAt (start + len) = criticalExcess (start + len)) :
    RecordBlock y start len := by
  have hStartLe : start ≤ P.oddCount := by
    exact
      (Nat.le_add_right start len).trans
       B.end_le_terminal
  have hStartRoof : y.height start = criticalHeight start := by
    have h := y.height_eq_index_add_excess hStartLe
    rw [hFlatStart] at h
    unfold criticalExcess at h
    have hBase := index_le_criticalHeight start
    omega
  have hEndpointEq : y.height (start + len) = x.height (start + len) := by
    by_cases hInterior : start + len < P.oddCount
    · have hy := y.height_eq_index_add_excess (Nat.le_of_lt hInterior)
      rw [hFlatEnd hInterior] at hy
      unfold criticalExcess at hy
      have hBase := index_le_criticalHeight (start + len)
      have hyRoof : y.height (start + len) = criticalHeight (start + len) := by
        omega
      rw [hyRoof, B.next_roof_if_interior hInterior]
    · have hTerminal : start + len = P.oddCount :=
        Nat.le_antisymm B.end_le_terminal (Nat.le_of_not_gt hInterior)
      rw [hTerminal, y.height_terminal, x.height_terminal]
  have hTotal :
      twoSteps (blockWord y start len) = criticalHeight len + 1 := by
    have hx := height_add_eq_add_blockDepth x start len
    have hy := height_add_eq_add_blockDepth y start len
    rw [B.start_roof, B.local_twoSteps] at hx
    rw [hStartRoof] at hy
    rw [hEndpointEq] at hy
    have hEq :
        criticalHeight start + twoSteps (blockWord y start len) =
          criticalHeight start + (criticalHeight len + 1) := by
      exact hy.symm.trans hx
    exact Nat.add_left_cancel hEq
  have hLocalDepth :
      ∀ j : ℕ,
        0 < j →
        j < len →
        twoSteps (blockWord y start j) = j := by
    intro j hjPos hjLt
    have hEndJ : start + j < P.oddCount := by
      exact lt_of_lt_of_le
        (Nat.add_lt_add_left hjLt start)
        B.end_le_terminal
    have hAt := y.height_eq_index_add_excess (Nat.le_of_lt hEndJ)
    rw [hFlatInside j hjPos hjLt] at hAt
    unfold criticalExcess at hAt
    have hBase := index_le_criticalHeight start
    have hAt' : y.height (start + j) = criticalHeight start + j := by
      omega
    have hAdd := height_add_eq_add_blockDepth y start j
    rw [hStartRoof, hAt'] at hAdd
    exact Nat.add_left_cancel hAdd.symm
  have hMinimal : MinimalBlock (blockWord y start len) := by
    have hOdd : oddSteps (blockWord y start len) = len :=
      oddSteps_blockWord y B.end_le_terminal
    refine {
      firstCrossing := ?_
      minimalDepth := by
        rw [hOdd]
        exact hTotal
    }
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · apply List.ne_nil_of_length_pos
      have : 0 < oddSteps (blockWord y start len) := by
        rw [hOdd]
        exact B.length_pos
      simpa [oddSteps] using this
    · intro j hjPos hjLtWord
      have hWordLen : (blockWord y start len).length = len := by
        simpa [oddSteps] using hOdd
      have hjLt : j < len := by simpa [hWordLen] using hjLtWord
      have hTake : (blockWord y start len).take j = blockWord y start j := by
        simp [blockWord, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjLt)]
      have hDepth := hLocalDepth j hjPos hjLt
      have hEndJ : start + j < P.oddCount := by
        exact lt_of_lt_of_le
          (Nat.add_lt_add_left hjLt start)
          B.end_le_terminal
      have hOddJ : oddSteps (blockWord y start j) = j :=
        oddSteps_blockWord y (Nat.le_of_lt hEndJ)
      apply (expanding_iff_twoPow_lt_threePow).2
      rw [hTake, hDepth, hOddJ]
      have hCrit := criticalHeight_pow_lt_threePow hjPos
      have hIdx := index_le_criticalHeight j
      have hPowLe : 2 ^ j ≤ 2 ^ criticalHeight j :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hIdx
      exact lt_of_le_of_lt hPowLe hCrit
    · apply contracting_of_twoSteps_eq_minimalDepth
      · rw [hOdd]
        exact B.length_pos
      · unfold minimalDepth
        rw [hOdd]
        exact hTotal
  have hLenLt : len < P.oddCount := by
    calc
      len < start + len :=
        Nat.lt_add_of_pos_left hStartPos
      _ ≤ P.oddCount :=
        B.end_le_terminal
  have hDrop :=
    chordDrop_of_primitiveReduced
      P hPrimitive hReduced B.length_pos hLenLt
  apply RecordBlock.ofMinimalAtRoof
    y B.length_pos B.end_le_terminal hMinimal hStartRoof
  · intro j hjPos _hjLt
    exact P.criticalHeight_below_chord hjPos
  · exact hDrop
  · intro hInterior
    have hEx := hFlatEnd hInterior
    have hHeight := y.height_eq_index_add_excess (Nat.le_of_lt hInterior)
    rw [hEx] at hHeight
    unfold criticalExcess at hHeight
    have hBase := index_le_criticalHeight (start + len)
    omega

/--
同じ length list の source RecordChain があるなら、平坦 profile を持つ target に
同じ RecordChain をそのまま構成できる。
-/
theorem RecordChain.of_flat_skeleton
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {x y : FiberPoint P.oddCount P.twoDepth}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths)
    (hStartPos : 0 < start)
    (hFlat :
      ∀ j : ℕ,
        start ≤ j →
        j < P.oddCount →
        y.excessAt j = flatExcessForSkeleton start lengths j) :
    RecordChain y start lengths := by
  revert hStartPos hFlat
  induction C with
  | @last start len B hTerminal =>
      intro hStartPos hFlat
      have hStartLt : start < P.oddCount := by
        calc
        start < start + len :=
          Nat.lt_add_of_pos_right B.length_pos
        _ = P.oddCount :=
      hTerminal
      have hStart : y.excessAt start = criticalExcess start := by
        rw [hFlat start le_rfl hStartLt]
        exact flatExcessForSkeleton_at_start_of_chain
          (RecordChain.last B hTerminal)
      have hInside :
          ∀ j : ℕ, 0 < j → j < len →
            y.excessAt (start + j) = criticalExcess start := by
        intro j hjPos hjLt
        rw [hFlat (start + j) (by omega) (by omega)]
        exact flatExcessForSkeleton_of_head
          start len [] (by omega) (by omega)
      have hEnd :
          start + len < P.oddCount →
            y.excessAt (start + len) = criticalExcess (start + len) := by
        intro hInt
        rw [hTerminal] at hInt
        omega
      have B' := recordBlock_of_flat_same_length
        P hPrimitive hReduced B hStartPos hStart hInside hEnd
      exact RecordChain.last B' hTerminal
  | @cons start len rest B hInterior T ih =>
      intro hStartPos hFlat
      have hStart : y.excessAt start = criticalExcess start := by
        rw [hFlat start le_rfl (by omega)]
        exact flatExcessForSkeleton_at_start_of_chain
          (RecordChain.cons B hInterior T)
      have hInside :
          ∀ j : ℕ, 0 < j → j < len →
            y.excessAt (start + j) = criticalExcess start := by
        intro j hjPos hjLt
        rw [hFlat (start + j) (by omega) (by omega)]
        exact flatExcessForSkeleton_of_head
          start len rest (by omega) (by omega)
      have hEnd :
          y.excessAt (start + len) = criticalExcess (start + len) := by
        rw [hFlat (start + len) (by omega) hInterior]
        rw [flatExcessForSkeleton_of_after_head
          start len rest le_rfl]
        exact flatExcessForSkeleton_at_start_of_chain T
      have B' := recordBlock_of_flat_same_length
        P hPrimitive hReduced B hStartPos hStart hInside (fun _ => hEnd)
      have hFlatTail :
          ∀ j : ℕ,
            start + len ≤ j →
            j < P.oddCount →
            y.excessAt j = flatExcessForSkeleton (start + len) rest j := by
        intro j hEndJ hjp
        rw [hFlat j (by omega) hjp]
        exact flatExcessForSkeleton_of_after_head
          start len rest hEndJ
      exact RecordChain.cons B' hInterior (ih (by omega) hFlatTail)

/-! ## 3. Boolean pattern ごとの choice-free 標準平坦代表 -/

/-- P29 の existence theorem を Prop 内だけで使い、平坦 column の単調性を得る。 -/
theorem canonicalFlatColumn_mono
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    Monotone
      (fun i : Fin P.oddCount =>
        flatExcessForSkeleton 1 (coarsenedLengthsFor D R) i.1) := by
  obtain ⟨x, E, _hFx, hE⟩ :=
    exists_actual_realization_of_pattern
      P hPrimitive hReduced u D R
  have C : RecordChain x 1 (coarsenedLengthsFor D R) := by
    have hC := E.chain
    rw [hE] at hC
    exact hC
  intro i j hij
  exact flatExcessForSkeleton_mono_of_chain C hij j.isLt

/-- 平坦 column は fixed rectangle の高さを越えない。 -/
theorem canonicalFlatColumn_bounded
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ∀ i : Fin P.oddCount,
      flatExcessForSkeleton 1 (coarsenedLengthsFor D R) i.1 ≤
        P.twoDepth - P.oddCount := by
  obtain ⟨x, E, _hFx, hE⟩ :=
    exists_actual_realization_of_pattern
      P hPrimitive hReduced u D R
  have C : RecordChain x 1 (coarsenedLengthsFor D R) := by
    have hC := E.chain
    rw [hE] at hC
    exact hC
  intro i
  have hLe := flatExcessForSkeleton_le_source_of_chain C i.isLt
  exact hLe.trans (x.excess_le_rectangleHeight (Nat.le_of_lt i.isLt))

/--
P29 の粗視化 length skeleton を、cut 1 から平坦 Ferrers profile へ送る。
column の値は `coarsenedLengthsFor D R` だけから決まり、実現点の選択には依存しない。
-/
def canonicalFlatFiberShape
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    FiberShape P.oddCount P.twoDepth := by
  have hp : 0 < P.oddCount := by
    have hEnd := D.chain.start_add_sum_eq_terminal
    omega
  have hpH : P.oddCount ≤ P.twoDepth := by
    have h := FiberPoint.oddSteps_le_twoSteps_of_valid u.valid
    rw [u.oddSteps_eq, u.twoSteps_eq] at h
    exact h
  refine {
    shape := {
      column := fun i =>
        flatExcessForSkeleton 1 (coarsenedLengthsFor D R) i.1
      mono := canonicalFlatColumn_mono
        P hPrimitive hReduced u D R
    }
    p_pos := hp
    p_le_H := hpH
    first_zero := ?_
    bounded := canonicalFlatColumn_bounded
      P hPrimitive hReduced u D R
  }
  change flatExcessForSkeleton 1 (coarsenedLengthsFor D R) 0 = 0
  exact flatExcessForSkeleton_of_before_start 1 _ (by omega)

/-- Boolean pattern の choice-free 標準平坦 FiberPoint。 -/
def canonicalFlatRepresentative
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    FiberPoint P.oddCount P.twoDepth :=
  (canonicalFlatFiberShape P hPrimitive hReduced u D R).toFiberPoint

/-- 標準平坦代表の proper excess は定義した階段 profile と exact に一致。 -/
theorem canonicalFlatRepresentative_excessAt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {j : ℕ}
    (hjp : j < P.oddCount) :
    (canonicalFlatRepresentative
      P hPrimitive hReduced u D R).excessAt j =
      flatExcessForSkeleton 1 (coarsenedLengthsFor D R) j := by
  let S := canonicalFlatFiberShape P hPrimitive hReduced u D R
  have hShape := S.toFerrersShape_toFiberPoint
  have hCol := congrArg
    (fun T : FerrersShape P.oddCount => T.column ⟨j, hjp⟩) hShape
  change
    (canonicalFlatRepresentative
      P hPrimitive hReduced u D R).excessAt j =
      (canonicalFlatFiberShape
        P hPrimitive hReduced u D R).shape.column ⟨j, hjp⟩ at hCol
  exact hCol

/-- 標準平坦代表は FirstCrossing。 -/
theorem canonicalFlatRepresentative_firstCrossing
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    FirstCrossing
      (canonicalFlatRepresentative
        P hPrimitive hReduced u D R).word := by
  obtain ⟨x, E, hFx, hE⟩ :=
    exists_actual_realization_of_pattern
      P hPrimitive hReduced u D R
  let L := coarsenedLengthsFor D R
  have C : RecordChain x 1 L := by
    have hC := E.chain
    rw [hE] at hC
    exact hC
  have hp : 0 < P.oddCount := by
    have hEnd := C.start_add_sum_eq_terminal
    omega
  have hContract : ContractingChord P.oddCount P.twoDepth := by
    have hPow := (contracting_iff_threePow_lt_twoPow).1 hFx.terminalContracting
    simpa [ContractingChord, x.oddSteps_eq, x.twoSteps_eq] using hPow
  apply firstCrossing_downward hp hContract hFx
  intro i
  change
    (canonicalFlatRepresentative
      P hPrimitive hReduced u D R).excessAt i.1 ≤ x.excessAt i.1
  rw [canonicalFlatRepresentative_excessAt
    P hPrimitive hReduced u D R i.isLt]
  exact flatExcessForSkeleton_le_source_of_chain C i.isLt

/--
標準平坦代表の canonical RecordDecomposition は、P29 の粗視化 length skeleton と exact に一致。
-/
theorem exists_canonicalFlatRecordDecomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ∃ E : RecordDecomposition
        (canonicalFlatRepresentative
          P hPrimitive hReduced u D R) 1,
      E.lengths = coarsenedLengthsFor D R := by
  obtain ⟨x, E0, _hFx, hE0⟩ :=
    exists_actual_realization_of_pattern
      P hPrimitive hReduced u D R
  let L := coarsenedLengthsFor D R
  have C0 : RecordChain x 1 L := by
    have hC := E0.chain
    rw [hE0] at hC
    exact hC
  let y := canonicalFlatRepresentative
    P hPrimitive hReduced u D R
  have hFlat :
      ∀ j : ℕ,
        1 ≤ j →
        j < P.oddCount →
        y.excessAt j = flatExcessForSkeleton 1 L j := by
    intro j _hj1 hjp
    dsimp [y, L]
    exact canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced u D R hjp
  have C : RecordChain y 1 L :=
    RecordChain.of_flat_skeleton
      P hPrimitive hReduced C0 (by omega) hFlat
  have hFy : FirstCrossing y.word := by
    dsimp [y]
    exact canonicalFlatRepresentative_firstCrossing
      P hPrimitive hReduced u D R
  let E : RecordDecomposition y 1 := {
    lengths := L
    chain := C
    whole_firstCrossing := hFy
  }
  exact ⟨E, rfl⟩

/-! ## 4. 同じ canonical skeleton の中での一意最小性 -/

/--
同じ coarse length skeleton を持つ任意の FiberPoint は、標準平坦代表の上側にある。
つまり標準平坦代表は Ferrers inclusion に関する最小実現。
-/
theorem canonicalFlatRepresentative_le_of_same_skeleton
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (x : FiberPoint P.oddCount P.twoDepth)
    (E : RecordDecomposition x 1)
    (hE : E.lengths = coarsenedLengthsFor D R) :
    FiberPoint.FerrersLe
      (canonicalFlatRepresentative
        P hPrimitive hReduced u D R) x := by
  let L := coarsenedLengthsFor D R
  have C : RecordChain x 1 L := by
    have hC := E.chain
    rw [hE] at hC
    exact hC
  intro i
  change
    (canonicalFlatRepresentative
      P hPrimitive hReduced u D R).excessAt i.1 ≤ x.excessAt i.1
  rw [canonicalFlatRepresentative_excessAt
    P hPrimitive hReduced u D R i.isLt]
  exact flatExcessForSkeleton_le_source_of_chain C i.isLt

/--
同じ canonical skeleton の実現が標準平坦代表以下でもあるなら、
Ferrers antisymmetry により FiberPoint 自体が標準平坦代表と一致する。
-/
theorem canonicalFlatRepresentative_unique_minimal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (x : FiberPoint P.oddCount P.twoDepth)
    (E : RecordDecomposition x 1)
    (hE : E.lengths = coarsenedLengthsFor D R)
    (hxLe : FiberPoint.FerrersLe x
      (canonicalFlatRepresentative
        P hPrimitive hReduced u D R)) :
    x = canonicalFlatRepresentative
      P hPrimitive hReduced u D R := by
  have hFlatLe :=
    canonicalFlatRepresentative_le_of_same_skeleton
      P hPrimitive hReduced u D R x E hE
  apply FiberPoint.toFerrersShape_injective
  exact FerrersShape.le_antisymm hxLe hFlatLe


/--
同じ canonical length skeleton を持つ全実現の中で、標準平坦代表は
Ferrers inclusion だけでなく genuine `affineConst` についても最小である。
-/
theorem canonicalFlatRepresentative_affineConst_le_of_same_skeleton
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (x : FiberPoint P.oddCount P.twoDepth)
    (E : RecordDecomposition x 1)
    (hE : E.lengths = coarsenedLengthsFor D R) :
    affineConst
        (canonicalFlatRepresentative
          P hPrimitive hReduced u D R).word ≤
      affineConst x.word := by
  have hFerrers :=
    canonicalFlatRepresentative_le_of_same_skeleton
      P hPrimitive hReduced u D R x E hE
  have hArea :
      weightedArea
          (canonicalFlatRepresentative
            P hPrimitive hReduced u D R).toFerrersShape ≤
        weightedArea x.toFerrersShape := by
    exact weightedArea_mono hFerrers
  rw [affineConst_eq_base_add_weightedArea,
      affineConst_eq_base_add_weightedArea]
  exact Nat.add_le_add_left hArea _

/-- 異なる Boolean pattern は標準平坦 FiberPoint も異なる。 -/
theorem canonicalFlatRepresentative_injective
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    Function.Injective
      (fun R : RetainedBoundaryPattern D =>
        canonicalFlatRepresentative
          P hPrimitive hReduced u D R) := by
  intro R S hPoint
  obtain ⟨ER, hER⟩ :=
    exists_canonicalFlatRecordDecomposition
      P hPrimitive hReduced u D R
  obtain ⟨ES, hES⟩ :=
    exists_canonicalFlatRecordDecomposition
      P hPrimitive hReduced u D S
  have hLengths :
      coarsenedLengthsFor D R =
        coarsenedLengthsFor D S := by
    have hCanon :=
      RecordDecomposition.lengths_unique_of_point_eq
        hPoint ER ES
    calc
      coarsenedLengthsFor D R = ER.lengths := hER.symm
      _ = ES.lengths := hCanon
      _ = coarsenedLengthsFor D S := hES
  exact coarsenedLengthsFor_injective D hLengths

/--
## 主定理

Boolean 粗視化の全 pattern は、choice-free な相異なる標準平坦 FirstCrossing point を持つ。
各 point の canonical skeleton は指定された粗視化 length list であり、
その skeleton を持つ全実現の Ferrers 最小元である。
-/
theorem exists_canonical_flat_boolean_family
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ∃ f : RetainedBoundaryPattern D →
        FiberPoint P.oddCount P.twoDepth,
      Function.Injective f ∧
      (∀ R : RetainedBoundaryPattern D,
        FirstCrossing (f R).word ∧
        ∃ E : RecordDecomposition (f R) 1,
          E.lengths = coarsenedLengthsFor D R ∧
          ∀ x : FiberPoint P.oddCount P.twoDepth,
            ∀ Ex : RecordDecomposition x 1,
              Ex.lengths = coarsenedLengthsFor D R →
              FiberPoint.FerrersLe (f R) x) ∧
      Fintype.card (RetainedBoundaryPattern D) =
        2 ^ (D.lengths.length - 1) := by
  let f : RetainedBoundaryPattern D →
      FiberPoint P.oddCount P.twoDepth :=
    fun R => canonicalFlatRepresentative
      P hPrimitive hReduced u D R
  refine ⟨f, ?_, ?_, retainedBoundaryPattern_card D⟩
  · exact canonicalFlatRepresentative_injective
      P hPrimitive hReduced u D
  · intro R
    refine ⟨?_, ?_⟩
    · dsimp [f]
      exact canonicalFlatRepresentative_firstCrossing
        P hPrimitive hReduced u D R
    · obtain ⟨E, hE⟩ :=
        exists_canonicalFlatRecordDecomposition
          P hPrimitive hReduced u D R
      refine ⟨E, hE, ?_⟩
      intro x Ex hEx
      dsimp [f]
      exact canonicalFlatRepresentative_le_of_same_skeleton
        P hPrimitive hReduced u D R x Ex hEx

end RecordFerrers
end Collatz2
