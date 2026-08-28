import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.GlobalLocalDecorationDeletion
import CollatzLean.Collatz2.RecordFerrers.Record.Canonicality

/-!
# Record–Ferrers Perturbation / Decoration Interval Skeleton Preservation

`GlobalLocalDecorationDeletion` では、actual source `u` と canonical flat top の間

  canonicalFlatTop ≤ x ≤ u

にある FirstCrossing fixed-fiber points を `InDecorationInterval` とした。

本ファイルでは、その区間が単なる Ferrers order interval ではなく、元の
`RecordDecomposition D` の length skeleton を完全に保存する actual decoration space
であることを証明する。

核心は次の三段階である。

* source の一つの `RecordBlock` を、flat skeleton と source の間にある target へ移す。
  record endpoints は lower/upper sandwich により critical roof 上へ固定され、
  local proper prefixes は target ≤ source から source block の FirstCrossing 条件を継承する。
* その block transfer を `RecordChain` 全体へ帰納的に貼る。
* `InDecorationInterval` の lower bound が canonical flat top であることから、
  flat skeleton lower bound を回収して元の `D.lengths` を target 上へ再構成する。

最終的に

  x ∈ InDecorationInterval
    ↔  x は source と flat top の間にあり、元の skeleton D.lengths を持つ actual decoration

のうち、必要な skeleton preservation 側を formalize する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 一つの source RecordBlock を interval target へ移送する -/

/--
source `u` の genuine record block を、同じ fixed fiber の target `x` へ移す。

必要なのは

* block start が positive、
* target が source 以下、
* target の block start が source と同じ critical roof、
* interior endpoint も source と同じ critical roof、

だけである。

proper local prefix depth は `x ≤ u` から source block の local FirstCrossing depth 以下になり、
terminal local depth は endpoints の一致から source と同じ `criticalHeight len + 1` に固定される。
-/
theorem recordBlock_of_between_flat_and_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {u x : FiberPoint P.oddCount P.twoDepth}
    {start len : ℕ}
    (B : RecordBlock u start len)
    (hStartPos : 0 < start)
    (hUpper : FiberPoint.FerrersLe x u)
    (hStartExcess :
      x.excessAt start = criticalExcess start)
    (hEndExcess :
      start + len < P.oddCount →
        x.excessAt (start + len) =
          criticalExcess (start + len)) :
    RecordBlock x start len := by
  have hStartLe : start ≤ P.oddCount := by
    exact
      (Nat.le_add_right start len).trans
        B.end_le_terminal
  have hStartRoof :
      x.height start = criticalHeight start := by
    have h := x.height_eq_index_add_excess hStartLe
    rw [hStartExcess] at h
    unfold criticalExcess at h
    have hBase := index_le_criticalHeight start
    omega
  have hEndpointEq :
      x.height (start + len) =
        u.height (start + len) := by
    by_cases hInterior : start + len < P.oddCount
    · have hx :=
        x.height_eq_index_add_excess
          (Nat.le_of_lt hInterior)
      rw [hEndExcess hInterior] at hx
      unfold criticalExcess at hx
      have hBase := index_le_criticalHeight (start + len)
      have hxRoof :
          x.height (start + len) =
            criticalHeight (start + len) := by
        omega
      rw [hxRoof, B.next_roof_if_interior hInterior]
    · have hTerminal : start + len = P.oddCount :=
        Nat.le_antisymm
          B.end_le_terminal
          (Nat.le_of_not_gt hInterior)
      rw [hTerminal, x.height_terminal, u.height_terminal]
  have hTotal :
      twoSteps (blockWord x start len) =
        criticalHeight len + 1 := by
    have hu := height_add_eq_add_blockDepth u start len
    have hx := height_add_eq_add_blockDepth x start len
    rw [B.start_roof, B.local_twoSteps] at hu
    rw [hStartRoof, hEndpointEq] at hx
    have hEq :
        criticalHeight start +
            twoSteps (blockWord x start len) =
          criticalHeight start +
            (criticalHeight len + 1) := by
      exact hx.symm.trans hu
    exact Nat.add_left_cancel hEq
  have hMinimal :
      MinimalBlock (blockWord x start len) := by
    have hOdd : oddSteps (blockWord x start len) = len :=
      oddSteps_blockWord x B.end_le_terminal
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
      have hPos : 0 < oddSteps (blockWord x start len) := by
        rw [hOdd]
        exact B.length_pos
      simpa [oddSteps] using hPos
    · intro j hjPos hjLtWord
      have hWordLen :
          (blockWord x start len).length = len := by
        simpa [oddSteps] using hOdd
      have hjLt : j < len := by
        simpa [hWordLen] using hjLtWord
      have hEndJ : start + j < P.oddCount := by
        exact lt_of_lt_of_le
          (Nat.add_lt_add_left hjLt start)
          B.end_le_terminal
      have hUpperCol := hUpper ⟨start + j, hEndJ⟩
      change
        x.excessAt (start + j) ≤
          u.excessAt (start + j) at hUpperCol
      have hxHeight :=
        x.height_eq_index_add_excess
          (Nat.le_of_lt hEndJ)
      have huHeight :=
        u.height_eq_index_add_excess
          (Nat.le_of_lt hEndJ)
      have hGlobalHeight :
          x.height (start + j) ≤
            u.height (start + j) := by
        omega
      have hxAdd := height_add_eq_add_blockDepth x start j
      have huAdd := height_add_eq_add_blockDepth u start j
      rw [hStartRoof] at hxAdd
      rw [B.start_roof] at huAdd
      have hLocalLe :
          twoSteps (blockWord x start j) ≤
            twoSteps (blockWord u start j) := by
        omega
      have hSourcePrefix :=
        B.minimal.firstCrossing.prefixTwoDepth_le_criticalHeight
          hjPos
          (by
            rw [B.local_oddSteps]
            exact hjLt)
      have hSourceSlice :
          prefixTwoDepth (blockWord u start len) j =
            twoSteps (blockWord u start j) := by
        unfold prefixTwoDepth blockWord
        rw [List.take_take,
            Nat.min_eq_left (Nat.le_of_lt hjLt)]
      rw [hSourceSlice] at hSourcePrefix
      have hTargetDepth :
          twoSteps (blockWord x start j) ≤
            criticalHeight j :=
        hLocalLe.trans hSourcePrefix
      have hTake :
          (blockWord x start len).take j =
            blockWord x start j := by
        simp [blockWord, List.take_take,
          Nat.min_eq_left (Nat.le_of_lt hjLt)]
      have hOddJ : oddSteps (blockWord x start j) = j :=
        oddSteps_blockWord x (Nat.le_of_lt hEndJ)
      apply (expanding_iff_twoPow_lt_threePow).2
      rw [hTake, hOddJ]
      have hPowLe :
          2 ^ twoSteps (blockWord x start j) ≤
            2 ^ criticalHeight j :=
        Nat.pow_le_pow_right
          (by omega : 0 < (2 : ℕ))
          hTargetDepth
      exact lt_of_le_of_lt hPowLe
        (criticalHeight_pow_lt_threePow hjPos)
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
      P hPrimitive hReduced
      B.length_pos hLenLt
  apply RecordBlock.ofMinimalAtRoof
    x B.length_pos B.end_le_terminal hMinimal hStartRoof
  · intro j hjPos _hjLt
    exact P.criticalHeight_below_chord hjPos
  · exact hDrop
  · intro hInterior
    have hEx := hEndExcess hInterior
    have hHeight :=
      x.height_eq_index_add_excess
        (Nat.le_of_lt hInterior)
    rw [hEx] at hHeight
    unfold criticalExcess at hHeight
    have hBase := index_le_criticalHeight (start + len)
    omega

/-! ## 2. whole RecordChain を同じ skeleton のまま移送する -/

/--
source RecordChain の flat skeleton と source profile の間に target `x` があれば、
同じ length list の RecordChain を target 上へ再構成できる。

lower flat bound は各 record boundary を critical roof に固定し、upper source bound は
各 local proper prefix が source local block より深くならないことを保証する。
-/
theorem RecordChain.of_between_flat_and_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {u x : FiberPoint P.oddCount P.twoDepth}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain u start lengths)
    (hStartPos : 0 < start)
    (hLower :
      ∀ j : ℕ,
        start ≤ j →
        j < P.oddCount →
        flatExcessForSkeleton start lengths j ≤
          x.excessAt j)
    (hUpper : FiberPoint.FerrersLe x u) :
    RecordChain x start lengths := by
  revert hStartPos hLower
  induction C with
  | @last start len B hTerminal =>
      intro hStartPos hLower
      have hStartLt : start < P.oddCount := by
        calc
          start < start + len :=
            Nat.lt_add_of_pos_right B.length_pos
          _ = P.oddCount := hTerminal
      have hFlatStart :
          flatExcessForSkeleton start [len] start =
            criticalExcess start :=
        flatExcessForSkeleton_at_start_of_chain
          (RecordChain.last B hTerminal)
      have hSourceStart :
          u.excessAt start = criticalExcess start :=
        excessAt_eq_criticalExcess_of_roof B.start_roof
      have hLowerStart := hLower start le_rfl hStartLt
      rw [hFlatStart] at hLowerStart
      have hUpperStart := hUpper ⟨start, hStartLt⟩
      change x.excessAt start ≤ u.excessAt start at hUpperStart
      have hStartExcess :
          x.excessAt start = criticalExcess start := by
        rw [hSourceStart] at hUpperStart
        omega
      have B' := recordBlock_of_between_flat_and_source
        P hPrimitive hReduced
        B hStartPos hUpper hStartExcess
        (by
          intro hInterior
          rw [hTerminal] at hInterior
          omega)
      exact RecordChain.last B' hTerminal
  | @cons start len rest B hInterior T ih =>
      intro hStartPos hLower
      have hFlatStart :
          flatExcessForSkeleton start (len :: rest) start =
            criticalExcess start :=
        flatExcessForSkeleton_at_start_of_chain
          (RecordChain.cons B hInterior T)
      have hSourceStart :
          u.excessAt start = criticalExcess start :=
        excessAt_eq_criticalExcess_of_roof B.start_roof
      have hLowerStart := hLower start le_rfl (by omega)
      rw [hFlatStart] at hLowerStart
      have hUpperStart := hUpper ⟨start, by omega⟩
      change x.excessAt start ≤ u.excessAt start at hUpperStart
      have hStartExcess :
          x.excessAt start = criticalExcess start := by
        rw [hSourceStart] at hUpperStart
        omega
      have hFlatEnd :
          flatExcessForSkeleton start (len :: rest) (start + len) =
            criticalExcess (start + len) := by
        rw [flatExcessForSkeleton_of_after_head
          start len rest le_rfl]
        exact flatExcessForSkeleton_at_start_of_chain T
      have hSourceEnd :
          u.excessAt (start + len) =
            criticalExcess (start + len) :=
        excessAt_eq_criticalExcess_of_roof
          (B.next_roof_if_interior hInterior)
      have hLowerEnd :=
        hLower (start + len) (by omega) hInterior
      rw [hFlatEnd] at hLowerEnd
      have hUpperEnd := hUpper ⟨start + len, hInterior⟩
      change
        x.excessAt (start + len) ≤
          u.excessAt (start + len) at hUpperEnd
      have hEndExcess :
          x.excessAt (start + len) =
            criticalExcess (start + len) := by
        rw [hSourceEnd] at hUpperEnd
        omega
      have B' := recordBlock_of_between_flat_and_source
        P hPrimitive hReduced
        B hStartPos hUpper hStartExcess
        (fun _ => hEndExcess)
      have hLowerTail :
          ∀ j : ℕ,
            start + len ≤ j →
            j < P.oddCount →
            flatExcessForSkeleton (start + len) rest j ≤
              x.excessAt j := by
        intro j hEndJ hjp
        have h := hLower j (by omega) hjp
        rw [flatExcessForSkeleton_of_after_head
          start len rest hEndJ] at h
        exact h
      exact RecordChain.cons B' hInterior
        (ih (by omega) hLowerTail)

/-! ## 3. Decoration interval は元の skeleton を完全保存する -/

/--
canonical flat top の proper profile は、元 `D.lengths` の flat skeleton そのもの。
全境界保持 pattern の粗視化が恒等であることを Bridge API から使う。
-/
theorem canonicalFlatTop_excessAt_eq_flatExcessForSkeleton
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {j : ℕ}
    (hjp : j < P.oddCount) :
    (canonicalFlatTop P hPrimitive hReduced u D).excessAt j =
      flatExcessForSkeleton 1 D.lengths j := by
  have h :=
    canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced u D
      (retainAllBoundaries D) hjp
  simpa [canonicalFlatTop, canonicalFlatPoint] using h

/--
## 主定理 1: interval の全中間点は元の Record skeleton を持つ。

`InDecorationInterval` の lower/upper Ferrers bounds だけで `D.chain` を target へ移送し、
whole FirstCrossing は interval definition からそのまま使う。
-/
theorem exists_recordDecomposition_same_lengths_of_inDecorationInterval
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth)
    (hx : InDecorationInterval P hPrimitive hReduced u D x) :
    ∃ E : RecordDecomposition x 1,
      E.lengths = D.lengths := by
  have hLower :
      ∀ j : ℕ,
        1 ≤ j →
        j < P.oddCount →
        flatExcessForSkeleton 1 D.lengths j ≤
          x.excessAt j := by
    intro j hj1 hjp
    have h := hx.1 ⟨j, hjp⟩
    change
      (canonicalFlatTop P hPrimitive hReduced u D).excessAt j ≤
        x.excessAt j at h
    rw [canonicalFlatTop_excessAt_eq_flatExcessForSkeleton
      P hPrimitive hReduced u D hjp] at h
    exact h
  have Cx : RecordChain x 1 D.lengths :=
    RecordChain.of_between_flat_and_source
      P hPrimitive hReduced
      D.chain (by omega) hLower hx.2.1
  let E : RecordDecomposition x 1 :=
    { lengths := D.lengths
      chain := Cx
      whole_firstCrossing := hx.2.2 }
  exact ⟨E, rfl⟩

/--
## 主定理 2: interval point の canonical Record skeleton は `D.lengths` に等しい。

存在だけでなく Record decomposition の canonicality を使い、target `x` 上で別の
RecordDecomposition を選んでも lengths は必ず元 skeleton に一致することを示す。
-/
theorem recordDecomposition_lengths_eq_source_of_inDecorationInterval
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth)
    (hx : InDecorationInterval P hPrimitive hReduced u D x)
    (E : RecordDecomposition x 1) :
    E.lengths = D.lengths := by
  obtain ⟨F, hF⟩ :=
    exists_recordDecomposition_same_lengths_of_inDecorationInterval
      P hPrimitive hReduced u D x hx
  calc
    E.lengths = F.lengths := E.lengths_unique F
    _ = D.lengths := hF

/-- interval point の pure `Skeleton` も source skeleton と exact に一致する。 -/
theorem skeleton_eq_source_of_inDecorationInterval
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth)
    (hx : InDecorationInterval P hPrimitive hReduced u D x)
    (E : RecordDecomposition x 1) :
    Skeleton.ofDecomposition E = Skeleton.ofDecomposition D := by
  apply Skeleton.eq_of_lengths_eq
  simpa using
    recordDecomposition_lengths_eq_source_of_inDecorationInterval
      P hPrimitive hReduced u D x hx E

/--
一つの actual one-cell decoration step の source / target は、どちらも元 `D.lengths` を
canonical Record skeleton として持つ。次段の proper-block support localization の入口。
-/
theorem ActualLocalFerrersCellDeletion.recordSkeleton_preserved
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    (∃ Ex : RecordDecomposition x 1, Ex.lengths = D.lengths) ∧
    (∃ Ey : RecordDecomposition y 1, Ey.lengths = D.lengths) := by
  exact ⟨
    exists_recordDecomposition_same_lengths_of_inDecorationInterval
      P hPrimitive hReduced u D x A.source_interval,
    exists_recordDecomposition_same_lengths_of_inDecorationInterval
      P hPrimitive hReduced u D y A.target_interval
  ⟩

/--
closure package: decoration interval は元 skeleton を保つ actual Record space である。
-/
structure DecorationIntervalSkeletonPreservationClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  every_interval_point_has_source_lengths :
    ∀ x : FiberPoint P.oddCount P.twoDepth,
      InDecorationInterval P hPrimitive hReduced u D x →
      ∃ E : RecordDecomposition x 1,
        E.lengths = D.lengths
  source_lengths_are_canonical :
    ∀ x : FiberPoint P.oddCount P.twoDepth,
      ∀ _hx : InDecorationInterval P hPrimitive hReduced u D x,
      ∀ E : RecordDecomposition x 1,
        E.lengths = D.lengths

/--
## Decoration Interval Skeleton Preservation closure theorem

actual→flat-top decoration interval の全中間点は、元 source decomposition と同じ
canonical record length skeleton を持つ。
-/
theorem decorationIntervalSkeletonPreservation_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    DecorationIntervalSkeletonPreservationClosed
      P hPrimitive hReduced u D := by
  refine {
    every_interval_point_has_source_lengths := ?_
    source_lengths_are_canonical := ?_
  }
  · intro x hx
    exact exists_recordDecomposition_same_lengths_of_inDecorationInterval
      P hPrimitive hReduced u D x hx
  · intro x hx E
    exact recordDecomposition_lengths_eq_source_of_inDecorationInterval
      P hPrimitive hReduced u D x hx E

end RecordFerrers
end Collatz2
