import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.DecorationIntervalSkeletonPreservation
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockReplacement

/-!
# Record–Ferrers Perturbation / Proper Local Decoration Support

`DecorationIntervalSkeletonPreservation` により、actual→flat-top decoration interval の
全中間点は元 source と同じ canonical record length skeleton を持つことが分かった。

本ファイルでは一つの `ActualLocalFerrersCellDeletion` をさらに局所化する。

主張は次の通り。

* one-cell unit cover では変化する Ferrers column はただ一つで、その高さ差も exact に 1。
* source / target の同一 skeleton の RecordChain を並行してたどると、その唯一の column を
  strict interior に含む共通 record block が存在する。
* 従って one-cell deletion の displacement support は whole fixed fiber ではなく、その
  genuine record block の open interval 内に完全に収まる。

これにより `ActualLocalFerrersCellDeletion` の "Local" は、単なる flat-top interval 内
という意味だけでなく、canonical record block 内の compact support という意味でも
formal に正当化される。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. unit cover の唯一変化 column -/

namespace FerrersShape.IsUnitCover

/--
unit cover `A ≤ B` では、exact に一つの column だけが 1 増え、他は全て一致する。
-/
theorem exists_unique_changed_column
    {p : ℕ}
    {A B : FerrersShape p}
    (h : FerrersShape.IsUnitCover A B) :
    ∃ i : Fin p,
      A.column i + 1 = B.column i ∧
      ∀ j : Fin p, j ≠ i → A.column j = B.column j := by
  have hStrict : ∃ i : Fin p, A.column i < B.column i := by
    by_contra hNo
    have hBA : B.Le A := by
      intro i
      by_contra hnot
      have hi : A.column i < B.column i := by omega
      exact hNo ⟨i, hi⟩
    have hEq : A = B := FerrersShape.le_antisymm h.1 hBA
    have hDist := h.2
    rw [hEq] at hDist
    simp at hDist
  rcases hStrict with ⟨i, hiStrict⟩
  let f : ℕ → ℕ := fun k =>
    (A.atNat k - B.atNat k) + (B.atNat k - A.atNat k)
  have hiMem : i.1 ∈ Finset.range p := Finset.mem_range.mpr i.isLt
  have hTotal :
      Finset.sum (Finset.range p) f = 1 := by
    simpa [f, FerrersShape.distance] using h.2
  have hiTermPos : 0 < f i.1 := by
    dsimp [f]
    simp [FerrersShape.atNat, i.isLt]
    omega
  have hiTermLe : f i.1 ≤ Finset.sum (Finset.range p) f :=
    Finset.single_le_sum_of_canonicallyOrdered
      (f := f) hiMem
  have hiTerm : f i.1 = 1 := by
    rw [hTotal] at hiTermLe
    omega
  have hSplit :=
    Finset.sum_erase_add (Finset.range p) f hiMem
  have hEraseZero :
      Finset.sum ((Finset.range p).erase i.1) f = 0 := by
    have hSplit' :
        Finset.sum ((Finset.range p).erase i.1) f + 1 = 1 := by
      simpa [hiTerm, hTotal] using hSplit
    omega
  have hiExact : A.column i + 1 = B.column i := by
    have hLe := h.1 i
    dsimp [f] at hiTerm
    simp [FerrersShape.atNat, i.isLt] at hiTerm
    omega
  refine ⟨i, hiExact, ?_⟩
  intro j hji
  have hValNe : j.1 ≠ i.1 := by
    intro hEq
    apply hji
    exact Fin.ext hEq
  have hjMem : j.1 ∈ (Finset.range p).erase i.1 := by
    simp [hValNe, j.isLt]
  have hjTermLe :
      f j.1 ≤ Finset.sum ((Finset.range p).erase i.1) f :=
    Finset.single_le_sum_of_canonicallyOrdered
      (f := f) hjMem
  rw [hEraseZero] at hjTermLe
  have hjZero : f j.1 = 0 := by omega
  have hLe := h.1 j
  dsimp [f] at hjZero
  simp [FerrersShape.atNat, j.isLt] at hjZero
  omega

end FerrersShape.IsUnitCover

/-! ## 2. Ferrers column equality から displacement equality へ -/

/-- proper cut の Ferrers column が一致すれば signed height displacement は 0。 -/
theorem profileDisplacement_eq_zero_of_ferrersColumn_eq
    {p H : ℕ}
    {x y : FiberPoint p H}
    {k : ℕ}
    (hk : k < p)
    (hColumn :
      x.toFerrersShape.column ⟨k, hk⟩ =
        y.toFerrersShape.column ⟨k, hk⟩) :
    profileDisplacement x y k = 0 := by
  have hx := x.height_eq_index_add_excess (Nat.le_of_lt hk)
  have hy := y.height_eq_index_add_excess (Nat.le_of_lt hk)
  have hExcess : x.excessAt k = y.excessAt k := by
    change x.excessAt k = y.excessAt k at hColumn
    exact hColumn
  unfold profileDisplacement
  rw [hx, hy, hExcess]
  simp

/-! ## 3. 同一 skeleton の二 RecordChain で changed column を含む block を探す -/

/--
二つの同じ位置・同じ長さの record block について、
Ferrers column が strict に異なる位置は共通 block start ではない。

両 block の start height は同じ critical roof に固定されるため、
その位置の excess、従って Ferrers column も一致する。
-/
theorem RecordBlock.changed_column_ne_common_start
    {p H : ℕ}
    {x y : FiberPoint p H}
    {start len : ℕ}
    (Bx : RecordBlock x start len)
    (By : RecordBlock y start len)
    {k : Fin p}
    (hChanged :
      y.toFerrersShape.column k < x.toFerrersShape.column k) :
    k.1 ≠ start := by
  have hStartLt : start < p := by
    calc
      start < start + len :=
        Nat.lt_add_of_pos_right Bx.length_pos
      _ ≤ p := Bx.end_le_terminal
  have hxStart :=
    x.height_eq_index_add_excess
      (Nat.le_of_lt hStartLt)
  have hyStart :=
    y.height_eq_index_add_excess
      (Nat.le_of_lt hStartLt)
  rw [Bx.start_roof] at hxStart
  rw [By.start_roof] at hyStart
  intro hkEq
  have hChanged' := hChanged
  change
    y.excessAt k.1 < x.excessAt k.1
    at hChanged'
  rw [hkEq] at hChanged'
  omega

/--
同じ length skeleton を持つ二つの RecordChain について、
ある Ferrers column が strict に異なるなら、
その column を strict interior に含む共通 record block が存在する。

対応する record boundaries は両 chain でともに critical roof 上にあるため、
changed column は共通 boundary にはなれない。
従って chain を左から走査すると、changed column は一意の共通 block の
strict interior に入る。
-/
theorem RecordChain.exists_common_block_strictly_containing_changed_column
    {p H : ℕ}
    {x y : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (Cx : RecordChain x start lengths)
    (Cy : RecordChain y start lengths)
    {k : Fin p}
    (hkStart : start ≤ k.1)
    (hChanged :
      y.toFerrersShape.column k < x.toFerrersShape.column k) :
    ∃ a len : ℕ,
      RecordBlock x a len ∧
      RecordBlock y a len ∧
      a < k.1 ∧
      k.1 < a + len := by
  induction Cx generalizing y with
  | @last start len Bx hTerminal =>
      cases Cy with
      | last By _hTerminal' =>
          have hkNeStart :
              k.1 ≠ start :=
            RecordBlock.changed_column_ne_common_start
              Bx By hChanged
          have hkLtStop :
              k.1 < start + len := by
            rw [hTerminal]
            exact k.isLt
          exact ⟨
            start,
            len,
            Bx,
            By,
            by omega,
            hkLtStop
          ⟩
      | cons By _hInterior' Ty =>
          cases Ty
  | @cons start len rest Bx hInterior Tx ih =>
      cases Cy with
      | last By _hTerminal' =>
          cases Tx
      | cons By _hInterior' Ty =>
          have hkNeStart :
              k.1 ≠ start :=
            RecordBlock.changed_column_ne_common_start
              Bx By hChanged
          by_cases hkHead : k.1 < start + len
          · exact ⟨
              start,
              len,
              Bx,
              By,
              by omega,
              hkHead
            ⟩
          · have hkTail :
                start + len ≤ k.1 := by
              omega
            exact ih Ty hkTail hChanged



/-! ## 4. one-cell edge を genuine record block support へ縮める -/

namespace ActualLocalFerrersCellDeletion

/--
one-cell actual deletion で変化する唯一の Ferrers column。
source `x` から target `y` への downward edge なので target column が exactly 1 小さい。
-/
theorem exists_unique_changed_column
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    ∃ k : Fin P.oddCount,
      y.toFerrersShape.column k + 1 = x.toFerrersShape.column k ∧
      ∀ j : Fin P.oddCount, j ≠ k →
        y.toFerrersShape.column j = x.toFerrersShape.column j := by
  exact A.unit_cover.exists_unique_changed_column

/--
## 主定理

任意 one-cell actual decoration deletion は、その唯一の changed column を strict interior に
含む genuine canonical record block の open interval に support を持つ。

特に whole-fiber `[0,p]` specialization ではなく、source / target の両方で実際に
`RecordBlock` となっている proper block interval 上の `BlockReplacement` を得る。
-/
theorem exists_proper_recordBlock_support
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    ∃ k : Fin P.oddCount,
      ∃ a len : ℕ,
        RecordBlock x a len ∧
        RecordBlock y a len ∧
        a < k.1 ∧
        k.1 < a + len ∧
        BlockReplacement x y a (a + len) := by
  rcases A.exists_unique_changed_column with
    ⟨k, hkExact, hkOnly⟩
  have hChanged :
      y.toFerrersShape.column k < x.toFerrersShape.column k := by
    omega
  rcases A.recordSkeleton_preserved with
    ⟨⟨Ex, hEx⟩, ⟨Ey, hEy⟩⟩
  have hLenXY : Ey.lengths = Ex.lengths := by
    exact hEy.trans hEx.symm
  have Cy : RecordChain y 1 Ex.lengths := by
    have h := Ey.chain
    rw [hLenXY] at h
    exact h
  have hkPos : 0 < k.1 := by
    by_contra hnot
    have hk0 : k.1 = 0 := by omega
    have hZeroY := y.toFerrersShape_first_zero P.oddCount_pos
    have hZeroX := x.toFerrersShape_first_zero P.oddCount_pos
    have hkFin : k = ⟨0, P.oddCount_pos⟩ := by
      apply Fin.ext
      exact hk0
    rw [hkFin, hZeroY, hZeroX] at hChanged
    omega
  rcases RecordChain.exists_common_block_strictly_containing_changed_column
      Ex.chain Cy (k := k) (by omega) hChanged with
    ⟨a, len, Bx, By, hak, hkb⟩
  have hReplacement : BlockReplacement x y a (a + len) := by
    refine {
      start_lt_stop := Nat.lt_add_of_pos_right Bx.length_pos
      stop_le_terminal := Bx.end_le_terminal
      outside := ?_
    }
    intro j hjp hOutside
    by_cases hjTerm : j = P.oddCount
    · subst j
      exact profileDisplacement_terminal x y
    · have hjLt : j < P.oddCount := by omega
      have hjNeKVal : j ≠ k.1 := by
        intro hEq
        subst j
        rcases hOutside with hLeft | hRight
        · omega
        · omega
      have hjNeK : (⟨j, hjLt⟩ : Fin P.oddCount) ≠ k := by
        intro hEq
        exact hjNeKVal (congrArg Fin.val hEq)
      have hCol := hkOnly ⟨j, hjLt⟩ hjNeK
      apply profileDisplacement_eq_zero_of_ferrersColumn_eq hjLt
      exact hCol.symm
  exact ⟨k, a, len, Bx, By, hak, hkb, hReplacement⟩

/--
proper support の存在だけを簡潔に使う公開版。
-/
theorem blockReplacement_on_some_recordBlock
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    ∃ a len : ℕ,
      RecordBlock x a len ∧
      RecordBlock y a len ∧
      BlockReplacement x y a (a + len) := by
  rcases A.exists_proper_recordBlock_support with
    ⟨k, a, len, Bx, By, hak, hkb, R⟩
  exact ⟨a, len, Bx, By, R⟩

end ActualLocalFerrersCellDeletion

/-! ## 5. closure package -/

/-- proper record-block localization の closure data。 -/
structure ProperLocalDecorationSupportClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  every_one_cell_edge_is_record_local :
    ∀ {x y : FiberPoint P.oddCount P.twoDepth},
      ActualLocalFerrersCellDeletion
          P hPrimitive hReduced u D x y →
        ∃ k : Fin P.oddCount,
          ∃ a len : ℕ,
            RecordBlock x a len ∧
            RecordBlock y a len ∧
            a < k.1 ∧
            k.1 < a + len ∧
            BlockReplacement x y a (a + len)

/--
## Proper Local Decoration Support closure theorem

actual→flat-top one-cell deletion の各 edge は、唯一の changed Ferrers column を含む
canonical record block 内だけに compact support を持つ genuine `BlockReplacement` である。
-/
theorem properLocalDecorationSupport_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ProperLocalDecorationSupportClosed
      P hPrimitive hReduced u D := by
  refine {
    every_one_cell_edge_is_record_local := ?_
  }
  intro x y A
  exact A.exists_proper_recordBlock_support

end RecordFerrers
end Collatz2
