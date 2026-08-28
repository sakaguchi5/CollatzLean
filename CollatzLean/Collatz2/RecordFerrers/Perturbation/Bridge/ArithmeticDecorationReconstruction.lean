import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationCoordinates

/-!
# Record–Ferrers Perturbation / Arithmetic Decoration Reconstruction

`ArithmeticDecorationCoordinates` では、cut 1 の genuine record decomposition が持つ
fine arithmetic data を

  [(record length, local affineConst), ...]

という canonical coordinate list へ移し、その weighted evaluator が source / flat-top
の affine translation を exact に再構成することを示した。

本ファイルでは、その coordinate list が単なる invariant ではなく、fixed `(p,H)` fiber
上の actual source を一意に決める lossless encoding であることを閉じる。

重要なのは cut 1 である。coordinate list は `word.drop 1` を record blocks に分解した
局所情報なので、先頭 exponent 自体は直接は含まない。しかし fixed fiber では
`twoSteps word = H` が固定されるため、suffix word が復元できれば残る先頭 exponent も
一意に決まる。

証明の流れは

  same arithmetic coordinates
      -> same local valid minimal blocks
      -> same `word.drop 1`
      -> same first exponent by fixed total two-depth
      -> same full word
      -> same FiberPoint

である。

従って `arithmeticDecorationCoordinates` は、decomposition witness に依存せず、かつ
source を区別する complete local arithmetic invariant になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. record block words は valid minimal blocks -/

/-
PublicAPI.leanに
theorem blocks_valid_public
theorem blocks_validMinimal
などが既に存在する
-/

/-! ## 2. coordinate equality は record suffix block 列を exact に復元 -/

/--
同じ arithmetic decoration coordinate list を持つ二つの cut 1 decomposition は、
source が異なっていても local block word 列そのものが一致する。

各 coordinate `(r,B)` が valid minimal block を一意に決める既存 local reconstruction の
list 版を Bridge に持ち上げたもの。
-/
theorem blocks_eq_of_same_arithmeticDecorationCoordinates
    {p H : ℕ}
    {u v : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hCoord :
      arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E) :
    D.blocks = E.blocks := by
  have hMap :
      D.blocks.map blockTranslationCoordinate =
        E.blocks.map blockTranslationCoordinate := by
    have hTrans : D.translationCoordinates = E.translationCoordinates := by
      simpa [arithmeticDecorationCoordinates] using hCoord
    rw [
      D.translationCoordinates_eq_blockCoordinateMap,
      E.translationCoordinates_eq_blockCoordinateMap
    ] at hTrans
    exact hTrans
  exact validMinimalBlocks_eq_of_coordinateMap_eq
    D.blocks_validMinimal E.blocks_validMinimal hMap

/-- coordinate equality は cut 1 suffix word `drop 1` を exact に復元する。 -/
theorem suffix_eq_of_same_arithmeticDecorationCoordinates
    {p H : ℕ}
    {u v : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hCoord :
      arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E) :
    u.word.drop 1 = v.word.drop 1 := by
  have hBlocks : D.blocks = E.blocks :=
    blocks_eq_of_same_arithmeticDecorationCoordinates D E hCoord
  calc
    u.word.drop 1 = D.blocks.flatten := D.blocks_flatten_eq_drop.symm
    _ = E.blocks.flatten := congrArg List.flatten hBlocks
    _ = v.word.drop 1 := E.blocks_flatten_eq_drop

/-! ## 3. fixed fiber が欠けた first exponent を復元 -/

/--
同じ fixed `(p,H)` fiber では、cut 1 suffix が一致すれば full word も一致する。

`RecordDecomposition _ 1` の存在から `1 ≤ p`。したがって両 word は nonempty。
残る先頭 exponent は fixed total depth `H` と共通 suffix depth から一意に決まる。
-/
theorem source_word_eq_of_same_suffix
    {p H : ℕ}
    (u v : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hDrop : u.word.drop 1 = v.word.drop 1) :
    u.word = v.word := by
  have hTwo : twoSteps u.word = twoSteps v.word :=
    u.twoSteps_eq.trans v.twoSteps_eq.symm
  cases hu : u.word with
  | nil =>
      have hStart := D.start_le_terminal
      have hOdd := u.oddSteps_eq
      rw [hu] at hOdd
      simp [oddSteps] at hOdd
      omega
  | cons a us =>
      cases hv : v.word with
      | nil =>
          have hStart := E.start_le_terminal
          have hOdd := v.oddSteps_eq
          rw [hv] at hOdd
          simp [oddSteps] at hOdd
          omega
      | cons b vs =>
          have hTail : us = vs := by
            have hDrop' := hDrop
            rw [hu, hv] at hDrop'
            simpa using hDrop'
          have hTwo' := hTwo
          rw [hu, hv] at hTwo'
          simp only [twoSteps_cons] at hTwo'
          rw [hTail] at hTwo'
          have hHead : a = b := by
            omega
          rw [hHead, hTail]

/--
## 主定理 1: fine arithmetic coordinates は full source word を lossless に決める

coordinate list で local valid minimal blocks を復号し、fixed total depth で先頭 exponent を
補うことで full actual word が一意に復元される。
-/
theorem source_word_eq_of_same_arithmeticDecorationCoordinates
    {p H : ℕ}
    (u v : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hCoord :
      arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E) :
    u.word = v.word := by
  apply source_word_eq_of_same_suffix u v D E
  exact suffix_eq_of_same_arithmeticDecorationCoordinates D E hCoord

/--
## 主定理 2: fine arithmetic coordinates は actual FiberPoint 自体を lossless に決める

fixed fiber 上で coordinate equality は source equality と同値になる方向の核心。
-/
theorem source_eq_of_same_arithmeticDecorationCoordinates
    {p H : ℕ}
    (u v : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hCoord :
      arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E) :
    u = v := by
  have hWord : u.word = v.word :=
    source_word_eq_of_same_arithmeticDecorationCoordinates
      u v D E hCoord
  cases u with
  | mk uw huValid huOdd huTwo =>
      cases v with
      | mk vw hvValid hvOdd hvTwo =>
          dsimp at hWord
          cases hWord
          rfl

/--
coordinate equality と source equality の exact characterization。

reverse directionでは、同一 source の decomposition witness を変えても coordinates が
変わらない既存 canonicity を使う。
-/
theorem arithmeticDecorationCoordinates_eq_iff_source_eq
    {p H : ℕ}
    (u v : FiberPoint p H)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1) :
    arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E ↔
      u = v := by
  constructor
  · intro hCoord
    exact source_eq_of_same_arithmeticDecorationCoordinates
      u v D E hCoord
  · intro huv
    subst v
    exact arithmeticDecorationCoordinates_independent_of_decomposition D E

/-! ## 4. decorated Boolean state も actual source を混同しない -/

/--
どの Boolean vertices を比較しても、decorated state 全体が一致するなら actual sources は
一致する。第二成分の fine arithmetic coordinate vector が source を完全に識別するため。
-/
theorem source_eq_of_same_arithmeticDecoratedBooleanState
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (R : RetainedBoundaryPattern D)
    (S : RetainedBoundaryPattern E)
    (hState :
      arithmeticDecoratedBooleanState
          P hPrimitive hReduced u D R =
        arithmeticDecoratedBooleanState
          P hPrimitive hReduced v E S) :
    u = v := by
  apply source_eq_of_same_arithmeticDecorationCoordinates u v D E
  have hSecond := congrArg Prod.snd hState
  simpa [arithmeticDecoratedBooleanState] using hSecond

/--
特に canonical flat top vertex に fine arithmetic coordinates を載せた state は
actual source の lossless signature。
-/
theorem source_eq_of_same_arithmeticDecoratedFlatTopState
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hState :
      arithmeticDecoratedBooleanState
          P hPrimitive hReduced u D (retainAllBoundaries D) =
        arithmeticDecoratedBooleanState
          P hPrimitive hReduced v E (retainAllBoundaries E)) :
    u = v := by
  exact source_eq_of_same_arithmeticDecoratedBooleanState
    P hPrimitive hReduced u v D E
    (retainAllBoundaries D) (retainAllBoundaries E) hState

/-! ## 5. closure package -/

/--
Arithmetic Decoration Reconstruction 層で閉じた lossless 性をまとめる。
-/
structure ArithmeticDecorationReconstructionClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  decomposition_canonical :
    ∀ E : RecordDecomposition u 1,
      arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E
  source_lossless :
    ∀ (v : FiberPoint P.oddCount P.twoDepth)
      (E : RecordDecomposition v 1),
      arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E →
      u = v
  decorated_state_lossless :
    ∀ (v : FiberPoint P.oddCount P.twoDepth)
      (E : RecordDecomposition v 1)
      (R : RetainedBoundaryPattern D)
      (S : RetainedBoundaryPattern E),
      arithmeticDecoratedBooleanState
          P hPrimitive hReduced u D R =
        arithmeticDecoratedBooleanState
          P hPrimitive hReduced v E S →
      u = v

/--
## Arithmetic Decoration Reconstruction closure theorem

cut 1 arithmetic coordinates は decomposition-independent であり、同じ fixed fiber 上の
actual source を一意に決める。さらに coordinates を固定したまま Boolean geometry を
動かす decorated state も source 情報を失わない。
-/
theorem arithmeticDecorationReconstruction_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ArithmeticDecorationReconstructionClosed
      P hPrimitive hReduced u D := by
  refine {
    decomposition_canonical := ?_
    source_lossless := ?_
    decorated_state_lossless := ?_
  }
  · intro E
    exact arithmeticDecorationCoordinates_independent_of_decomposition D E
  · intro v E hCoord
    exact source_eq_of_same_arithmeticDecorationCoordinates
      u v D E hCoord
  · intro v E R S hState
    exact source_eq_of_same_arithmeticDecoratedBooleanState
      P hPrimitive hReduced u v D E R S hState

end RecordFerrers
end Collatz2
