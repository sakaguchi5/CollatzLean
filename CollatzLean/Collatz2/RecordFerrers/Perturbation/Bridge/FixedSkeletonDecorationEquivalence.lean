import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.FixedSkeletonDecorationAssembly
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationReconstruction

/-!
# Record–Ferrers Perturbation / Fixed Skeleton Decoration Equivalence

`FixedSkeletonDecorationAssembly` では、固定した genuine record skeleton

  D.lengths = [r₁, r₂, ..., rₘ]

の各 `LocalDecoration rᵢ` を互いに独立に選んだ任意 tuple が、同じ primitive/reduced
fixed chord 上の genuine `FiberPoint` / `RecordDecomposition` として実現できることを示した。
これは product description の surjectivity 側である。

本ファイルでは逆向きを閉じる。

actual 側では decomposition witness 自体を状態に含めず、

  x : FiberPoint P.oddCount P.twoDepth
  ∃ E : RecordDecomposition x 1, E.lengths = D.lengths

だけを持つ subtype `FixedSkeletonSource` を用いる。decomposition witness は Prop 側に落ちるので、
同じ actual source を witness の選び方によって重複して数えない。

各 source から canonical record block list を取り出して `LocalDecorationTuple D.lengths` に戻し、
assembly と extraction が互いに逆であることを示す。

* tuple → source → tuple は、assembly 後の `blocks_eq` と Record decomposition canonicity。
* source → tuple → source は、同じ local block list から得る arithmetic decoration coordinates が
  一致することと既存 lossless reconstruction。

最終的に

  FixedSkeletonSource P u D ≃ LocalDecorationTuple D.lengths

を得る。従って「各 local decoration は独立に実現できる」だけでなく、fixed-skeleton
actual state space 自体が local decoration dependent product そのものである。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. concrete block list から dependent LocalDecorationTuple へ戻す -/

namespace LocalDecorationTuple

/--
`bs.map oddSteps = rs` を満たす genuine valid-minimal block list を、
そのまま `LocalDecorationTuple rs` に持ち上げる。

各 tuple 成分の `word` は対応する block word そのものであり、追加の choice はない。
-/
def ofBlocksWithLengths :
    (rs : List ℕ) →
    (bs : List Word) →
    bs.map oddSteps = rs →
    (∀ b ∈ bs, ValidMinimalBlock b) →
    LocalDecorationTuple rs
  | [], [], _, _ => .nil
  | [], b :: bs, hLengths, _ => by
      simp at hLengths
  | r :: rs, [], hLengths, _ => by
      simp at hLengths
  | r :: rs, b :: bs, hLengths, hValid => by
      simp only [List.map_cons, List.cons.injEq] at hLengths
      exact .cons
        { word := b
          validMinimal := hValid b (by simp)
          length_eq := hLengths.1 }
        (ofBlocksWithLengths
          rs
          bs
          hLengths.2
          (by
            intro c hc
            exact hValid c (by simp [hc])))

/-- `ofBlocksWithLengths` は入力 block list を exact に保持する。 -/
@[simp] theorem ofBlocksWithLengths_blocks
    (rs : List ℕ)
    (bs : List Word)
    (hLengths : bs.map oddSteps = rs)
    (hValid : ∀ b ∈ bs, ValidMinimalBlock b) :
    (ofBlocksWithLengths rs bs hLengths hValid).blocks = bs := by
  induction rs generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          simp at hLengths
  | cons r rs ih =>
      cases bs with
      | nil =>
          simp at hLengths
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at hLengths
          have hTailValid : ∀ c ∈ bs, ValidMinimalBlock c := by
            intro c hc
            exact hValid c (by simp [hc])
          simp only [ofBlocksWithLengths, blocks_cons, List.cons.injEq]
          exact ⟨trivial, ih bs hLengths.2 hTailValid⟩

/--
同じ index length list 上の two tuples は concrete block list が同じなら等しい。
local decoration 自体の extensionality と tuple の再帰構造だけを使う。
-/
theorem eq_of_blocks_eq
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (hBlocks : A.blocks = B.blocks) :
    A = B := by
  induction A with
  | nil =>
      cases B
      rfl
  | @cons r rs A T ih =>
      cases B with
      | cons B U =>
          simp only [blocks_cons, List.cons.injEq] at hBlocks
          have hHead : A = B := LocalDecoration.ext hBlocks.1
          subst B
          have hTail : T = U := ih hBlocks.2
          subst U
          rfl

end LocalDecorationTuple

/-! ## 2. fixed-skeleton actual source space -/

/--
元 decomposition `D` と同じ canonical record length skeleton を持つ actual sources。

状態本体は `FiberPoint` だけであり、decomposition witness は subtype property の Prop 側に置く。
従って同じ actual source は decomposition witness の違いで重複しない。
-/
def FixedSkeletonSource
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Type :=
  {x : FiberPoint P.oddCount P.twoDepth //
    ∃ E : RecordDecomposition x 1,
      E.lengths = D.lengths}

namespace FixedSkeletonSource

/-- fixed-skeleton source が持つ actual FiberPoint。 -/
def point
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X : FixedSkeletonSource P u D) :
    FiberPoint P.oddCount P.twoDepth :=
  X.1

/-- source property から decomposition witness を一つ選ぶ。 -/
noncomputable def decomposition
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X : FixedSkeletonSource P u D) :
    RecordDecomposition X.1 1 :=
  Classical.choose X.2

/-- chosen decomposition は元 `D.lengths` と同じ skeleton を持つ。 -/
theorem decomposition_lengths
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X : FixedSkeletonSource P u D) :
    X.decomposition.lengths = D.lengths :=
  Classical.choose_spec X.2

/--
actual source の chosen decomposition block list を dependent local-decoration tuple へ戻す。
Record decomposition の local blocks は全て genuine valid minimal blocks なので choice は不要。
-/
noncomputable def toLocalDecorationTuple
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X : FixedSkeletonSource P u D) :
    LocalDecorationTuple D.lengths :=
  LocalDecorationTuple.ofBlocksWithLengths
    D.lengths
    X.decomposition.blocks
    (X.decomposition.blocks_oddSteps_eq_lengths.trans X.decomposition_lengths)
    X.decomposition.blocks_validMinimal

/-- extracted tuple の concrete blocks は chosen decomposition の blocks そのもの。 -/
@[simp] theorem toLocalDecorationTuple_blocks
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X : FixedSkeletonSource P u D) :
    X.toLocalDecorationTuple.blocks = X.decomposition.blocks := by
  unfold toLocalDecorationTuple
  apply LocalDecorationTuple.ofBlocksWithLengths_blocks

/--
chosen witness 以外の decomposition を使っても extracted block list は同じ。
これは `RecordDecomposition.blocks_unique` による decomposition-independence。
-/
theorem toLocalDecorationTuple_blocks_eq_any_decomposition
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X : FixedSkeletonSource P u D)
    (E : RecordDecomposition X.1 1) :
    X.toLocalDecorationTuple.blocks = E.blocks := by
  rw [X.toLocalDecorationTuple_blocks]
  exact X.decomposition.blocks_unique E

end FixedSkeletonSource

/-! ## 3. tuple から fixed-skeleton source へ戻す -/

/--
任意 local-decoration tuple を既存 explicit assembly で actual source に戻す。
result decomposition が `D.lengths` を持つことが subtype membership を与える。
-/
def fixedSkeletonSourceOfTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    FixedSkeletonSource P u D := by
  let A := assembleFixedSkeleton P hPrimitive hReduced u D T
  exact ⟨A.point, ⟨A.decomposition, A.lengths_eq⟩⟩

@[simp] theorem fixedSkeletonSourceOfTuple_point
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    (fixedSkeletonSourceOfTuple
      P hPrimitive hReduced u D T).1 =
      (assembleFixedSkeleton P hPrimitive hReduced u D T).point := by
  rfl

/-! ## 4. tuple → source → tuple -/

/--
assembly した source から local tuple を再抽出すると元 tuple に exact に戻る。

subtype property が選ぶ decomposition は assembly が作った witness と同一とは限らないが、
同じ actual source / start の record decomposition は block list が canonical なので問題ない。
-/
theorem localDecorationTuple_roundtrip
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (T : LocalDecorationTuple D.lengths) :
    (fixedSkeletonSourceOfTuple
      P hPrimitive hReduced u D T).toLocalDecorationTuple = T := by
  apply LocalDecorationTuple.eq_of_blocks_eq
  let A := assembleFixedSkeleton P hPrimitive hReduced u D T
  let X := fixedSkeletonSourceOfTuple P hPrimitive hReduced u D T
  have hChosen :
      X.decomposition.blocks = A.decomposition.blocks := by
    exact X.decomposition.blocks_unique A.decomposition
  calc
    X.toLocalDecorationTuple.blocks = X.decomposition.blocks :=
      X.toLocalDecorationTuple_blocks
    _ = A.decomposition.blocks := hChosen
    _ = T.blocks := A.blocks_eq

/-! ## 5. source → tuple → source -/

/--
source から extracted tuple を assembly し直すと元 source に exact に戻る。

assembly decomposition と元 source の chosen decomposition は同じ concrete block list を持つ。
従って `(length, local affineConst)` coordinates が一致し、既存 lossless reconstruction が
full `FiberPoint` equality を与える。
-/
theorem fixedSkeletonSource_roundtrip
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    fixedSkeletonSourceOfTuple
      P hPrimitive hReduced u D X.toLocalDecorationTuple = X := by
  let T := X.toLocalDecorationTuple
  let A := assembleFixedSkeleton P hPrimitive hReduced u D T
  let E := X.decomposition
  have hTupleBlocks : T.blocks = E.blocks := by
    dsimp [T, E]
    exact X.toLocalDecorationTuple_blocks
  have hBlocks : A.decomposition.blocks = E.blocks := by
    calc
      A.decomposition.blocks = T.blocks := A.blocks_eq
      _ = E.blocks := hTupleBlocks
  have hCoord :
      arithmeticDecorationCoordinates A.decomposition =
        arithmeticDecorationCoordinates E := by
    unfold arithmeticDecorationCoordinates
    rw [
      A.decomposition.translationCoordinates_eq_blockCoordinateMap,
      E.translationCoordinates_eq_blockCoordinateMap,
      hBlocks
    ]
  have hPoint : A.point = X.1 :=
    source_eq_of_same_arithmeticDecorationCoordinates
      A.point X.1 A.decomposition E hCoord
  apply Subtype.ext
  change A.point = X.1
  exact hPoint

/-! ## 6. exact equivalence -/

/--
## Fixed Skeleton Decoration Equivalence 主定理

primitive + StripReduced fixed chord 上で、元 decomposition `D` と同じ record length skeleton を
持つ actual source space は、各 block length に沿った local decoration dependent product と
exact に同値。

これは assembly の「任意 tuple が実現できる」という全射性を、actual source の lossless
reconstruction と組み合わせて state-space equivalence に昇格したもの。
-/
noncomputable def fixedSkeletonSourceEquiv
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FixedSkeletonSource P u D ≃
      LocalDecorationTuple D.lengths where
  toFun := fun X => X.toLocalDecorationTuple
  invFun := fun T =>
    fixedSkeletonSourceOfTuple P hPrimitive hReduced u D T
  left_inv := fixedSkeletonSource_roundtrip
    P hPrimitive hReduced u D
  right_inv := localDecorationTuple_roundtrip
    P hPrimitive hReduced u D

/-- extraction map は injective: local decoration tuple が同じなら actual source も同じ。 -/
theorem fixedSkeletonSource_eq_of_same_localDecorationTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {X Y : FixedSkeletonSource P u D}
    (hTuple : X.toLocalDecorationTuple = Y.toLocalDecorationTuple) :
    X = Y := by
  exact (fixedSkeletonSourceEquiv
    P hPrimitive hReduced u D).injective hTuple

/-- assembly map も injective: 異なる local tuples は異なる actual sources を与える。 -/
theorem fixedSkeletonAssembly_injective
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {T U : LocalDecorationTuple D.lengths}
    (hSource :
      fixedSkeletonSourceOfTuple P hPrimitive hReduced u D T =
        fixedSkeletonSourceOfTuple P hPrimitive hReduced u D U) :
    T = U := by
  have h := congrArg
    (fun X : FixedSkeletonSource P u D => X.toLocalDecorationTuple)
    hSource
  rw [
    localDecorationTuple_roundtrip
      P hPrimitive hReduced u D T,
    localDecorationTuple_roundtrip
      P hPrimitive hReduced u D U
  ] at h
  exact h

/-- equivalence closure package。 -/
structure FixedSkeletonDecorationEquivalenceClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  extraction_injective :
    Function.Injective
      (fun X : FixedSkeletonSource P u D =>
        X.toLocalDecorationTuple)
  extraction_surjective :
    Function.Surjective
      (fun X : FixedSkeletonSource P u D =>
        X.toLocalDecorationTuple)

/-- fixed-skeleton actual state space と local-decoration product の bijectivity closure。 -/
theorem fixedSkeletonDecorationEquivalence_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FixedSkeletonDecorationEquivalenceClosed
      P hPrimitive hReduced u D := by
  let e := fixedSkeletonSourceEquiv P hPrimitive hReduced u D
  exact {
    extraction_injective := e.injective
    extraction_surjective := e.surjective
  }

end RecordFerrers
end Collatz2
