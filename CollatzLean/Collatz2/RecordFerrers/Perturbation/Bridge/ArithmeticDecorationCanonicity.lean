import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationBridge
import CollatzLean.Collatz2.RecordFerrers.Record.Canonicality
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.FerrersReconstruction

/-!
# Record–Ferrers Perturbation / Arithmetic Decoration Canonicity

`ArithmeticDecorationBridge` では actual source を

  actual source
      |
      | decorationGap を外部に保持
      v
  canonical flat top
      |
      | Boolean boundary geometry
      v
  absolute bottom

という三層へ exact に分離した。

本ファイルでは、この上段の射が `RecordDecomposition` の任意選択に
依存しないことを閉じる。

決定的なのは既存の canonical record theory である。

* `RecordBlock.length_unique`:
  同じ point / anchor から出る genuine RecordBlock の長さは一意。
* `RecordChain.lengths_unique`:
  同じ point / start の genuine RecordChain の length list は一意。
* `RecordDecomposition.lengths_unique`:
  同じ actual source の record decomposition は canonical length skeleton を持つ。

一方 P30 の canonical flat representative は、その coarse length skeleton だけから
Ferrers profile を直接構成している。

したがって全境界保持の場合、

  canonicalFlatTop
    = flatExcessForSkeleton 1 D.lengths

であり、`D.lengths` 自体が canonical なので `canonicalFlatTop` も canonical になる。

ここからさらに

* `decorationGap`
* `boundaryGap`
* arithmetic decoration signature
* geometric decorated-flat signature

がすべて decomposition-independent であることを示す。

最後に fixed `(p,H)` fiber では genuine `affineConst` が `FiberPoint` を一意に決める
既存 reconstruction theorem を用い、

  canonical flat geometry + external arithmetic decoration

が actual source を lossless に復元することを閉じる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. canonical flat top は length skeleton だけで決まる -/

/--
二つの actual sources が同じ fixed fiber にあり、その cut 1 record decomposition の
length skeleton が一致するなら、両者から得る canonical flat top は exact に一致する。

重要なのは `u = v` を仮定していない点である。
`canonicalFlatTop` は source の local decoration ではなく、
canonical record length skeleton だけを見ている。
-/
theorem canonicalFlatTop_eq_of_lengths_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hLengths : D.lengths = E.lengths) :
    canonicalFlatTop P hPrimitive hReduced u D =
      canonicalFlatTop P hPrimitive hReduced v E := by
  apply FiberPoint.toFerrersShape_injective
  apply FerrersShape.ext
  intro i
  change
    (canonicalFlatTop P hPrimitive hReduced u D).excessAt i.1 =
      (canonicalFlatTop P hPrimitive hReduced v E).excessAt i.1
  simp only [canonicalFlatTop, canonicalFlatPoint]
  rw [
    canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced u D (retainAllBoundaries D) i.isLt,
    canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced v E (retainAllBoundaries E) i.isLt,
    coarsenedLengthsFor_retainAllBoundaries D,
    coarsenedLengthsFor_retainAllBoundaries E,
    hLengths
  ]

/--
同じ actual source に対する `canonicalFlatTop` は
`RecordDecomposition` の選択に依存しない。

`RecordDecomposition.lengths_unique` と
`canonicalFlatTop_eq_of_lengths_eq` を接続した主 canonicity theorem。
-/
theorem canonicalFlatTop_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    canonicalFlatTop P hPrimitive hReduced u D =
      canonicalFlatTop P hPrimitive hReduced u E := by
  exact
    canonicalFlatTop_eq_of_lengths_eq
      P hPrimitive hReduced u u D E
      (RecordDecomposition.lengths_unique D E)

/-- canonical flat top の underlying word も decomposition-independent。 -/
theorem canonicalFlatTop_word_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    (canonicalFlatTop P hPrimitive hReduced u D).word =
      (canonicalFlatTop P hPrimitive hReduced u E).word := by
  exact congrArg
    (fun x : FiberPoint P.oddCount P.twoDepth => x.word)
    (canonicalFlatTop_independent_of_decomposition
      P hPrimitive hReduced u D E)

/-- canonical flat top の genuine `affineConst` も decomposition-independent。 -/
theorem canonicalFlatTop_affineConst_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    affineConst (canonicalFlatTop P hPrimitive hReduced u D).word =
      affineConst (canonicalFlatTop P hPrimitive hReduced u E).word := by
  exact congrArg affineConst
    (canonicalFlatTop_word_independent_of_decomposition
      P hPrimitive hReduced u D E)

/-! ## 2. absolute bottom と二つの gap はそれぞれ canonical -/

/--
Bridge 側の `canonicalFlatBottom` は source / decomposition の選択に依存しない。

これは P35 の absolute-bottom theorem の Bridge 名による再掲。
top と違い、bottom は canonical skeleton にさえ依存せず fixed fiber だけで決まる。
-/
theorem canonicalFlatBottom_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1) :
    canonicalFlatBottom P hPrimitive hReduced u D =
      canonicalFlatBottom P hPrimitive hReduced v E := by
  simpa [canonicalFlatBottom] using
    canonicalNoBoundaryPoint_independent_of_decomposition
      P hPrimitive hReduced u v D E

/--
actual source から canonical flat top までに失われる `decorationGap` は
decomposition-independent。

したがって `decorationGap` は「任意に選んだ decomposition に付随する差」ではなく、
actual source に内在する canonical arithmetic decoration invariant である。
-/
theorem decorationGap_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    decorationGap P hPrimitive hReduced u D =
      decorationGap P hPrimitive hReduced u E := by
  unfold decorationGap
  rw [
    canonicalFlatTop_affineConst_independent_of_decomposition
      P hPrimitive hReduced u D E
  ]

/--
canonical flat top から absolute bottom までの `boundaryGap` も
decomposition-independent。

top は source の canonical record skeleton により決まり、
bottom は fixed fiber の absolute endpoint なので、この差も canonical。
-/
theorem boundaryGap_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    boundaryGap P hPrimitive hReduced u D =
      boundaryGap P hPrimitive hReduced u E := by
  unfold boundaryGap
  rw [
    canonicalFlatTop_affineConst_independent_of_decomposition
      P hPrimitive hReduced u D E
  ]
  have hBottom :
      canonicalFlatBottom P hPrimitive hReduced u D =
        canonicalFlatBottom P hPrimitive hReduced u E :=
    canonicalFlatBottom_independent_of_decomposition
      P hPrimitive hReduced u u D E
  rw [hBottom]

/--
二つの gap を組にした canonical gap pair。

第一成分は Boolean boundary geometry、
第二成分は actual local decoration の arithmetic contribution。
-/
def canonicalGapPair
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ × ℕ :=
  (boundaryGap P hPrimitive hReduced u D,
    decorationGap P hPrimitive hReduced u D)

/-- canonical gap pair は decomposition-independent。 -/
theorem canonicalGapPair_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    canonicalGapPair P hPrimitive hReduced u D =
      canonicalGapPair P hPrimitive hReduced u E := by
  apply Prod.ext
  · exact boundaryGap_independent_of_decomposition
      P hPrimitive hReduced u D E
  · exact decorationGap_independent_of_decomposition
      P hPrimitive hReduced u D E

/-! ## 3. exact arithmetic recovery は decomposition-free -/

/--
Bridge が外部 decoration を flat top へ戻して得る recovered `affineConst`。
-/
def recoveredAffineConst
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ :=
  affineConst (canonicalFlatTop P hPrimitive hReduced u D).word +
    decorationGap P hPrimitive hReduced u D

/-- recovered `affineConst` は actual source の genuine `affineConst` そのもの。 -/
@[simp] theorem recoveredAffineConst_eq_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    recoveredAffineConst P hPrimitive hReduced u D =
      affineConst u.word := by
  unfold recoveredAffineConst
  exact
    (affineConst_eq_flatTop_add_decorationGap
      P hPrimitive hReduced u D).symm

/-- recovered `affineConst` は decomposition-independent。 -/
theorem recoveredAffineConst_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    recoveredAffineConst P hPrimitive hReduced u D =
      recoveredAffineConst P hPrimitive hReduced u E := by
  rw [
    recoveredAffineConst_eq_source,
    recoveredAffineConst_eq_source
  ]

/--
absolute base より上の二つの canonical arithmetic layers。

以前は和だけの decomposition-independence しか使えなかったが、
本ファイルでは各 gap が個別に canonical なので、その強い corollary として残す。
-/
theorem boundaryGap_add_decorationGap_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    boundaryGap P hPrimitive hReduced u D +
        decorationGap P hPrimitive hReduced u D =
      boundaryGap P hPrimitive hReduced u E +
        decorationGap P hPrimitive hReduced u E := by
  rw [
    boundaryGap_independent_of_decomposition
      P hPrimitive hReduced u D E,
    decorationGap_independent_of_decomposition
      P hPrimitive hReduced u D E
  ]

/-! ## 4. arithmetic signature は canonical かつ lossless -/

/--
actual source の arithmetic decoration signature。

第一成分は canonical flat top の genuine `affineConst`、
第二成分は actual source まで戻す `decorationGap`。
-/
def arithmeticDecorationSignature
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ × ℕ :=
  (affineConst (canonicalFlatTop P hPrimitive hReduced u D).word,
    decorationGap P hPrimitive hReduced u D)

/-- arithmetic decoration signature は decomposition-independent。 -/
theorem arithmeticDecorationSignature_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    arithmeticDecorationSignature P hPrimitive hReduced u D =
      arithmeticDecorationSignature P hPrimitive hReduced u E := by
  apply Prod.ext
  · exact canonicalFlatTop_affineConst_independent_of_decomposition
      P hPrimitive hReduced u D E
  · exact decorationGap_independent_of_decomposition
      P hPrimitive hReduced u D E

/-- arithmetic signature の二成分の和は actual source の `affineConst`。 -/
theorem arithmeticDecorationSignature_sum_eq_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (arithmeticDecorationSignature P hPrimitive hReduced u D).1 +
        (arithmeticDecorationSignature P hPrimitive hReduced u D).2 =
      affineConst u.word := by
  exact
    (affineConst_eq_flatTop_add_decorationGap
      P hPrimitive hReduced u D).symm

/--
flat top の `affineConst` と decoration gap が双方一致すれば actual source は一致する。

fixed fiber 上の既存 theorem `fiberPoint_eq_of_same_affineConst` により、
Bridge の二つの算術成分は lossless。
-/
theorem source_eq_of_same_flatTopAffineConst_and_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hTop :
      affineConst (canonicalFlatTop P hPrimitive hReduced u D).word =
        affineConst (canonicalFlatTop P hPrimitive hReduced v E).word)
    (hGap :
      decorationGap P hPrimitive hReduced u D =
        decorationGap P hPrimitive hReduced v E) :
    u = v := by
  apply fiberPoint_eq_of_same_affineConst
  calc
    affineConst u.word =
        affineConst (canonicalFlatTop P hPrimitive hReduced u D).word +
          decorationGap P hPrimitive hReduced u D :=
      affineConst_eq_flatTop_add_decorationGap
        P hPrimitive hReduced u D
    _ =
        affineConst (canonicalFlatTop P hPrimitive hReduced v E).word +
          decorationGap P hPrimitive hReduced v E := by
      rw [hTop, hGap]
    _ = affineConst v.word :=
      (affineConst_eq_flatTop_add_decorationGap
        P hPrimitive hReduced v E).symm

/-- arithmetic decoration signature equality は actual source equality を強制する。 -/
theorem source_eq_of_same_arithmeticDecorationSignature
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hSig :
      arithmeticDecorationSignature P hPrimitive hReduced u D =
        arithmeticDecorationSignature P hPrimitive hReduced v E) :
    u = v := by
  have hTop :=
    congrArg (fun z : ℕ × ℕ => z.1) hSig
  have hGap :=
    congrArg (fun z : ℕ × ℕ => z.2) hSig
  apply
    source_eq_of_same_flatTopAffineConst_and_decorationGap
      P hPrimitive hReduced u v D E
  · simpa [arithmeticDecorationSignature] using hTop
  · simpa [arithmeticDecorationSignature] using hGap

/-! ## 5. geometric decorated-flat signature: 上段矢印そのもの -/

/--
actual source を

  canonical flat geometry + external arithmetic decoration

へ送る geometric signature。

これは Bridge の一番上の矢印を直接データ化したもの。
-/
def decoratedFlatSignature
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint P.oddCount P.twoDepth × ℕ :=
  (canonicalFlatTop P hPrimitive hReduced u D,
    decorationGap P hPrimitive hReduced u D)

/--
geometric decorated-flat signature は decomposition-independent。

したがって上段の bridge は任意に選んだ decomposition に依存する construction ではなく、
actual source に内在する canonical encoding である。
-/
theorem decoratedFlatSignature_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    decoratedFlatSignature P hPrimitive hReduced u D =
      decoratedFlatSignature P hPrimitive hReduced u E := by
  apply Prod.ext
  · exact canonicalFlatTop_independent_of_decomposition
      P hPrimitive hReduced u D E
  · exact decorationGap_independent_of_decomposition
      P hPrimitive hReduced u D E

/--
canonical flat top 自身と decoration gap が一致すれば actual source は一致する。
-/
theorem source_eq_of_same_canonicalFlatTop_and_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hTop :
      canonicalFlatTop P hPrimitive hReduced u D =
        canonicalFlatTop P hPrimitive hReduced v E)
    (hGap :
      decorationGap P hPrimitive hReduced u D =
        decorationGap P hPrimitive hReduced v E) :
    u = v := by
  have hTopAffine :
      affineConst (canonicalFlatTop P hPrimitive hReduced u D).word =
        affineConst (canonicalFlatTop P hPrimitive hReduced v E).word := by
    exact congrArg
      (fun x : FiberPoint P.oddCount P.twoDepth => affineConst x.word)
      hTop
  exact
    source_eq_of_same_flatTopAffineConst_and_decorationGap
      P hPrimitive hReduced u v D E hTopAffine hGap

/--
geometric decorated-flat signature equality は actual source equality を強制する。

これが

  actual source
      ↦ (canonical flat geometry, arithmetic decoration)

という Bridge の canonical lossless encoding theorem。
-/
theorem source_eq_of_same_decoratedFlatSignature
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hSig :
      decoratedFlatSignature P hPrimitive hReduced u D =
        decoratedFlatSignature P hPrimitive hReduced v E) :
    u = v := by
  have hTop :=
    congrArg
      (fun z : FiberPoint P.oddCount P.twoDepth × ℕ => z.1)
      hSig
  have hGap :=
    congrArg
      (fun z : FiberPoint P.oddCount P.twoDepth × ℕ => z.2)
      hSig
  apply
    source_eq_of_same_canonicalFlatTop_and_decorationGap
      P hPrimitive hReduced u v D E
  · simpa [decoratedFlatSignature] using hTop
  · simpa [decoratedFlatSignature] using hGap

/-! ## 6. 三層分解の canonicality -/

/--
同じ actual source に対して三層の arithmetic decomposition の各成分が
decomposition-independent。

absolute base は `P.oddCount` だけで決まり、
`boundaryGap` と `decorationGap` は本ファイルで個別に canonical と分かった。
-/
theorem canonical_three_layer_components
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    boundaryGap P hPrimitive hReduced u D =
        boundaryGap P hPrimitive hReduced u E ∧
      decorationGap P hPrimitive hReduced u D =
        decorationGap P hPrimitive hReduced u E := by
  exact ⟨
    boundaryGap_independent_of_decomposition
      P hPrimitive hReduced u D E,
    decorationGap_independent_of_decomposition
      P hPrimitive hReduced u D E
  ⟩

/--
Bridge の exact three-layer formula は、任意の genuine decomposition で
同じ二つの canonical gap を読む。

この theorem 自体は既存 exact formula の再掲だが、
直前の canonicity theorem と組み合わせることで

  affineConst(actual)
    = absoluteBase
      + canonical boundary contribution
      + canonical decoration contribution

という decomposition-free interpretation を持つ。
-/
theorem affineConst_eq_canonical_three_layer_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryGap P hPrimitive hReduced u D +
        decorationGap P hPrimitive hReduced u D := by
  exact
    affineConst_eq_absoluteBase_add_boundaryGap_add_decorationGap
      P hPrimitive hReduced u D

end RecordFerrers
end Collatz2
