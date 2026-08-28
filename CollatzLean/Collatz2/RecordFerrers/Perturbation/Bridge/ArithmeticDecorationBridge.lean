import CollatzLean.Collatz2.RecordFerrers.Perturbation.P35ActualDeletionSystemClosure

/-!
# Record–Ferrers Perturbation / Arithmetic Decoration Bridge

P29--P35 で閉じた canonical Boolean / Ferrers 摂動系と、
元の actual FiberPoint が持つ genuine `affineConst` を接続するための橋。

このファイルでは、Perturbation 側の標準平坦化そのものに算術情報を
押し込めない。代わりに

* 全境界保持 pattern を canonical flat family の「上端」として固定する。
* その上端が元の actual source 以下にあることを示す。
* 任意の Boolean pattern も元の actual source 以下にあることを示す。
* actual source と flat top の差を `decorationGap`、flat top と absolute bottom
  の差を `boundaryGap` として外部に保持する。
* genuine `affineConst` を

    absolute bottom + boundaryGap + decorationGap

  に exact に分解する。

したがって P1--P35 の純粋 Perturbation 理論を変更せず、
actual arithmetic / decoration 側との接続だけをこの層に隔離できる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 全境界保持 pattern は元の skeleton をそのまま与える -/

/--
全 flag が `true` なら Boolean 粗視化は何もしない。

これは P29 の一般的な `coarsenByFlags` に対する内部補題であり、
Bridge の公開 API では次の
`coarsenedLengthsFor_retainAllBoundaries` を使う。
-/
private theorem coarsenByFlags_eq_self_of_all_true
    (lengths : List ℕ)
    (flags : List Bool)
    (hFlags : flags.length = lengths.length - 1)
    (hTrue : ∀ b ∈ flags, b = true) :
    coarsenByFlags lengths flags = lengths := by
  induction lengths generalizing flags with
  | nil =>
      have hLen : flags.length = 0 := by
        simpa using hFlags
      have hNil : flags = [] := List.length_eq_zero_iff.mp hLen
      subst flags
      rfl
  | cons r rest ih =>
      cases rest with
      | nil =>
          have hLen : flags.length = 0 := by
            simpa using hFlags
          have hNil : flags = [] := List.length_eq_zero_iff.mp hLen
          subst flags
          rfl
      | cons s tail =>
          cases flags with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hFlags
              omega
          | cons b bs =>
              have hb : b = true := hTrue b (by simp)
              subst b
              have hBsTrue : ∀ x ∈ bs, x = true := by
                intro x hx
                exact hTrue x (by simp [hx])
              have hBsLen :
                  bs.length = (s :: tail).length - 1 := by
                simp only [List.length_cons] at hFlags ⊢
                omega
              have hTail := ih bs hBsLen hBsTrue
              simp only [coarsenByFlags]
              rw [hTail]

/-- 全保持 pattern の retained flag は全て `true`。 -/
private theorem retainedFlags_retainAll_all_true
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    ∀ b ∈ retainedFlags (retainAllBoundaries D), b = true := by
  intro b hb
  unfold retainedFlags at hb
  rcases List.mem_ofFn.mp hb with ⟨i, hi⟩
  have hiTrue : true = b := by
    simpa [retainAllBoundaries] using hi
  exact hiTrue.symm

/--
全内部 Record 境界を保持すると、P29 の粗視化 length skeleton は
元の `RecordDecomposition.lengths` と exact に一致する。
-/
@[simp] theorem coarsenedLengthsFor_retainAllBoundaries
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    coarsenedLengthsFor D (retainAllBoundaries D) = D.lengths := by
  unfold coarsenedLengthsFor
  exact coarsenByFlags_eq_self_of_all_true
    D.lengths
    (retainedFlags (retainAllBoundaries D))
    (retainedFlags_length (retainAllBoundaries D))
    (retainedFlags_retainAll_all_true D)

/-! ## 2. actual source と canonical flat Boolean family の幾何学的接続 -/

/--
元の全 Record 境界を保持した canonical flat representative。
Boolean family の幾何学的な上端として使う。
-/
def canonicalFlatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint P.oddCount P.twoDepth :=
  canonicalFlatPoint
    P hPrimitive hReduced u D (retainAllBoundaries D)

/--
P35 の全消去 normal form を Bridge 側では canonical flat bottom と呼ぶ。
これは fixed fiber 全体の absolute bottom と exact に一致する。
-/
def canonicalFlatBottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint P.oddCount P.twoDepth :=
  canonicalNoBoundaryPoint P hPrimitive hReduced u D

/--
全境界保持 canonical flat point は元の actual source 以下にある。

ここで初めて P30 の「同じ skeleton の標準平坦代表は最小」という定理を
元の source 自身へ適用する。
-/
theorem canonicalFlatTop_ferrersLe_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint.FerrersLe
      (canonicalFlatTop P hPrimitive hReduced u D) u := by
  have h :=
    canonicalFlatRepresentative_le_of_same_skeleton
      P hPrimitive hReduced u D
      (retainAllBoundaries D)
      u D
      (coarsenedLengthsFor_retainAllBoundaries D).symm
  simpa [canonicalFlatTop, canonicalFlatPoint] using h

/--
任意の Boolean pattern の canonical flat point は元の actual source 以下にある。

Boolean 順序では任意の pattern が全保持 pattern 以下であり、P33 がその順序を
Ferrers inclusion へ exact に送る。そこから上の定理へ推移する。
-/
theorem canonicalFlatPoint_ferrersLe_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    FiberPoint.FerrersLe
      (canonicalFlatPoint P hPrimitive hReduced u D R) u := by
  have hRTop :
      FiberPoint.FerrersLe
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (canonicalFlatPoint
          P hPrimitive hReduced u D (retainAllBoundaries D)) :=
    canonicalFlatPoint_ferrersLe_of_retainedLe
      P hPrimitive hReduced u D
      (RetainedBoundaryPattern.le_all D R)
  have hTop :
      FiberPoint.FerrersLe
        (canonicalFlatPoint
          P hPrimitive hReduced u D (retainAllBoundaries D)) u := by
    simpa [canonicalFlatTop] using
      canonicalFlatTop_ferrersLe_source
        P hPrimitive hReduced u D
  intro i
  exact (hRTop i).trans (hTop i)

/-! ## 3. actual arithmetic を flat geometry の外側に保持する -/

/--
flat top の genuine `affineConst` は actual source の値以下。
これは decoration gap を自然数として定義できることを保証する。
-/
theorem canonicalFlatTop_affineConst_le_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst (canonicalFlatTop P hPrimitive hReduced u D).word ≤
      affineConst u.word := by
  have h :=
    canonicalFlatRepresentative_affineConst_le_of_same_skeleton
      P hPrimitive hReduced u D
      (retainAllBoundaries D)
      u D
      (coarsenedLengthsFor_retainAllBoundaries D).symm
  simpa [canonicalFlatTop, canonicalFlatPoint] using h

/-- absolute bottom の `affineConst` は flat top 以下。 -/
theorem canonicalFlatBottom_affineConst_le_top
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word ≤
      affineConst (canonicalFlatTop P hPrimitive hReduced u D).word := by
  rcases canonicalNoBoundaryPoint_global_potential_minimum
      P hPrimitive hReduced u D with
    ⟨_hArea, _hBottom, _hAreaMin, hAffineMin⟩
  have h := hAffineMin
    (canonicalFlatTop P hPrimitive hReduced u D)
  simpa [canonicalFlatBottom] using h

/--
actual source に残る「局所 decoration 側」の算術量。

flat top まで落として失われる genuine `affineConst` の差を保持する。
-/
def decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ :=
  affineConst u.word -
    affineConst (canonicalFlatTop P hPrimitive hReduced u D).word

/--
Boolean boundary geometry が flat top から absolute bottom まで持つ算術量。
-/
def boundaryGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ :=
  affineConst (canonicalFlatTop P hPrimitive hReduced u D).word -
    affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word

/-- actual source の `affineConst` は flat top と decoration gap に exact に分解する。 -/
theorem affineConst_eq_flatTop_add_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      affineConst (canonicalFlatTop P hPrimitive hReduced u D).word +
        decorationGap P hPrimitive hReduced u D := by
  have hLe :=
    canonicalFlatTop_affineConst_le_source
      P hPrimitive hReduced u D
  unfold decorationGap
  omega

/-- flat top の `affineConst` は absolute bottom と boundary gap に exact に分解する。 -/
theorem flatTop_affineConst_eq_bottom_add_boundaryGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst (canonicalFlatTop P hPrimitive hReduced u D).word =
      affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word +
        boundaryGap P hPrimitive hReduced u D := by
  have hLe :=
    canonicalFlatBottom_affineConst_le_top
      P hPrimitive hReduced u D
  unfold boundaryGap
  omega

/--
Bridge の中心的な exact decomposition。

actual arithmetic は

  absolute bottom + Boolean-boundary contribution + local-decoration contribution

へ分離される。
-/
theorem affineConst_eq_bottom_add_boundaryGap_add_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word +
        boundaryGap P hPrimitive hReduced u D +
        decorationGap P hPrimitive hReduced u D := by
  calc
    affineConst u.word =
        affineConst (canonicalFlatTop P hPrimitive hReduced u D).word +
          decorationGap P hPrimitive hReduced u D :=
      affineConst_eq_flatTop_add_decorationGap
        P hPrimitive hReduced u D
    _ =
        (affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word +
          boundaryGap P hPrimitive hReduced u D) +
          decorationGap P hPrimitive hReduced u D := by
      rw [flatTop_affineConst_eq_bottom_add_boundaryGap
        P hPrimitive hReduced u D]

/--
P35 の absolute-bottom formula を代入した算術版。

固定 fiber では actual `affineConst` が

  (3^p - 2^p) + boundaryGap + decorationGap

と exact に書ける。
-/
theorem affineConst_eq_absoluteBase_add_boundaryGap_add_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryGap P hPrimitive hReduced u D +
        decorationGap P hPrimitive hReduced u D := by
  rcases canonicalNoBoundaryPoint_global_potential_minimum
      P hPrimitive hReduced u D with
    ⟨_hArea, hBottomExact, _hAreaMin, _hAffineMin⟩
  have hBottom :
      affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word =
        3 ^ P.oddCount - 2 ^ P.oddCount := by
    simpa [canonicalFlatBottom] using hBottomExact
  calc
    affineConst u.word =
        affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word +
          boundaryGap P hPrimitive hReduced u D +
          decorationGap P hPrimitive hReduced u D :=
      affineConst_eq_bottom_add_boundaryGap_add_decorationGap
        P hPrimitive hReduced u D
    _ =
        (3 ^ P.oddCount - 2 ^ P.oddCount) +
          boundaryGap P hPrimitive hReduced u D +
          decorationGap P hPrimitive hReduced u D := by
      rw [hBottom]

end RecordFerrers
end Collatz2
