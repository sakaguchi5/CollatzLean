import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationReconstruction

/-!
# Record–Ferrers Perturbation / Arithmetic Decoration Separation

`ArithmeticDecorationReconstruction` では、cut 1 の genuine record decomposition が持つ
fine coordinate list

  [(r₁,B₁), ..., (rₘ,Bₘ)]

が fixed `(p,H)` fiber 上の actual source を lossless に決めることを示した。

ただしこの coordinate list は、

* `rᵢ` : canonical record geometry の length skeleton
* `Bᵢ` : local valid minimal block の affine translation

を同じ pair list に同居させている。したがって lossless ではあるが、geometry と arithmetic
の情報分離としては冗長である。

本ファイルではこの冗長性を除く。

まず canonical flat top が source の canonical record length skeleton を exact に表すこと、

  canonicalFlatTop(u,D) = canonicalFlatTop(v,E)
    ↔ D.lengths = E.lengths

を閉じる。

次に pair coordinate equality を

  [(rᵢ,Bᵢ)] equality
    ↔ length skeleton equality ∧ local B-vector equality

へ exact に分解する。

最後に `ArithmeticDecorationReconstruction` と結合して

  u = v
    ↔ canonicalFlatTop(u,D) = canonicalFlatTop(v,E)
       ∧ localArithmeticTranslations D = localArithmeticTranslations E

を得る。

従って actual source は非冗長に

  canonical Record/Ferrers geometry
  + pure local arithmetic translation vector [B₁,...,Bₘ]

へ lossless に分離される。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. pair coordinate list は first / second projection から復元できる -/

/--
pair list は first projection と second projection の二列が一致すれば一致する。

後段で `(rᵢ,Bᵢ)` coordinate list を geometry 列 `rᵢ` と arithmetic 列 `Bᵢ` に
exact に分離するための一般補題。
-/
theorem pairList_eq_of_fst_snd_maps_eq
    {α β : Type}
    {xs ys : List (α × β)}
    (hFst : xs.map Prod.fst = ys.map Prod.fst)
    (hSnd : xs.map Prod.snd = ys.map Prod.snd) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          simp at hFst
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hFst
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at hFst hSnd
          have hXY : x = y := by
            apply Prod.ext
            · exact hFst.1
            · exact hSnd.1
          subst y
          have hTail : xs = ys := ih hFst.2 hSnd.2
          rw [hTail]

/--
`arithmeticDecorationCoordinates` equality は、canonical length skeleton equality と
pure local arithmetic translation vector equality の conjunction と exact に同値。
-/
theorem arithmeticDecorationCoordinates_eq_iff_lengths_and_localTranslations_eq
    {p H : ℕ}
    {u v : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1) :
    arithmeticDecorationCoordinates D =
        arithmeticDecorationCoordinates E ↔
      D.lengths = E.lengths ∧
        localArithmeticTranslations D = localArithmeticTranslations E := by
  constructor
  · intro hCoord
    constructor
    · calc
        D.lengths =
            (arithmeticDecorationCoordinates D).map Prod.fst :=
          (arithmeticDecorationCoordinates_lengths D).symm
        _ = (arithmeticDecorationCoordinates E).map Prod.fst :=
          congrArg (List.map Prod.fst) hCoord
        _ = E.lengths := arithmeticDecorationCoordinates_lengths E
    · unfold localArithmeticTranslations
      exact congrArg (List.map Prod.snd) hCoord
  · rintro ⟨hLengths, hTranslations⟩
    apply pairList_eq_of_fst_snd_maps_eq
    · rw [
        arithmeticDecorationCoordinates_lengths D,
        arithmeticDecorationCoordinates_lengths E,
        hLengths
      ]
    · simpa [localArithmeticTranslations] using hTranslations

/-! ## 2. canonical flat top は length skeleton の exact geometric encoding -/

/--
canonical flat top equality から source record length skeleton equality を復元する。

各 flat top には元 skeleton と同じ length list を持つ genuine decomposition が存在する。
flat points が一致すれば、その同一点上の genuine record decompositions の canonicality により
chosen length lists が一致し、元 skeleton も一致する。
-/
theorem lengths_eq_of_canonicalFlatTop_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hFlat :
      canonicalFlatTop P hPrimitive hReduced u D =
        canonicalFlatTop P hPrimitive hReduced v E) :
    D.lengths = E.lengths := by
  let DU := canonicalFlatTopDecomposition
    P hPrimitive hReduced u D
  let EV := canonicalFlatTopDecomposition
    P hPrimitive hReduced v E
  have hDU : DU.lengths = D.lengths := by
    dsimp [DU]
    exact canonicalFlatTopDecomposition_lengths
      P hPrimitive hReduced u D
  have hEV : EV.lengths = E.lengths := by
    dsimp [EV]
    exact canonicalFlatTopDecomposition_lengths
      P hPrimitive hReduced v E
  have hChosen : DU.lengths = EV.lengths := by
    exact RecordDecomposition.lengths_unique_of_point_eq hFlat DU EV
  calc
    D.lengths = DU.lengths := hDU.symm
    _ = EV.lengths := hChosen
    _ = E.lengths := hEV

/--
## 主定理 1: canonical flat top equality ↔ canonical length skeleton equality

canonical flat geometry は source の record length skeleton を余さず、重複なく符号化する。
-/
theorem canonicalFlatTop_eq_iff_lengths_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1) :
    canonicalFlatTop P hPrimitive hReduced u D =
        canonicalFlatTop P hPrimitive hReduced v E ↔
      D.lengths = E.lengths := by
  constructor
  · intro hFlat
    exact lengths_eq_of_canonicalFlatTop_eq
      P hPrimitive hReduced u v D E hFlat
  · intro hLengths
    exact canonicalFlatTop_eq_of_lengths_eq
      P hPrimitive hReduced u v D E hLengths

/-! ## 3. geometry + pure B-vector から full coordinate vector を復元 -/

/--
canonical flat geometry と pure local arithmetic translation vector が一致すれば、
full `(length,B)` coordinate vector が一致する。

geometry equality が `rᵢ` 列を、translation equality が `Bᵢ` 列を供給する。
-/
theorem arithmeticDecorationCoordinates_eq_of_same_flatTop_and_localTranslations
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hFlat :
      canonicalFlatTop P hPrimitive hReduced u D =
        canonicalFlatTop P hPrimitive hReduced v E)
    (hTranslations :
      localArithmeticTranslations D =
        localArithmeticTranslations E) :
    arithmeticDecorationCoordinates D =
      arithmeticDecorationCoordinates E := by
  apply
    (arithmeticDecorationCoordinates_eq_iff_lengths_and_localTranslations_eq
      D E).2
  exact ⟨
    lengths_eq_of_canonicalFlatTop_eq
      P hPrimitive hReduced u v D E hFlat,
    hTranslations
  ⟩

/--
## 主定理 2: canonical geometry + pure arithmetic B-vector は actual source を lossless に決める

以前の reconstruction では full pair coordinate vector `[(rᵢ,Bᵢ)]` が source を決めた。
ここでは `rᵢ` を canonical flat geometry 側へ完全に移し、arithmetic 側には `Bᵢ` だけを残す。
-/
theorem source_eq_of_same_canonicalFlatTop_and_localArithmeticTranslations
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1)
    (hFlat :
      canonicalFlatTop P hPrimitive hReduced u D =
        canonicalFlatTop P hPrimitive hReduced v E)
    (hTranslations :
      localArithmeticTranslations D =
        localArithmeticTranslations E) :
    u = v := by
  apply source_eq_of_same_arithmeticDecorationCoordinates u v D E
  exact arithmeticDecorationCoordinates_eq_of_same_flatTop_and_localTranslations
    P hPrimitive hReduced u v D E hFlat hTranslations

/--
## 主定理 3: actual source equality の非冗長 separation characterization

fixed fiber 上では actual source equality は

  canonical flat geometry equality
  ∧ pure local arithmetic B-vector equality

と exact に同値。
-/
theorem source_eq_iff_canonicalFlatTop_eq_and_localArithmeticTranslations_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1) :
    u = v ↔
      canonicalFlatTop P hPrimitive hReduced u D =
          canonicalFlatTop P hPrimitive hReduced v E ∧
        localArithmeticTranslations D =
          localArithmeticTranslations E := by
  constructor
  · intro huv
    subst v
    constructor
    · exact canonicalFlatTop_independent_of_decomposition
        P hPrimitive hReduced u D E
    · exact localArithmeticTranslations_independent_of_decomposition D E
  · rintro ⟨hFlat, hTranslations⟩
    exact source_eq_of_same_canonicalFlatTop_and_localArithmeticTranslations
      P hPrimitive hReduced u v D E hFlat hTranslations

/-! ## 4. separated signature -/

/--
actual source の非冗長 separated signature。

第一成分は canonical Record/Ferrers geometry、第二成分は純粋な local arithmetic B-vector。
full pair coordinates の length 成分は第一成分へ吸収されている。
-/
def separatedArithmeticDecorationSignature
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint P.oddCount P.twoDepth × List ℕ :=
  (canonicalFlatTop P hPrimitive hReduced u D,
    localArithmeticTranslations D)

/-- separated signature は decomposition witness に依存しない。 -/
theorem separatedArithmeticDecorationSignature_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    separatedArithmeticDecorationSignature
        P hPrimitive hReduced u D =
      separatedArithmeticDecorationSignature
        P hPrimitive hReduced u E := by
  apply Prod.ext
  · exact canonicalFlatTop_independent_of_decomposition
      P hPrimitive hReduced u D E
  · exact localArithmeticTranslations_independent_of_decomposition D E

/--
## 主定理 4: separated signature equality ↔ actual source equality

これが geometry / arithmetic separation の最終 lossless statement。
-/
theorem separatedArithmeticDecorationSignature_eq_iff_source_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u v : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition v 1) :
    separatedArithmeticDecorationSignature
        P hPrimitive hReduced u D =
        separatedArithmeticDecorationSignature
          P hPrimitive hReduced v E ↔
      u = v := by
  constructor
  · intro hSig
    have hFlat := congrArg Prod.fst hSig
    have hTranslations := congrArg Prod.snd hSig
    exact source_eq_of_same_canonicalFlatTop_and_localArithmeticTranslations
      P hPrimitive hReduced u v D E hFlat hTranslations
  · intro huv
    subst v
    exact separatedArithmeticDecorationSignature_independent_of_decomposition
      P hPrimitive hReduced u D E

/-! ## 5. closure package -/

/--
Arithmetic Decoration Separation 層で閉じた exact separation facts をまとめる。
-/
structure ArithmeticDecorationSeparationClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  flat_geometry_complete :
    ∀ (v : FiberPoint P.oddCount P.twoDepth)
      (E : RecordDecomposition v 1),
      canonicalFlatTop P hPrimitive hReduced u D =
          canonicalFlatTop P hPrimitive hReduced v E ↔
        D.lengths = E.lengths
  coordinate_split_exact :
    ∀ (v : FiberPoint P.oddCount P.twoDepth)
      (E : RecordDecomposition v 1),
      arithmeticDecorationCoordinates D =
          arithmeticDecorationCoordinates E ↔
        D.lengths = E.lengths ∧
          localArithmeticTranslations D = localArithmeticTranslations E
  separated_source_exact :
    ∀ (v : FiberPoint P.oddCount P.twoDepth)
      (E : RecordDecomposition v 1),
      u = v ↔
        canonicalFlatTop P hPrimitive hReduced u D =
            canonicalFlatTop P hPrimitive hReduced v E ∧
          localArithmeticTranslations D = localArithmeticTranslations E
  signature_canonical :
    ∀ E : RecordDecomposition u 1,
      separatedArithmeticDecorationSignature
          P hPrimitive hReduced u D =
        separatedArithmeticDecorationSignature
          P hPrimitive hReduced u E
  signature_lossless :
    ∀ (v : FiberPoint P.oddCount P.twoDepth)
      (E : RecordDecomposition v 1),
      separatedArithmeticDecorationSignature
          P hPrimitive hReduced u D =
          separatedArithmeticDecorationSignature
            P hPrimitive hReduced v E ↔
        u = v

/--
## Arithmetic Decoration Separation closure theorem

actual source は canonical flat geometry と pure local arithmetic translation vector に
exact かつ decomposition-independent に分離される。full pair coordinate vector の
length information は geometry 側へ完全に吸収され、arithmetic 側には `Bᵢ` 列だけが残る。
-/
theorem arithmeticDecorationSeparation_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ArithmeticDecorationSeparationClosed
      P hPrimitive hReduced u D := by
  refine {
    flat_geometry_complete := ?_
    coordinate_split_exact := ?_
    separated_source_exact := ?_
    signature_canonical := ?_
    signature_lossless := ?_
  }
  · intro v E
    exact canonicalFlatTop_eq_iff_lengths_eq
      P hPrimitive hReduced u v D E
  · intro v E
    exact arithmeticDecorationCoordinates_eq_iff_lengths_and_localTranslations_eq
      D E
  · intro v E
    exact source_eq_iff_canonicalFlatTop_eq_and_localArithmeticTranslations_eq
      P hPrimitive hReduced u v D E
  · intro E
    exact separatedArithmeticDecorationSignature_independent_of_decomposition
      P hPrimitive hReduced u D E
  · intro v E
    exact separatedArithmeticDecorationSignature_eq_iff_source_eq
      P hPrimitive hReduced u v D E

end RecordFerrers
end Collatz2
