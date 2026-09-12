import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphObservableUniqueness
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.LazyOstrowskiCompleteCode
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphOstrowskiBridge

/-!
# Collatz3 Experimental2: actual Sturmian path の完全 edge-count code

Theorem 47 bridge により、weight `N` の canonical 初期 Sturmian path の `edgeCount` は
canonical lazy Ostrowski digits と一致する。

本ファイルではこの `edgeCount` 自体を canonical path code として公開し、

* 実 path による realization,
* lazy digits との exact equality,
* path code から weight の復元,
* weight 上の injectivity,
* block-length 列の encode/decode

を閉じる。

raw dependent path term を code として保存せず、実 graph path から読める `edgeCount` を
proof-object independent な完全符号として使う。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/-- weight `N` の canonical 初期 Sturmian path から読む edge-count code。 -/
noncomputable def canonicalSturmianPathCodeOfWeight
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) : ℕ → ℕ :=
  (canonicalInitialSturmianPath W N).path.edgeCount

/-- canonical path code は canonical lazy Ostrowski digit code と exact に一致する。 -/
theorem canonicalSturmianPathCodeOfWeight_eq_lazyDigits
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    canonicalSturmianPathCodeOfWeight W N =
      canonicalLazyOstrowskiDigits W N := by
  funext h
  exact edgeCount_eq_canonicalLazyDigits (canonicalInitialSturmianPath W N).path h

/-- canonical path code は実際の初期 Sturmian path の edgeCount として実現される。 -/
theorem canonicalSturmianPathCodeOfWeight_realized
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    ∃ P : InitialSturmianPathOfWeight W N,
      P.path.edgeCount = canonicalSturmianPathCodeOfWeight W N := by
  exact ⟨canonicalInitialSturmianPath W N, rfl⟩

/--
任意の weight-`N` 初期 path から読んだ code は canonical path code と同じ。
これが path proof object に依存しない canonicality。
-/
theorem initialPath_edgeCount_eq_canonicalSturmianPathCode
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (P : InitialSturmianPathOfWeight W N) :
    P.path.edgeCount = canonicalSturmianPathCodeOfWeight W N := by
  exact initialPaths_sameWeight_edgeCount_eq
    P.path (canonicalInitialSturmianPath W N).path

/-- path code は元の weight を一意に決める。 -/
theorem canonicalSturmianPathCodeOfWeight_injective
    (W : UnitOstrowskiWeightSystem) :
    Function.Injective (canonicalSturmianPathCodeOfWeight W) := by
  intro M N hCode
  apply canonicalLazyOstrowskiDigits_injective W
  rw [← canonicalSturmianPathCodeOfWeight_eq_lazyDigits W M,
    ← canonicalSturmianPathCodeOfWeight_eq_lazyDigits W N]
  exact hCode

/-- canonical path code から weight を復元する decoder。 -/
noncomputable def canonicalSturmianPathWeight
    (W : UnitOstrowskiWeightSystem)
    (code : ℕ → ℕ) : ℕ :=
  canonicalLazyOstrowskiValue W code

/-- canonical path code を decode すると元の weight に戻る。 -/
@[simp] theorem canonicalSturmianPathWeight_code
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    canonicalSturmianPathWeight W (canonicalSturmianPathCodeOfWeight W N) = N := by
  rw [canonicalSturmianPathCodeOfWeight_eq_lazyDigits]
  exact canonicalLazyOstrowskiValue_digits W N

/-- `d` が weight `N` の実初期 path の edgeCount として現れること。 -/
def IsInitialSturmianPathCode
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (d : ℕ → ℕ) : Prop :=
  ∃ P : InitialSturmianPathOfWeight W N, P.path.edgeCount = d

/-- 実 path code であることと canonical path code に一致することは同値。 -/
theorem isInitialSturmianPathCode_iff_eq_canonical
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (d : ℕ → ℕ) :
    IsInitialSturmianPathCode W N d ↔
      d = canonicalSturmianPathCodeOfWeight W N := by
  constructor
  · rintro ⟨P, hP⟩
    have hCanon := initialPath_edgeCount_eq_canonicalSturmianPathCode P
    rw [hP] at hCanon
    exact hCanon
  · intro h
    subst d
    exact canonicalSturmianPathCodeOfWeight_realized W N

namespace RotationOstrowskiSystem

/-- `D.horizontalWeights` に対する weight `N` の actual Sturmian path code。 -/
noncomputable def sturmianPathCodeOfWeight
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) : ℕ → ℕ :=
  canonicalSturmianPathCodeOfWeight D.horizontalWeights N

/-- `D` の path code は canonical lazy graph path の edgeCount そのもの。 -/
theorem sturmianPathCodeOfWeight_eq_edgeCount
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.sturmianPathCodeOfWeight N =
      (D.canonicalLazySturmianGraphPath N).path.edgeCount := by
  rfl

/-- `D` の path code は horizontal lazy Ostrowski digits と一致する。 -/
theorem sturmianPathCodeOfWeight_eq_lazyDigits
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.sturmianPathCodeOfWeight N =
      canonicalLazyOstrowskiDigits D.horizontalWeights N :=
  canonicalSturmianPathCodeOfWeight_eq_lazyDigits D.horizontalWeights N

/-- `D` の path code は weight 上で injective。 -/
theorem sturmianPathCodeOfWeight_injective
    {α : ℝ}
    (D : RotationOstrowskiSystem α) :
    Function.Injective D.sturmianPathCodeOfWeight :=
  canonicalSturmianPathCodeOfWeight_injective D.horizontalWeights

/-- block length 列を actual Sturmian path edge-count code の列へ写す。 -/
noncomputable def sturmianPathLengthCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) : List (ℕ → ℕ) :=
  rs.map D.sturmianPathCodeOfWeight

/-- path code 列を各 weight / block length へ戻す。 -/
noncomputable def sturmianPathLengthDecode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (code : List (ℕ → ℕ)) : List ℕ :=
  code.map (canonicalSturmianPathWeight D.horizontalWeights)

/-- path code 列は encode 後の decode で元の length 列へ exact に戻る。 -/
@[simp] theorem sturmianPathLengthDecode_encode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) :
    D.sturmianPathLengthDecode (D.sturmianPathLengthCode rs) = rs := by
  induction rs with
  | nil =>
      simp [sturmianPathLengthCode, sturmianPathLengthDecode]
  | cons r rs ih =>
      change
        canonicalSturmianPathWeight D.horizontalWeights
              (D.sturmianPathCodeOfWeight r) ::
            D.sturmianPathLengthDecode (D.sturmianPathLengthCode rs) =
          r :: rs
      simp [sturmianPathCodeOfWeight, ih]

/-- block length 列の actual Sturmian path code は injective。 -/
theorem sturmianPathLengthCode_injective
    {α : ℝ}
    (D : RotationOstrowskiSystem α) :
    Function.Injective D.sturmianPathLengthCode := by
  intro rs ss hCode
  have hDecoded := congrArg D.sturmianPathLengthDecode hCode
  simpa using hDecoded

end RotationOstrowskiSystem

end GenericRecordFerrers
end Experimental2
end Collatz3
