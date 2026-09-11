import CollatzLean.Collatz3.Bridge.Experimental2DualOstrowskiCoordinates
import CollatzLean.Collatz3.Bridge.RecordFerrersRealization

/-!
# Collatz3 Bridge: dual Ostrowski coordinates と initial-value realization

`RecordFerrersRealization` で得た profile residue class を、
`Experimental2DualOstrowskiCoordinates` の二座標へ接続する。

役割は明確に分ける。

* vertical canonical code は terminal two-depth `H` を表し、residue modulus `2^(H+1)` を決める。
* horizontal canonical code は canonical initial value、または同じ residue class に属する actual start を表す。

二つの digit 列を直接同一視する theorem は置かない。
同一 Collatz packet であることから生じる residue constraint を介してのみ両者を結ぶ。
-/

namespace Collatz3
open Experimental2
namespace Bridge
namespace BeattyRegularOstrowskiSystem

/--
RecordFerrers の terminal height が決める odd-start modulus を、
vertical canonical Ostrowski code の `Q`-evaluation だけで書いた形。

従って structural vertical coordinate は初期値 residue の精度 `2^(H+1)` を exact に決める。
-/
theorem recordRealizationModulus_eq_verticalOstrowski
    (D : BeattyRegularOstrowskiSystem)
    (m : ℕ) :
    Critical.profileOddEndpointModulus m =
      2 ^
        (ostrowskiPrefixSum D.weights.Q
            (D.verticalOstrowskiDigits (Critical.criticalTwoDepth m))
            (Critical.criticalTwoDepth m + 1) + 1) := by
  rw [Critical.profileOddEndpointModulus_eq]
  rw [D.verticalOstrowskiDigits_reconstruct
    (Critical.criticalTwoDepth m)]

/--
RecordFerrers packet の canonical initial value は、horizontal canonical code から
exact に復元できる。
-/
theorem recordCanonicalInitialValue_horizontal_reconstruct
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    ostrowskiPrefixSum (D.horizontalWeights).Q
        (D.horizontalOstrowskiDigits (recordCanonicalInitialValue R))
        (recordCanonicalInitialValue R + 1) =
      recordCanonicalInitialValue R := by
  exact
    D.horizontalOstrowskiDigits_reconstruct
      (recordCanonicalInitialValue R)

/--
horizontal canonical code が復元する canonical initial value を residue ring に戻すと、
RecordFerrers packet の realization class そのものになる。
-/
theorem recordCanonicalHorizontal_cast_eq_realizationClass
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    ((ostrowskiPrefixSum (D.horizontalWeights).Q
          (D.horizontalOstrowskiDigits (recordCanonicalInitialValue R))
          (recordCanonicalInitialValue R + 1) : ℕ) :
        ZMod (Critical.profileOddEndpointModulus m)) =
      recordRealizationClass R := by
  rw [D.recordCanonicalInitialValue_horizontal_reconstruct R]
  exact Critical.profileCanonicalStart_cast R.profile.1

/--
同じ word/profile packet の canonical residue representative は horizontal coordinate でも一致する。

これは初期値側と RecordFerrers 側の Ostrowski digits が直接一致するという主張ではない。
両者が同じ canonical natural number を表すため、その horizontal normal form が一致する。
-/
theorem recordCanonicalHorizontalDigits_eq_wordCanonicalHorizontalDigits
    (D : BeattyRegularOstrowskiSystem)
    {w : Word}
    {R : Ferrers.RecordFerrers (Word.oddSteps w)}
    (hReal : IsWordRecordRealization R)
    (hFirst : Word.CriticalFirstPassage w) :
    D.horizontalOstrowskiDigits (recordCanonicalInitialValue R) =
      D.horizontalOstrowskiDigits (Word.canonicalStart w) := by
  rw [hReal.canonicalInitialValue_eq_wordCanonicalStart hFirst]

/--
actual start `x` の horizontal canonical code を評価して residue ring に送ると、
同じ RecordFerrers packet が指定する realization class に入る。

これが二段階

`RecordFerrers/Ostrowski packet -> residue class -> horizontal Ostrowski start`

の exact coupling theorem。
-/
theorem horizontalOstrowski_start_has_recordRealizationClass
    (D : BeattyRegularOstrowskiSystem)
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w)
    (R : Ferrers.RecordFerrers (Word.oddSteps w))
    (hReal : IsWordRecordRealization R)
    {x y : ℕ}
    (hEndpoint : w.EndpointEquation x y)
    (hy : Odd y) :
    ((ostrowskiPrefixSum (D.horizontalWeights).Q
          (D.horizontalOstrowskiDigits x) (x + 1) : ℕ) :
        ZMod (Critical.profileOddEndpointModulus (Word.oddSteps w))) =
      recordRealizationClass R := by
  rw [D.horizontalOstrowskiDigits_reconstruct x]
  exact
    endpoint_start_has_recordRealizationClass
      hFirst R hReal hEndpoint hy

/--
同じ packet について、Record partition / affine numerator / horizontal canonical representative を
一度に読めるまとめ theorem。

`canonicalRecordLengths` は word の逆符号化ではなく、同じ extracted profile の派生 view として現れる。
-/
theorem recordPacket_dualOstrowski_views
    (D : BeattyRegularOstrowskiSystem)
    {w : Word}
    {R : Ferrers.RecordFerrers (Word.oddSteps w)}
    (hReal : IsWordRecordRealization R)
    (hFirst : Word.CriticalFirstPassage w) :
    Ferrers.canonicalRecordLengths R.profile.1 =
        Ferrers.canonicalRecordLengths (Critical.profileFromWord w) ∧
      Critical.profileAffineNumerator R.profile.1 = Word.affineConst w ∧
      D.horizontalOstrowskiDigits (recordCanonicalInitialValue R) =
        D.horizontalOstrowskiDigits (Word.canonicalStart w) := by
  exact ⟨hReal.canonicalRecordLengths_eq,
    hReal.profileAffineNumerator_eq_affineConst hFirst,
    D.recordCanonicalHorizontalDigits_eq_wordCanonicalHorizontalDigits
      hReal hFirst⟩

end BeattyRegularOstrowskiSystem
end Bridge
end Collatz3
