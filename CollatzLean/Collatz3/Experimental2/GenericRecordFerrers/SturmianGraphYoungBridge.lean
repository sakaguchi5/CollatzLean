import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphOstrowskiBridge
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.OstrowskiYoungCompleteCode

/-!
# Collatz3 Experimental2: Sturmian graph coordinate と Young/Ferrers 完全符号

`OstrowskiYoungCompleteCode` では、完成 `RecordFerrers` の canonical block 長 `r` を
それぞれ `horizontalOstrowskiDigits r` に置き換え、その digit-code だけから

* `canonicalRecordLengths`,
* rank-envelope Ferrers / Young shape

を exact に復元した。

一方 `SturmianGraphOstrowskiBridge` では、この horizontal digit が使う weight system と
2012 年型 semi-normalized Sturmian graph の arc-weight system が同一であることを固定した。

そこで本ファイルでは、既存の canonical Young code を
「Sturmian graph と共有する weighted coordinate code」として公開する。

注意：ここで得るのはまだ greedy/canonical digit code と graph weight basis の exact 接続である。
2012 年 Theorem 47 の本体である

`lazy digits <-> unique Sturmian graph path`

は次段で証明する。未証明の counting theorem を axiom として導入しない。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RecordFerrers

/--
完成 RecordFerrers の canonical block を、Sturmian graph と共有する horizontal
Ostrowski weight 上の digit-code として読む公開名。

実体は `canonicalOstrowskiYoungCode` と同じで、データを重複保存しない。
-/
noncomputable def canonicalSturmianGraphDigitCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    List (ℕ → ℕ) :=
  R.canonicalOstrowskiYoungCode A

/-- Sturmian graph coordinate code は既存 canonical Young code と definitionally 同じ。 -/
@[simp] theorem canonicalSturmianGraphDigitCode_eq_youngCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    R.canonicalSturmianGraphDigitCode A =
      R.canonicalOstrowskiYoungCode A := rfl

/--
Sturmian graph coordinate code から canonical block length 列を exact に復元する。

各 digit は graph arc-weight と同じ `horizontalWeights.Q` を用いるため、
これは RecordFerrers の horizontal block partition を Sturmian weighted coordinate 側へ
移した最初の exact bridge になる。
-/
theorem canonicalSturmianGraphDigitCode_decodes_to_lengths
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    let D : RotationOstrowskiSystem α :=
      RotationOstrowskiExistence.rotationOstrowskiSystem α A
    D.horizontalOstrowskiLengthDecode (R.canonicalSturmianGraphDigitCode A) =
      canonicalRecordLengths (irrationalRotationRoof α) m R.height := by
  simpa [canonicalSturmianGraphDigitCode] using
    R.canonicalOstrowskiYoungCode_decodes_to_lengths A

/--
同じ Sturmian graph coordinate code を持つ二つの完成 RecordFerrers は、
canonical block length 列も exact に一致する。
-/
theorem canonicalRecordLengths_eq_of_sturmianGraphDigitCode_eq
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalSturmianGraphDigitCode A =
      S.canonicalSturmianGraphDigitCode A) :
    canonicalRecordLengths (irrationalRotationRoof α) m R.height =
      canonicalRecordLengths (irrationalRotationRoof α) m S.height := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  have hCode' :
      R.canonicalOstrowskiDigitCode D =
        S.canonicalOstrowskiDigitCode D := by
    simpa [canonicalSturmianGraphDigitCode,
      canonicalOstrowskiYoungCode, D] using hCode
  exact R.canonicalRecordLengths_eq_of_canonicalOstrowskiDigitCode_eq D S hCode'

/--
同じ Sturmian graph coordinate code は同じ rank-envelope Young/Ferrers shape を決める。

これは現段階での graph-side complete-code theorem。
次段で digit-code を unique lazy path 列へ持ち上げれば、そのまま
「Sturmian path code が Young/Ferrers shape を決める」定理へ昇格できる。
-/
theorem rankFerrersShape_eq_of_sturmianGraphDigitCode_eq
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalSturmianGraphDigitCode A =
      S.canonicalSturmianGraphDigitCode A) :
    R.rankFerrersShape = S.rankFerrersShape := by
  apply R.canonicalRecordLengths_complete_for_rankFerrersShape S
  exact R.canonicalRecordLengths_eq_of_sturmianGraphDigitCode_eq A S hCode

/--
公開 wrapper：Sturmian graph と共有する digit-code は rank Ferrers shape の完全符号として使える。
-/
theorem canonicalSturmianGraphDigitCode_complete_for_rankFerrersShape
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalSturmianGraphDigitCode A =
      S.canonicalSturmianGraphDigitCode A) :
    R.rankFerrersShape = S.rankFerrersShape :=
  R.rankFerrersShape_eq_of_sturmianGraphDigitCode_eq A S hCode

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
