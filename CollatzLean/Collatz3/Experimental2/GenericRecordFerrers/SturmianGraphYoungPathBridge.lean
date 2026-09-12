import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphPathCode
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.OstrowskiYoungCompleteCode
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RotationOstrowskiExistence

/-!
# Collatz3 Experimental2: actual Sturmian path code と Young/Ferrers 完全符号

`OstrowskiYoungCompleteCode` は各 canonical block length を greedy Ostrowski digits で符号化した。
一方 `SturmianGraphPathCode` では、同じ block length を weight とする実 Sturmian graph path の
`edgeCount` を canonical lazy path code として完全復号できるようにした。

本ファイルでは完成 RecordFerrers の canonical block 列を actual path-code 列へ移し、

* path code から canonicalRecordLengths を exact に復元すること、
* 同じ path code が同じ rank Ferrers / Young shape を決めること、
* path code から shape を直接返す decoder、
* 外部 RotationOstrowskiSystem certificate を残さない canonical wrapper

を閉じる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RecordFerrers

/--
完成 RecordFerrers の canonical block 列を、各 block weight の actual Sturmian path edge-count code に写す。
-/
noncomputable def canonicalSturmianPathCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    List (ℕ → ℕ) :=
  D.sturmianPathLengthCode
    (canonicalRecordLengths (irrationalRotationRoof α) m R.height)

/-- actual Sturmian path code から canonicalRecordLengths を exact に復元する。 -/
@[simp] theorem decode_canonicalSturmianPathCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.sturmianPathLengthDecode (R.canonicalSturmianPathCode D) =
      canonicalRecordLengths (irrationalRotationRoof α) m R.height := by
  unfold canonicalSturmianPathCode
  exact D.sturmianPathLengthDecode_encode _

/--
同じ actual Sturmian path code を持つ二つの完成 RecordFerrers は canonical block length 列が一致する。
-/
theorem canonicalRecordLengths_eq_of_sturmianPathCode_eq
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalSturmianPathCode D =
      S.canonicalSturmianPathCode D) :
    canonicalRecordLengths (irrationalRotationRoof α) m R.height =
      canonicalRecordLengths (irrationalRotationRoof α) m S.height := by
  apply D.sturmianPathLengthCode_injective
  simpa [canonicalSturmianPathCode] using hCode

/--
actual Sturmian path code は rank-envelope Ferrers / Young shape の完全符号として使える。
-/
theorem rankFerrersShape_eq_of_sturmianPathCode_eq
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalSturmianPathCode D =
      S.canonicalSturmianPathCode D) :
    R.rankFerrersShape = S.rankFerrersShape := by
  apply R.canonicalRecordLengths_complete_for_rankFerrersShape S
  exact R.canonicalRecordLengths_eq_of_sturmianPathCode_eq D S hCode

/-- 公開 wrapper：same path code implies same rank Ferrers shape。 -/
theorem canonicalSturmianPathCode_complete_for_rankFerrersShape
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalSturmianPathCode D =
      S.canonicalSturmianPathCode D) :
    R.rankFerrersShape = S.rankFerrersShape :=
  R.rankFerrersShape_eq_of_sturmianPathCode_eq D S hCode

end RecordFerrers

namespace RotationOstrowskiSystem

/--
actual Sturmian path-code 列だけから rank-envelope Ferrers shape を復元する decoder。
-/
noncomputable def sturmianRankFerrersShapeFromPathCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (code : List (ℕ → ℕ)) :
    Combinatorics.FerrersShape (m - 1) :=
  D.ostrowskiRankFerrersShapeFromLengths A m
    (D.sturmianPathLengthDecode code)

end RotationOstrowskiSystem

namespace RecordFerrers

/-- canonical actual path code を shape decoder に入れると元の rankFerrersShape に exact に戻る。 -/
theorem sturmianRankFerrersShapeFromPathCode_eq_rankFerrersShape
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.sturmianRankFerrersShapeFromPathCode A m
        (R.canonicalSturmianPathCode D) =
      R.rankFerrersShape := by
  unfold RotationOstrowskiSystem.sturmianRankFerrersShapeFromPathCode
  rw [R.decode_canonicalSturmianPathCode D]
  exact R.ostrowskiRankFerrersShape_eq_rankFerrersShape D A

/--
存在定理で canonical に選んだ RotationOstrowskiSystem を用いる actual Sturmian path code。
-/
noncomputable def canonicalSturmianYoungPathCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    List (ℕ → ℕ) :=
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  R.canonicalSturmianPathCode D

/-- certificate-free actual path-code shape decoder。 -/
noncomputable def canonicalSturmianYoungShapeFromPathCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (code : List (ℕ → ℕ)) :
    Combinatorics.FerrersShape (m - 1) :=
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  D.sturmianRankFerrersShapeFromPathCode A m code

/--
外部 certificate なしの最終復元定理：actual Sturmian path code から rankFerrersShape 全体を復元する。
-/
theorem canonicalSturmianYoungShapeFromPathCode_eq_rankFerrersShape
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    canonicalSturmianYoungShapeFromPathCode A m
        (R.canonicalSturmianYoungPathCode A) =
      R.rankFerrersShape := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    D.sturmianRankFerrersShapeFromPathCode A m
        (R.canonicalSturmianPathCode D) =
      R.rankFerrersShape
  exact R.sturmianRankFerrersShapeFromPathCode_eq_rankFerrersShape D A

/-- certificate-free path code から canonicalRecordLengths も exact に復元できる。 -/
theorem canonicalSturmianYoungPathCode_decodes_to_lengths
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    let D : RotationOstrowskiSystem α :=
      RotationOstrowskiExistence.rotationOstrowskiSystem α A
    D.sturmianPathLengthDecode (R.canonicalSturmianYoungPathCode A) =
      canonicalRecordLengths (irrationalRotationRoof α) m R.height := by
  dsimp [canonicalSturmianYoungPathCode]
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    D.sturmianPathLengthDecode (R.canonicalSturmianPathCode D) =
      canonicalRecordLengths (irrationalRotationRoof α) m R.height
  exact R.decode_canonicalSturmianPathCode D

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
