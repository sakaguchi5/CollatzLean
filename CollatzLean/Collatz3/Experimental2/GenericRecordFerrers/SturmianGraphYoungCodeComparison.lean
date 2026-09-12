import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphYoungBridge
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphYoungPathBridge

/-!
# Collatz3 Experimental2: greedy Young code と lazy Sturmian path code の exact 比較

同じ canonical block length `r` には、現在二つの完全符号がある。

* `horizontalOstrowskiDigits r`：canonical greedy Ostrowski code、
* `sturmianPathCodeOfWeight r`：actual Sturmian graph path の `edgeCount`、すなわち lazy code。

これらの digit 列そのものは一般に同一ではない。
本ファイルでは両者を直接等置せず、共通の block length 列を介して exact に比較する。

中心となる図式は

`greedy code -> canonicalRecordLengths -> actual path code`

および逆向きである。

従って

* greedy Young code と lazy/path code は相互変換できる、
* 両者を decode すると同じ `canonicalRecordLengths` を返す、
* 二つの RecordFerrers が greedy code で一致することと path code で一致することは同値、
* 両 code の shape decoder は canonical input 上で同じ rank Ferrers / Young shape を返す

ことを証明する。

ここでは greedy と lazy を同一視しないことが重要である。
一致するのは digit 列ではなく、それらが完全符号している underlying block-length data である。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RotationOstrowskiSystem

/--
greedy Ostrowski block-code を一度 length 列へ戻し、同じ length 列の actual Sturmian path-code へ移す。
-/
noncomputable def greedyLengthCodeToSturmianPathCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (code : List (ℕ → ℕ)) : List (ℕ → ℕ) :=
  D.sturmianPathLengthCode
    (D.horizontalOstrowskiLengthDecode code)

/--
actual Sturmian path-code を一度 length 列へ戻し、同じ length 列の greedy Ostrowski code へ移す。
-/
noncomputable def sturmianPathCodeToGreedyLengthCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (code : List (ℕ → ℕ)) : List (ℕ → ℕ) :=
  D.horizontalOstrowskiLengthCode
    (D.sturmianPathLengthDecode code)

/-- canonical greedy length-code を path-code へ移すと、同じ length 列の canonical path-code になる。 -/
@[simp] theorem greedyLengthCodeToSturmianPathCode_encode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) :
    D.greedyLengthCodeToSturmianPathCode
        (D.horizontalOstrowskiLengthCode rs) =
      D.sturmianPathLengthCode rs := by
  unfold greedyLengthCodeToSturmianPathCode
  rw [D.horizontalOstrowskiLengthDecode_encode]

/-- canonical path length-code を greedy code へ戻すと、同じ length 列の canonical greedy code になる。 -/
@[simp] theorem sturmianPathCodeToGreedyLengthCode_encode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) :
    D.sturmianPathCodeToGreedyLengthCode
        (D.sturmianPathLengthCode rs) =
      D.horizontalOstrowskiLengthCode rs := by
  unfold sturmianPathCodeToGreedyLengthCode
  rw [D.sturmianPathLengthDecode_encode]

/-- canonical greedy code の像では path 化して戻す round trip が exact。 -/
@[simp] theorem sturmianPathCodeToGreedy_after_greedyToPath
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) :
    D.sturmianPathCodeToGreedyLengthCode
        (D.greedyLengthCodeToSturmianPathCode
          (D.horizontalOstrowskiLengthCode rs)) =
      D.horizontalOstrowskiLengthCode rs := by
  rw [D.greedyLengthCodeToSturmianPathCode_encode,
    D.sturmianPathCodeToGreedyLengthCode_encode]

/-- canonical path code の像でも greedy 化して戻す round trip が exact。 -/
@[simp] theorem greedyToPath_after_sturmianPathCodeToGreedy
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) :
    D.greedyLengthCodeToSturmianPathCode
        (D.sturmianPathCodeToGreedyLengthCode
          (D.sturmianPathLengthCode rs)) =
      D.sturmianPathLengthCode rs := by
  rw [D.sturmianPathCodeToGreedyLengthCode_encode,
    D.greedyLengthCodeToSturmianPathCode_encode]

end RotationOstrowskiSystem

namespace RecordFerrers

/--
完成 RecordFerrers の greedy block-code を共通 length 列経由で移すと、actual Sturmian path-code になる。
-/
theorem canonicalOstrowskiDigitCode_to_sturmianPathCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.greedyLengthCodeToSturmianPathCode
        (R.canonicalOstrowskiDigitCode D) =
      R.canonicalSturmianPathCode D := by
  unfold RotationOstrowskiSystem.greedyLengthCodeToSturmianPathCode
  rw [R.decode_canonicalOstrowskiDigitCode D]
  rfl

/--
完成 RecordFerrers の actual path-code を共通 length 列経由で戻すと greedy block-code になる。
-/
theorem canonicalSturmianPathCode_to_ostrowskiDigitCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.sturmianPathCodeToGreedyLengthCode
        (R.canonicalSturmianPathCode D) =
      R.canonicalOstrowskiDigitCode D := by
  unfold RotationOstrowskiSystem.sturmianPathCodeToGreedyLengthCode
  rw [R.decode_canonicalSturmianPathCode D]
  rfl

/--
greedy code と actual path-code をそれぞれ decode すると、同じ canonicalRecordLengths に戻る。
-/
theorem decode_canonicalOstrowskiDigitCode_eq_decode_canonicalSturmianPathCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.horizontalOstrowskiLengthDecode (R.canonicalOstrowskiDigitCode D) =
      D.sturmianPathLengthDecode (R.canonicalSturmianPathCode D) := by
  rw [R.decode_canonicalOstrowskiDigitCode D,
    R.decode_canonicalSturmianPathCode D]

/--
二つの完成 RecordFerrers が greedy code で一致することと、actual path-code で一致することは exact に同値。
-/
theorem canonicalOstrowskiDigitCode_eq_iff_sturmianPathCode_eq
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m) :
    R.canonicalOstrowskiDigitCode D = S.canonicalOstrowskiDigitCode D ↔
      R.canonicalSturmianPathCode D = S.canonicalSturmianPathCode D := by
  constructor
  · intro hCode
    have hLengths :=
      R.canonicalRecordLengths_eq_of_canonicalOstrowskiDigitCode_eq D S hCode
    unfold canonicalSturmianPathCode
    rw [hLengths]
  · intro hCode
    have hLengths :=
      R.canonicalRecordLengths_eq_of_sturmianPathCode_eq D S hCode
    unfold canonicalOstrowskiDigitCode
    rw [hLengths]

/--
canonical input 上では greedy-code shape decoder と path-code shape decoder は同じ shape を返す。
-/
theorem ostrowskiShapeDecoder_eq_sturmianShapeDecoder_on_canonicalCodes
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.ostrowskiRankFerrersShapeFromDigitCode A m
        (R.canonicalOstrowskiDigitCode D) =
      D.sturmianRankFerrersShapeFromPathCode A m
        (R.canonicalSturmianPathCode D) := by
  rw [R.ostrowskiRankFerrersShapeFromDigitCode_eq_rankFerrersShape D A,
    R.sturmianRankFerrersShapeFromPathCode_eq_rankFerrersShape D A]

/--
外部 certificate を残さない canonical greedy Young code を actual Sturmian Young path-code へ移す。
-/
theorem canonicalOstrowskiYoungCode_to_sturmianYoungPathCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    let D : RotationOstrowskiSystem α :=
      RotationOstrowskiExistence.rotationOstrowskiSystem α A
    D.greedyLengthCodeToSturmianPathCode
        (R.canonicalOstrowskiYoungCode A) =
      R.canonicalSturmianYoungPathCode A := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    D.greedyLengthCodeToSturmianPathCode
        (R.canonicalOstrowskiDigitCode D) =
      R.canonicalSturmianPathCode D
  exact R.canonicalOstrowskiDigitCode_to_sturmianPathCode D

/-- certificate-free actual path-code から canonical greedy Young code へ exact に戻る。 -/
theorem canonicalSturmianYoungPathCode_to_ostrowskiYoungCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    let D : RotationOstrowskiSystem α :=
      RotationOstrowskiExistence.rotationOstrowskiSystem α A
    D.sturmianPathCodeToGreedyLengthCode
        (R.canonicalSturmianYoungPathCode A) =
      R.canonicalOstrowskiYoungCode A := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    D.sturmianPathCodeToGreedyLengthCode
        (R.canonicalSturmianPathCode D) =
      R.canonicalOstrowskiDigitCode D
  exact R.canonicalSturmianPathCode_to_ostrowskiDigitCode D

/--
certificate-free な二 code を decode すると、どちらも同じ canonicalRecordLengths を返す。
-/
theorem canonicalYoungCode_decoders_eq
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    let D : RotationOstrowskiSystem α :=
      RotationOstrowskiExistence.rotationOstrowskiSystem α A
    D.horizontalOstrowskiLengthDecode (R.canonicalOstrowskiYoungCode A) =
      D.sturmianPathLengthDecode (R.canonicalSturmianYoungPathCode A) := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    D.horizontalOstrowskiLengthDecode (R.canonicalOstrowskiDigitCode D) =
      D.sturmianPathLengthDecode (R.canonicalSturmianPathCode D)
  exact R.decode_canonicalOstrowskiDigitCode_eq_decode_canonicalSturmianPathCode D

/--
certificate-free canonical codes についても、greedy code の一致と actual path-code の一致は同値。
-/
theorem canonicalOstrowskiYoungCode_eq_iff_sturmianYoungPathCode_eq
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m) :
    R.canonicalOstrowskiYoungCode A = S.canonicalOstrowskiYoungCode A ↔
      R.canonicalSturmianYoungPathCode A = S.canonicalSturmianYoungPathCode A := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    R.canonicalOstrowskiDigitCode D = S.canonicalOstrowskiDigitCode D ↔
      R.canonicalSturmianPathCode D = S.canonicalSturmianPathCode D
  exact R.canonicalOstrowskiDigitCode_eq_iff_sturmianPathCode_eq D S

/--
certificate-free canonical input 上では、greedy Young shape decoder と
actual path-code shape decoder は一致する。
-/
theorem canonicalYoungShapeDecoders_eq
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    canonicalOstrowskiYoungShapeFromCode A m
        (R.canonicalOstrowskiYoungCode A) =
      canonicalSturmianYoungShapeFromPathCode A m
        (R.canonicalSturmianYoungPathCode A) := by
  rw [R.canonicalOstrowskiYoungShapeFromCode_eq_rankFerrersShape A,
    R.canonicalSturmianYoungShapeFromPathCode_eq_rankFerrersShape A]

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
