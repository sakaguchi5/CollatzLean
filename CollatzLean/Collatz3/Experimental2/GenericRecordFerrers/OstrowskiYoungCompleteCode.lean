import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.OstrowskiRankFerrersBridge

/-!
# Collatz3 Experimental2: Ostrowski 桁列による rank-envelope Young/Ferrers 図形の完全符号

前段 `OstrowskiRankFerrersBridge` では、完成 `RecordFerrers` の各 canonical block 長 `r` について

* `r` は `horizontalOstrowskiDigits r` の weighted sum から復元でき、
* 対応する縦落差は同じ Ostrowski data から exact に決まり、
* その drop 列から作った Ferrers shape は `RecordFerrers.rankFerrersShape` と一致する

ところまで閉じた。

このファイルではさらに一段進め、block 長そのものを保存しない。
各 block を canonical horizontal Ostrowski digit 列

`horizontalOstrowskiDigits r : ℕ → ℕ`

だけへ置き換える。

中心結果は次の三段である。

1. `horizontalOstrowskiDigits` は自然数上で injective。
2. digit 列から元の自然数を戻す `horizontalOstrowskiValue` を定義し、
   `decode (encode rs) = rs` を exact に証明する。
3. 完成 `RecordFerrers` の canonical block digit-code だけから
   `canonicalRecordLengths` と rank-envelope Ferrers / Young shape を完全に復元する。

従って固定した無理回転の Ostrowski system に対して、
`canonicalRecordLengths` の各要素の digit 列だけを並べた code は
Young/Ferrers 図形の完全な符号になる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RotationOstrowskiSystem

/-- horizontal canonical digits は、その canonical support 以後ではすべて `0`。 -/
theorem horizontalOstrowskiDigits_eq_zero_of_large
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ)
    {n : ℕ}
    (hn : N + 1 ≤ n) :
    D.horizontalOstrowskiDigits N n = 0 := by
  simpa [horizontalOstrowskiDigits] using
    canonicalOstrowskiDigits_eq_zero_of_large D.horizontalWeights N hn

/--
canonical support より長い prefix を取っても weighted sum は変わらず `N`。

これにより digit 関数そのものを比較するとき、二つの自然数で異なる
canonical support 長を共通の大きな prefix へ持ち上げられる。
-/
theorem horizontalOstrowskiDigits_reconstruct_of_large
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ)
    {t : ℕ}
    (hNt : N + 1 ≤ t) :
    ostrowskiPrefixSum D.horizontalWeights.Q
      (D.horizontalOstrowskiDigits N) t = N := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hNt
  induction s with
  | zero =>
      simpa using D.horizontalOstrowskiDigits_reconstruct N
  | succ s ih =>
      rw [show N + 1 + (s + 1) = (N + 1 + s) + 1 by omega]
      rw [ostrowskiPrefixSum_succ, ih (by omega)]
      rw [D.horizontalOstrowskiDigits_eq_zero_of_large N (by omega)]
      simp

/--
自然数 `N` の horizontal canonical Ostrowski digit 関数は `N` を一意に決める。

support 長は code に別保存しない。二つの digit 関数が等しければ、
両方の support を含む共通 prefix 上の weighted sum を比較して元の自然数が一致する。
-/
theorem horizontalOstrowskiDigits_injective
    {α : ℝ}
    (D : RotationOstrowskiSystem α) :
    Function.Injective D.horizontalOstrowskiDigits := by
  intro M N hDigits
  let t : ℕ := max (M + 1) (N + 1)
  have hM :
      ostrowskiPrefixSum D.horizontalWeights.Q
          (D.horizontalOstrowskiDigits M) t = M :=
    D.horizontalOstrowskiDigits_reconstruct_of_large M
      (by dsimp [t]; omega)
  have hN :
      ostrowskiPrefixSum D.horizontalWeights.Q
          (D.horizontalOstrowskiDigits N) t = N :=
    D.horizontalOstrowskiDigits_reconstruct_of_large N
      (by dsimp [t]; omega)
  calc
    M =
        ostrowskiPrefixSum D.horizontalWeights.Q
          (D.horizontalOstrowskiDigits M) t := hM.symm
    _ =
        ostrowskiPrefixSum D.horizontalWeights.Q
          (D.horizontalOstrowskiDigits N) t := by rw [hDigits]
    _ = N := hN

/--
一つの horizontal Ostrowski digit 列から、その列が canonical code している自然数を戻す。

canonical digit 関数でない入力には `0` を返す。
完成 RecordFerrers の code では必ず canonical digit 関数を入力するため、
後段では `encode → decode` が exact に恒等になる。
-/
noncomputable def horizontalOstrowskiValue
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (d : ℕ → ℕ) : ℕ := by
  classical
  exact
    if h : ∃ N : ℕ, D.horizontalOstrowskiDigits N = d then
      Classical.choose h
    else
      0

/-- canonical horizontal digit 列を復号すると元の自然数へ戻る。 -/
@[simp] theorem horizontalOstrowskiValue_digits
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.horizontalOstrowskiValue (D.horizontalOstrowskiDigits N) = N := by
  have hExists :
      ∃ M : ℕ,
        D.horizontalOstrowskiDigits M = D.horizontalOstrowskiDigits N :=
    ⟨N, rfl⟩
  rw [horizontalOstrowskiValue, dite_eq_left hExists]
  apply D.horizontalOstrowskiDigits_injective
  exact Classical.choose_spec hExists

/--
length 列を、各要素の horizontal canonical Ostrowski digit 関数だけからなる code へ写す。

元の自然数 length は code 側には保存しない。
-/
def horizontalOstrowskiLengthCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) : List (ℕ → ℕ) :=
  rs.map D.horizontalOstrowskiDigits

/-- block digit-code を各要素ごとに復号して length 列へ戻す。 -/
noncomputable def horizontalOstrowskiLengthDecode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (code : List (ℕ → ℕ)) : List ℕ :=
  code.map D.horizontalOstrowskiValue

/--
length 列を Ostrowski digit-code に変換してから復号すると、元の length 列に exact に戻る。

これが block 列レベルの完全符号定理。
-/
@[simp] theorem horizontalOstrowskiLengthDecode_encode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (rs : List ℕ) :
    D.horizontalOstrowskiLengthDecode
        (D.horizontalOstrowskiLengthCode rs) = rs := by
  induction rs with
  | nil =>
      simp [
        horizontalOstrowskiLengthCode,
        horizontalOstrowskiLengthDecode
      ]
  | cons r rs ih =>
      change
        D.horizontalOstrowskiValue
            (D.horizontalOstrowskiDigits r) ::
          D.horizontalOstrowskiLengthDecode
            (D.horizontalOstrowskiLengthCode rs)
          =
        r :: rs
      simp [ih]

/-- length 列の Ostrowski digit-code 写像は injective。 -/
theorem horizontalOstrowskiLengthCode_injective
    {α : ℝ}
    (D : RotationOstrowskiSystem α) :
    Function.Injective D.horizontalOstrowskiLengthCode := by
  intro rs ss hCode
  have hDecoded :=
    congrArg D.horizontalOstrowskiLengthDecode hCode
  simpa using hDecoded

end RotationOstrowskiSystem

namespace RecordFerrers

/--
完成 RecordFerrers の canonical block code。

`canonicalRecordLengths` 自体は保存せず、その各要素 `r` の
`horizontalOstrowskiDigits r` だけを順番どおり保存する。
-/
noncomputable def canonicalOstrowskiDigitCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    List (ℕ → ℕ) :=
  D.horizontalOstrowskiLengthCode
    (canonicalRecordLengths (irrationalRotationRoof α) m R.height)

/-- canonical Ostrowski digit-code から元の `canonicalRecordLengths` を exact に復元する。 -/
@[simp] theorem decode_canonicalOstrowskiDigitCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.horizontalOstrowskiLengthDecode (R.canonicalOstrowskiDigitCode D) =
      canonicalRecordLengths (irrationalRotationRoof α) m R.height := by
  unfold canonicalOstrowskiDigitCode
  exact D.horizontalOstrowskiLengthDecode_encode _

/--
同じ Ostrowski block digit-code を持つ二つの完成 RecordFerrers は、
canonical length 列も exact に一致する。
-/
theorem canonicalRecordLengths_eq_of_canonicalOstrowskiDigitCode_eq
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalOstrowskiDigitCode D =
      S.canonicalOstrowskiDigitCode D) :
    canonicalRecordLengths (irrationalRotationRoof α) m R.height =
      canonicalRecordLengths (irrationalRotationRoof α) m S.height := by
  apply D.horizontalOstrowskiLengthCode_injective
  exact hCode

/--
canonical block の Ostrowski digit-code は rank-envelope Ferrers / Young shape の完全符号。

同じ code を持てば、`canonicalRecordLengths` を経由して shape 全体が exact に一致する。
-/
theorem rankFerrersShape_eq_of_canonicalOstrowskiDigitCode_eq
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalOstrowskiDigitCode D =
      S.canonicalOstrowskiDigitCode D) :
    R.rankFerrersShape = S.rankFerrersShape := by
  apply R.canonicalRecordLengths_complete_for_rankFerrersShape S
  exact R.canonicalRecordLengths_eq_of_canonicalOstrowskiDigitCode_eq D S hCode

/-- 「完全符号」として読む公開 wrapper。 -/
theorem canonicalOstrowskiDigitCode_complete_for_rankFerrersShape
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    (R S : RecordFerrers (irrationalRotationRoof α) m)
    (hCode : R.canonicalOstrowskiDigitCode D =
      S.canonicalOstrowskiDigitCode D) :
    R.rankFerrersShape = S.rankFerrersShape :=
  R.rankFerrersShape_eq_of_canonicalOstrowskiDigitCode_eq D S hCode

end RecordFerrers

namespace RotationOstrowskiSystem

/--
Ostrowski block digit-code だけから rank-envelope Ferrers shape を復元する実際の decoder。

まず各 digit 関数を length へ戻し、その length 列を前段の
`ostrowskiRankFerrersShapeFromLengths` へ渡す。
-/
noncomputable def ostrowskiRankFerrersShapeFromDigitCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (code : List (ℕ → ℕ)) :
    Combinatorics.FerrersShape (m - 1) :=
  D.ostrowskiRankFerrersShapeFromLengths A m
    (D.horizontalOstrowskiLengthDecode code)

end RotationOstrowskiSystem

namespace RecordFerrers

/--
完成 RecordFerrers の canonical Ostrowski digit-code を shape decoder に入れると、
元の rank-envelope Ferrers shape が exact に復元される。
-/
theorem ostrowskiRankFerrersShapeFromDigitCode_eq_rankFerrersShape
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    D.ostrowskiRankFerrersShapeFromDigitCode A m
        (R.canonicalOstrowskiDigitCode D) =
      R.rankFerrersShape := by
  unfold RotationOstrowskiSystem.ostrowskiRankFerrersShapeFromDigitCode
  rw [R.decode_canonicalOstrowskiDigitCode D]
  exact R.ostrowskiRankFerrersShape_eq_rankFerrersShape D A

/--
同じ canonical Ostrowski digit-code は、decoder が返す shape も当然同じ。
これは code → shape が実際の関数として well-defined であることの直接形。
-/
theorem ostrowskiRankFerrersShapeFromDigitCode_eq_of_code_eq
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    {code₁ code₂ : List (ℕ → ℕ)}
    (hCode : code₁ = code₂) :
    D.ostrowskiRankFerrersShapeFromDigitCode A m code₁ =
      D.ostrowskiRankFerrersShapeFromDigitCode A m code₂ := by
  rw [hCode]

/--
存在定理で canonical に選んだ `RotationOstrowskiSystem` を用いる block digit-code。
外部 certificate を引数として残さない。
-/
noncomputable def canonicalOstrowskiYoungCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    List (ℕ → ℕ) :=
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  R.canonicalOstrowskiDigitCode D

/--
存在定理で canonical に選んだ system を用いる shape decoder。
-/
noncomputable def canonicalOstrowskiYoungShapeFromCode
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (code : List (ℕ → ℕ)) :
    Combinatorics.FerrersShape (m - 1) :=
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  D.ostrowskiRankFerrersShapeFromDigitCode A m code

/--
外部 certificate なしの最終復元定理。

任意の無理回転上の完成 RecordFerrers は、各 canonical block の
horizontal Ostrowski digit 列だけを並べた code から、その rank-envelope
Ferrers / Young shape 全体を exact に復元できる。
-/
theorem canonicalOstrowskiYoungShapeFromCode_eq_rankFerrersShape
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    canonicalOstrowskiYoungShapeFromCode A m
        (R.canonicalOstrowskiYoungCode A) =
      R.rankFerrersShape := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    D.ostrowskiRankFerrersShapeFromDigitCode A m
        (R.canonicalOstrowskiDigitCode D) =
      R.rankFerrersShape
  exact R.ostrowskiRankFerrersShapeFromDigitCode_eq_rankFerrersShape D A

/--
canonical system で作った code から length 列も exact に復元できる。
Young/Ferrers shape だけでなく、その canonical horizontal block partition 自体も失われない。
-/
theorem canonicalOstrowskiYoungCode_decodes_to_lengths
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    let D : RotationOstrowskiSystem α :=
      RotationOstrowskiExistence.rotationOstrowskiSystem α A
    D.horizontalOstrowskiLengthDecode (R.canonicalOstrowskiYoungCode A) =
      canonicalRecordLengths (irrationalRotationRoof α) m R.height := by
  dsimp [canonicalOstrowskiYoungCode]
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change
    D.horizontalOstrowskiLengthDecode (R.canonicalOstrowskiDigitCode D) =
      canonicalRecordLengths (irrationalRotationRoof α) m R.height
  exact R.decode_canonicalOstrowskiDigitCode D

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
