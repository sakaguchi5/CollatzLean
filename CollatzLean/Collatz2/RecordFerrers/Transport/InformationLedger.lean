import CollatzLean.Collatz2.RecordFerrers.Transport.Certificates
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.InformationBoundary
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.TranslationCoordinates

/-!
# Record–Ferrers RF-B1: 既存情報の復元台帳

Phase A までに既に得られている「情報を失わない」定理を、
RF-B0 の証明書語彙で登録する。

ここでの目的は全対象の完全復元ではなく、各情報からどの性質・数値まで
確実に戻せるかを theorem として明示すること。
-/

namespace Collatz2
namespace RecordFerrers

open Word
open Transport

/-- valid word を subtype として扱う。 -/
abbrev ValidWord := {w : Word // Valid w}

/-- valid minimal block を subtype として扱う。 -/
abbrev ValidMinimalWord := {w : Word // ValidMinimalBlock w}

/-- valid word の `(oddSteps, twoSteps, affineConst)` 情報。 -/
structure WordSignature where
  oddCount : ℕ
  twoDepth : ℕ
  translation : ℕ

/-- valid word の三つ組情報。 -/
def validWordSignature (w : ValidWord) : WordSignature :=
  { oddCount := oddSteps w.1
    twoDepth := twoSteps w.1
    translation := affineConst w.1 }

/-- `(oddSteps,twoSteps,affineConst)` は valid word 自体を決定する。 -/
theorem validWordSignature_determines_word :
    DeterminesValue validWordSignature (fun w : ValidWord => w.1) := by
  intro x y h
  apply word_eq_of_same_losslessTriple x.2 y.2
  · exact congrArg WordSignature.oddCount h
  · exact congrArg WordSignature.twoDepth h
  · exact congrArg WordSignature.translation h

/-- fixed chord 上で保持する完全 Ferrers 情報。 -/
def fullFerrersInfo
    {p H : ℕ}
    (x : FiberPoint p H) : FerrersShape p :=
  x.toFerrersShape

/-- 完全 Ferrers 図形は fixed chord の word を決定する。 -/
theorem fullFerrersInfo_determines_word
    {p H : ℕ} :
    DeterminesValue
      (fullFerrersInfo (p := p) (H := H))
      (fun x : FiberPoint p H => x.word) := by
  intro x y h
  exact word_eq_of_same_fullFerrersShape h

/-- 完全 Ferrers 図形は FirstCrossing の真偽も決定する。 -/
theorem fullFerrersInfo_determines_firstCrossing
    {p H : ℕ} :
    DeterminesProp
      (fullFerrersInfo (p := p) (H := H))
      (fun x : FiberPoint p H => FirstCrossing x.word) := by
  intro x y h
  have hw : x.word = y.word :=
    fullFerrersInfo_determines_word h
  constructor <;> intro hF
  · simpa [hw] using hF
  · simpa [hw] using hF

/-- proper cut の高さだけを残した情報。範囲外は 0 とする。 -/
def properHeightInfo
    {p H : ℕ}
    (x : FiberPoint p H) : ℕ → ℕ :=
  fun k => if _hk : k < p then x.height k else 0

/-- proper prefix 高さ全体は fixed chord の word を決定する。 -/
theorem properHeightInfo_determines_word
    {p H : ℕ} :
    DeterminesValue
      (properHeightInfo (p := p) (H := H))
      (fun x : FiberPoint p H => x.word) := by
  intro x y h
  apply FiberPoint.word_eq_of_height_eq
  intro k hk
  have hkEq := congrFun h k
  simpa [properHeightInfo, hk] using hkEq

/-- 完全 Ferrers 図形は affine translation も決定する。 -/
theorem fullFerrersInfo_determines_affineConst
    {p H : ℕ} :
    DeterminesValue
      (fullFerrersInfo (p := p) (H := H))
      (fun x : FiberPoint p H => affineConst x.word) := by
  exact DeterminesValue.comp
    fullFerrersInfo_determines_word
    (by
      intro x y h
      change affineConst x.word = affineConst y.word
      change x.word = y.word at h
      exact congrArg affineConst h)

/-- valid minimal block が持つ局所 `(length,B)` 座標。 -/
def validMinimalCoordinate
    (w : ValidMinimalWord) : ℕ × ℕ :=
  blockTranslationCoordinate w.1

/-- valid minimal block は局所 `(length,B)` 座標だけで決定する。 -/
theorem validMinimalCoordinate_determines_word :
    DeterminesValue validMinimalCoordinate (fun w : ValidMinimalWord => w.1) := by
  intro x y h
  have hLen : oddSteps x.1 = oddSteps y.1 :=
    congrArg Prod.fst h
  have hB : affineConst x.1 = affineConst y.1 :=
    congrArg Prod.snd h
  exact
    validMinimalBlock_unique_of_same_length_affineConst
      x.2 y.2 hLen hB

/--
同じ skeleton 上では translation coordinate 列が block 列そのものを決定する。
-/
theorem translationCoordinates_determine_blocks
    {S : Skeleton} :
    DeterminesValue
      (fun D : ValidDecoratedSkeleton S => D.translationCoordinates)
      (fun D : ValidDecoratedSkeleton S => D.blocks) := by
  intro A B h
  exact A.blocks_eq_of_translationCoordinates_eq B h

end RecordFerrers
end Collatz2
