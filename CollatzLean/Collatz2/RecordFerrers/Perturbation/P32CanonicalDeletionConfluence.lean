import CollatzLean.Collatz2.RecordFerrers.Perturbation.P31BooleanBoundaryOrder

/-!
# Record–Ferrers 摂動理論 32: 標準境界削除の可換性と合流

P31 の `eraseRetainedBoundary` を一段の標準粗視化とみなす。
pattern 側では削除は冪等かつ可換である。

P30 の choice-free 標準平坦代表へ写すと、異なる順序で二境界を消した経路は
同じ FiberPoint に exact に到達する。
したがって標準平坦 family 上では、二境界削除の diamond は skeleton equality ではなく
FiberPoint equality として閉じる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 一段の canonical boundary deletion。 -/
def CanonicalBoundaryDeletion
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) : Prop :=
  ∃ b : InternalRecordBoundary D,
    R b = true ∧
    S = eraseRetainedBoundary R b

/-- 一段削除は Boolean 順序を strict でなくとも下向きに進む。 -/
theorem CanonicalBoundaryDeletion.le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S : RetainedBoundaryPattern D}
    (h : CanonicalBoundaryDeletion D R S) :
    S.Le R := by
  rcases h with ⟨b, hb, rfl⟩
  exact eraseRetainedBoundary_le R b

/--
保持されている境界を消す一段は pattern を本当に変える。
-/
theorem CanonicalBoundaryDeletion.ne
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S : RetainedBoundaryPattern D}
    (h : CanonicalBoundaryDeletion D R S) :
    S ≠ R := by
  rcases h with ⟨b, hb, rfl⟩
  intro hEq
  have hAt := congrArg (fun T : RetainedBoundaryPattern D => T b) hEq
  simp [eraseRetainedBoundary, hb] at hAt

/-- 二つの境界を消す pattern-level diamond。 -/
theorem twoBoundaryDeletion_pattern_diamond
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (a b : InternalRecordBoundary D) :
    eraseRetainedBoundary (eraseRetainedBoundary R a) b =
      eraseRetainedBoundary (eraseRetainedBoundary R b) a :=
  eraseRetainedBoundary_comm R a b

/--
P30 の標準平坦代表上では、二境界削除の順序を変えても
最終 FiberPoint 自体が exact に同じ。
-/
theorem twoBoundaryDeletion_fiberPoint_diamond
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (a b : InternalRecordBoundary D) :
    canonicalFlatPoint P hPrimitive hReduced u D
        (eraseRetainedBoundary (eraseRetainedBoundary R a) b) =
      canonicalFlatPoint P hPrimitive hReduced u D
        (eraseRetainedBoundary (eraseRetainedBoundary R b) a) := by
  rw [eraseRetainedBoundary_comm R a b]

/-- 同じ境界の重複削除も FiberPoint 上で冪等。 -/
theorem repeatedBoundaryDeletion_fiberPoint_idem
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    canonicalFlatPoint P hPrimitive hReduced u D
        (eraseRetainedBoundary (eraseRetainedBoundary R b) b) =
      canonicalFlatPoint P hPrimitive hReduced u D
        (eraseRetainedBoundary R b) := by
  rw [eraseRetainedBoundary_idem R b]

/--
二つの保持境界 a,b があるとき、どちらを先に消しても
各一段は genuine pattern change で、共通 endpoint を持つ。
-/
theorem exists_canonical_twoDeletion_diamond
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (a b : InternalRecordBoundary D)
    (ha : R a = true)
    (hb : R b = true)
    (hab : a ≠ b) :
    ∃ Ra Rb Rab : RetainedBoundaryPattern D,
      CanonicalBoundaryDeletion D R Ra ∧
      CanonicalBoundaryDeletion D R Rb ∧
      CanonicalBoundaryDeletion D Ra Rab ∧
      CanonicalBoundaryDeletion D Rb Rab ∧
      canonicalFlatPoint P hPrimitive hReduced u D Rab =
        canonicalFlatPoint P hPrimitive hReduced u D
          (eraseRetainedBoundary (eraseRetainedBoundary R b) a) := by
  let Ra := eraseRetainedBoundary R a
  let Rb := eraseRetainedBoundary R b
  let Rab := eraseRetainedBoundary Ra b
  refine ⟨Ra, Rb, Rab, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨a, ha, rfl⟩
  · exact ⟨b, hb, rfl⟩
  · have hbRa : Ra b = true := by
      dsimp [Ra]
      simp [eraseRetainedBoundary, hab.symm, hb]
    exact ⟨b, hbRa, rfl⟩
  · have haRb : Rb a = true := by
      dsimp [Rb]
      simp [eraseRetainedBoundary, hab, ha]
    refine ⟨a, haRb, ?_⟩
    dsimp [Rab, Ra, Rb]
    exact eraseRetainedBoundary_comm R a b
  · dsimp [Rab, Ra]
    rw [eraseRetainedBoundary_comm R a b]

/--
全消去 pattern の標準平坦代表は、削除順序に依存しない canonical endpoint として固定される。
ここでは endpoint 自体を名前付きで与える。
-/
def canonicalNoBoundaryPoint
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint P.oddCount P.twoDepth :=
  canonicalFlatPoint P hPrimitive hReduced u D
    (retainNoBoundaries D)

/-- 全消去 endpoint は FirstCrossing。 -/
theorem canonicalNoBoundaryPoint_firstCrossing
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FirstCrossing
      (canonicalNoBoundaryPoint
        P hPrimitive hReduced u D).word := by
  unfold canonicalNoBoundaryPoint canonicalFlatPoint
  exact canonicalFlatRepresentative_firstCrossing
    P hPrimitive hReduced u D (retainNoBoundaries D)

end RecordFerrers
end Collatz2
