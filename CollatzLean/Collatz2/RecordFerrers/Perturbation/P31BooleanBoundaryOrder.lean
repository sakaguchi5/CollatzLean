import CollatzLean.Collatz2.RecordFerrers.Perturbation.P30CanonicalFlatRepresentatives

/-!
# Record–Ferrers 摂動理論 31: Boolean 境界順序

P29 で導入した内部 Record 境界の保持 pattern に対し、
「残している境界の包含」を順序として整理する。

ここでは粗視化後の境界番号を追跡しない。
元の canonical internal boundary を Bool で残す / 消すというデータだけで、
meet / join / complement と一境界削除を扱う。

P30 の標準平坦代表写像はこの Boolean family 上で単射なので、
次段では削除図式を actual FiberPoint の equality へ持ち上げられる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace RetainedBoundaryPattern

/-- Boolean 境界順序は反射的。 -/
theorem le_refl
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D) :
    R.Le R := by
  intro i hi
  exact hi

/-- Boolean 境界順序は推移的。 -/
theorem le_trans
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S T : RetainedBoundaryPattern D}
    (hRS : R.Le S)
    (hST : S.Le T) :
    R.Le T := by
  intro i hi
  exact hST i (hRS i hi)

/-- Boolean 境界順序は反対称。 -/
theorem le_antisymm
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S : RetainedBoundaryPattern D}
    (hRS : R.Le S)
    (hSR : S.Le R) :
    R = S := by
  funext i
  cases hR : R i <;> cases hS : S i
  · rfl
  · exfalso
    have := hSR i (by simp only [hS])
    simp [hR] at this
  · exfalso
    have := hRS i (by simp only [hR])
    simp [hS] at this
  · rfl

/-- 全消去 pattern は最小元。 -/
theorem none_le
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    (retainNoBoundaries D).Le R := by
  intro i hi
  simp [retainNoBoundaries] at hi

/-- 全保持 pattern は最大元。 -/
theorem le_all
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    R.Le (retainAllBoundaries D) := by
  intro i hi
  simp [retainAllBoundaries]

/-- meet は左入力以下。 -/
theorem meet_le_left
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    (retainedMeet R S).Le R := by
  intro i hi
  cases hR : R i <;> cases hS : S i <;>
    simp [retainedMeet, hR, hS] at hi ⊢

/-- meet は右入力以下。 -/
theorem meet_le_right
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    (retainedMeet R S).Le S := by
  intro i hi
  cases hR : R i <;> cases hS : S i <;>
    simp [retainedMeet, hR, hS] at hi ⊢

/-- 両方以下の pattern は meet 以下。 -/
theorem le_meet
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {T R S : RetainedBoundaryPattern D}
    (hTR : T.Le R)
    (hTS : T.Le S) :
    T.Le (retainedMeet R S) := by
  intro i hi
  have hR := hTR i hi
  have hS := hTS i hi
  cases hRi : R i <;> cases hSi : S i <;>
    simp [retainedMeet, hRi, hSi] at hR hS ⊢

/-- 左入力は join 以下。 -/
theorem left_le_join
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    R.Le (retainedJoin R S) := by
  intro i hi
  cases hR : R i <;> cases hS : S i <;>
    simp [retainedJoin, hR, hS] at hi ⊢

/-- 右入力は join 以下。 -/
theorem right_le_join
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    S.Le (retainedJoin R S) := by
  intro i hi
  cases hR : R i <;> cases hS : S i <;>
    simp [retainedJoin, hR, hS] at hi ⊢

/-- 両入力の上界は join の上界。 -/
theorem join_le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S T : RetainedBoundaryPattern D}
    (hRT : R.Le T)
    (hST : S.Le T) :
    (retainedJoin R S).Le T := by
  intro i hi
  cases hR : R i <;> cases hS : S i
  · simp [retainedJoin, hR, hS] at hi
  · exact hST i (by simp only [hS])
  · exact hRT i (by simp only [hR])
  · exact hRT i (by simp only [hR])

end RetainedBoundaryPattern

/--
既存 pattern から一つの内部境界だけを消す。
すでに消えている境界に適用しても pattern は変わらない。
-/
def eraseRetainedBoundary
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    RetainedBoundaryPattern D :=
  fun i => if i = b then false else R i

@[simp] theorem eraseRetainedBoundary_at
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    eraseRetainedBoundary R b b = false := by
  simp [eraseRetainedBoundary]

@[simp] theorem eraseRetainedBoundary_of_ne
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    {b i : InternalRecordBoundary D}
    (h : i ≠ b) :
    eraseRetainedBoundary R b i = R i := by
  simp [eraseRetainedBoundary, h]

/-- 一境界削除は Boolean 順序を下向きに進む。 -/
theorem eraseRetainedBoundary_le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    (eraseRetainedBoundary R b).Le R := by
  intro i hi
  by_cases h : i = b
  · subst i
    simp [eraseRetainedBoundary] at hi
  · simpa [eraseRetainedBoundary, h] using hi

/-- 同じ境界を二度消しても変わらない。 -/
@[simp] theorem eraseRetainedBoundary_idem
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    eraseRetainedBoundary (eraseRetainedBoundary R b) b =
      eraseRetainedBoundary R b := by
  funext i
  by_cases h : i = b <;>
    simp [eraseRetainedBoundary, h]

/-- 異なる二境界の削除は可換。 -/
theorem eraseRetainedBoundary_comm
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (a b : InternalRecordBoundary D) :
    eraseRetainedBoundary (eraseRetainedBoundary R a) b =
      eraseRetainedBoundary (eraseRetainedBoundary R b) a := by
  funext i
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    simp [eraseRetainedBoundary, hia, hib]

/-- 一境界削除が何も変えないことと、その境界が既に消えていることは同値。 -/
theorem eraseRetainedBoundary_eq_self_iff
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    eraseRetainedBoundary R b = R ↔ R b = false := by
  constructor
  · intro hEq
    have hAt := congrArg (fun T : RetainedBoundaryPattern D => T b) hEq
    simpa [eraseRetainedBoundary] using hAt
  · intro hb
    funext i
    by_cases hib : i = b
    · subst i
      simp [eraseRetainedBoundary, hb]
    · simp [eraseRetainedBoundary, hib]

/-- Boolean meet が左入力に一致することは、左入力が右入力以下であることと同値。 -/
theorem retainedMeet_eq_left_iff_le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    retainedMeet R S = R ↔ R.Le S := by
  constructor
  · intro hEq
    have h := RetainedBoundaryPattern.meet_le_right R S
    rw [hEq] at h
    exact h
  · intro hRS
    apply RetainedBoundaryPattern.le_antisymm
    · exact RetainedBoundaryPattern.meet_le_left R S
    · exact RetainedBoundaryPattern.le_meet
        (RetainedBoundaryPattern.le_refl R) hRS

/-- Boolean join が右入力に一致することは、左入力が右入力以下であることと同値。 -/
theorem retainedJoin_eq_right_iff_le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    retainedJoin R S = S ↔ R.Le S := by
  constructor
  · intro hEq
    have h := RetainedBoundaryPattern.left_le_join R S
    rw [hEq] at h
    exact h
  · intro hRS
    apply RetainedBoundaryPattern.le_antisymm
    · exact RetainedBoundaryPattern.join_le
        hRS (RetainedBoundaryPattern.le_refl S)
    · exact RetainedBoundaryPattern.right_le_join R S

/-- P30 の標準平坦代表写像を短い名前で固定する。 -/
def canonicalFlatPoint
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    RetainedBoundaryPattern D →
      FiberPoint P.oddCount P.twoDepth :=
  fun R => canonicalFlatRepresentative
    P hPrimitive hReduced u D R

/-- 標準平坦代表写像は単射。 -/
theorem canonicalFlatPoint_injective
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    Function.Injective
      (canonicalFlatPoint P hPrimitive hReduced u D) := by
  exact canonicalFlatRepresentative_injective
    P hPrimitive hReduced u D

end RecordFerrers
end Collatz2
