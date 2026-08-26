import CollatzLean.Collatz2.RecordFerrers.Perturbation.P15CanonicalRepairCut
import CollatzLean.Collatz2.Geometry.PrimitiveReducedChristoffelBridge

/-!
# Record–Ferrers 摂動理論 16: primitive + reduced repair の Christoffel 座標化

primitive + StripReduced contracting exponent pair では proper cut の critical roof が
`floor(H*k/p)` と exact に一致する。したがって repair contact は

* target height = `floor(H*k/p)`
* target signed chord rank = `(H*k) mod p`

という Christoffel の floor / remainder 条件へ完全に変換できる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
fixed chord `(p,H)` で height が chord floor に一致すれば、signed chord rank は
Euclidean remainder `(H*k) mod p` そのものになる。
-/
theorem chordRankInt_eq_mod_of_height_eq_chordFloor
    {p H : ℕ}
    (v : FiberPoint p H)
    {k : ℕ}
    (hHeight : v.height k = H * k / p) :
    chordRankInt v.word k = ((H * k) % p : ℤ) := by
  have hPrefix :
      prefixTwoDepth v.word k = H * k / p := by
    simpa [FiberPoint.height] using hHeight
  have hDiv := Nat.mod_add_div (H * k) p
  have hDivZ :
      ((H * k) % p : ℤ) +
          (p : ℤ) * (H * k / p : ℤ) =
        (H * k : ℤ) := by
    exact_mod_cast hDiv
  unfold chordRankInt
  rw [v.twoSteps_eq, v.oddSteps_eq, hPrefix]
  push_cast at hDivZ ⊢
  linarith

/-- primitive + reduced 側で repair contact を読む Christoffel floor/mod 条件。 -/
def ChristoffelRepairCondition
    (P : Word.ContractingExponentPair)
    (v : FiberPoint P.oddCount P.twoDepth)
    (k : ℕ) : Prop :=
  v.height k = P.twoDepth * k / P.oddCount ∧
    chordRankInt v.word k =
      ((P.twoDepth * k) % P.oddCount : ℤ)

/--
primitive + StripReduced pair では proper roof contact と Christoffel floor/mod 条件が exact に同値。
-/
theorem roofContact_iff_christoffelRepairCondition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.oddCount) :
    RoofContact v k ↔ ChristoffelRepairCondition P v k := by
  have hFloor :=
    P.criticalHeight_eq_chordFloor_of_primitive_reduced
      hPrimitive hReduced hkPos hkLt
  constructor
  · intro hRoof
    have hHeight :
        v.height k = P.twoDepth * k / P.oddCount := by
      unfold RoofContact at hRoof
      rw [hFloor] at hRoof
      exact hRoof
    refine ⟨hHeight, ?_⟩
    exact chordRankInt_eq_mod_of_height_eq_chordFloor v hHeight
  · intro hChristoffel
    unfold ChristoffelRepairCondition at hChristoffel
    unfold RoofContact
    rw [hFloor]
    exact hChristoffel.1

/-- repair candidate の roof 条件を Christoffel floor/mod 条件へ置き換えた版。 -/
def ChristoffelRepairCandidate
    (P : Word.ContractingExponentPair)
    (v : FiberPoint P.oddCount P.twoDepth)
    (after k : ℕ) : Prop :=
  after < k ∧ k < P.oddCount ∧ ChristoffelRepairCondition P v k

/--
primitive + StripReduced では ordinary repair candidate と Christoffel repair candidate が exact に同値。
-/
theorem repairCandidate_iff_christoffelRepairCandidate
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (v : FiberPoint P.oddCount P.twoDepth)
    (after k : ℕ) :
    RepairCandidate v after k ↔
      ChristoffelRepairCandidate P v after k := by
  unfold RepairCandidate ChristoffelRepairCandidate
  constructor
  · rintro ⟨hAfter, hkLt, hRoof⟩
    have hkPos : 0 < k := by omega
    refine ⟨hAfter, hkLt, ?_⟩
    exact
      (roofContact_iff_christoffelRepairCondition
        P hPrimitive hReduced v hkPos hkLt).1 hRoof
  · rintro ⟨hAfter, hkLt, hChristoffel⟩
    have hkPos : 0 < k := by omega
    refine ⟨hAfter, hkLt, ?_⟩
    exact
      (roofContact_iff_christoffelRepairCondition
        P hPrimitive hReduced v hkPos hkLt).2 hChristoffel

namespace RepairCut

/--
primitive + StripReduced では canonical repair cut 自身が Christoffel floor/mod 条件を満たす。
-/
theorem christoffelCondition
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    {after k : ℕ}
    (R : RepairCut v after k) :
    ChristoffelRepairCondition P v k := by
  have hkPos : 0 < k := by
    have hAfter := R.after_lt
    omega
  exact
    (roofContact_iff_christoffelRepairCondition
      P hPrimitive hReduced v hkPos R.proper).1 R.contact

/--
primitive + StripReduced repair cut の target rank は Euclidean remainder そのもの。
-/
theorem chordRankInt_eq_mod
    {P : Word.ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {v : FiberPoint P.oddCount P.twoDepth}
    {after k : ℕ}
    (R : RepairCut v after k) :
    chordRankInt v.word k =
      ((P.twoDepth * k) % P.oddCount : ℤ) := by
  exact (R.christoffelCondition hPrimitive hReduced).2

end RepairCut

end RecordFerrers
end Collatz2
