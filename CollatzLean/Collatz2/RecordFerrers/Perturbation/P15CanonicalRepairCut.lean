import CollatzLean.Collatz2.RecordFerrers.Perturbation.P14RoofContactSaturation

/-!
# Record–Ferrers 摂動理論 15: canonical repair cut

壊れた旧 boundary `after` より後で、target path が初めて critical roof に再接触する cut を
repair cut と定義する。自然数順序の最小性を定義に含めることで、その位置は自動的に一意になる。
P14 により、この cut は source clearance を displacement が初めて使い切る点でもある。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- `after` より後にある proper roof contact の候補。 -/
def RepairCandidate
    {p H : ℕ}
    (v : FiberPoint p H)
    (after k : ℕ) : Prop :=
  after < k ∧ k < p ∧ RoofContact v k

/--
`after` より後にある最初の proper roof contact。
`least` により candidate の中で最小であることを直接保持する。
-/
structure RepairCut
    {p H : ℕ}
    (v : FiberPoint p H)
    (after k : ℕ) : Prop where
  candidate : RepairCandidate v after k
  least : ∀ j : ℕ, RepairCandidate v after j → k ≤ j

namespace RepairCut

/-- repair cut は壊れた旧 boundary より strict に後ろ。 -/
theorem after_lt
    {p H after k : ℕ}
    {v : FiberPoint p H}
    (R : RepairCut v after k) :
    after < k :=
  R.candidate.1

/-- repair cut は terminal より前の proper cut。 -/
theorem proper
    {p H after k : ℕ}
    {v : FiberPoint p H}
    (R : RepairCut v after k) :
    k < p :=
  R.candidate.2.1

/-- repair cut では target が critical roof に接触する。 -/
theorem contact
    {p H after k : ℕ}
    {v : FiberPoint p H}
    (R : RepairCut v after k) :
    RoofContact v k :=
  R.candidate.2.2

/-- 同じ target / after に対する repair cut index は一意。 -/
theorem index_unique
    {p H after k l : ℕ}
    {v : FiberPoint p H}
    (A : RepairCut v after k)
    (B : RepairCut v after l) :
    k = l := by
  apply Nat.le_antisymm
  · exact A.least l B.candidate
  · exact B.least k A.candidate

/-- repair cut は任意 source から見て displacement = source clearance の飽和点。 -/
theorem displacement_eq_clearance
    {p H after k : ℕ}
    {u v : FiberPoint p H}
    (R : RepairCut v after k) :
    profileDisplacement u v k = criticalDefectInt u k :=
  displacement_eq_clearance_of_roofContact u v R.contact

/--
repair cut より前には clearance の飽和点は存在しない。
したがって `k` は source から見ても最初の saturation point。
-/
theorem no_earlier_saturation
    {p H after k : ℕ}
    {u v : FiberPoint p H}
    (R : RepairCut v after k)
    {j : ℕ}
    (hAfter : after < j)
    (hBefore : j < k) :
    profileDisplacement u v j ≠ criticalDefectInt u j := by
  intro hSat
  have hRoof : RoofContact v j :=
    roofContact_of_displacement_eq_clearance u v hSat
  have hProper : j < p :=
    lt_trans hBefore R.proper
  have hCandidate : RepairCandidate v after j :=
    ⟨hAfter, hProper, hRoof⟩
  have hLeast := R.least j hCandidate
  omega

end RepairCut

end RecordFerrers
end Collatz2
