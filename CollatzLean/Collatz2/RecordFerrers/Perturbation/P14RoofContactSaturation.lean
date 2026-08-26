import CollatzLean.Collatz2.RecordFerrers.Perturbation.P13PermanentOldBoundaryFailure
import CollatzLean.Collatz2.RecordFerrers.Core.ProfileDisplacement

/-!
# Record–Ferrers 摂動理論 14: roof contact と clearance 飽和

fixed-chord deformation `u -> v` について、target が cut `k` で critical roof に接触することを
source clearance と profile displacement の exact equality として特徴づける。
FirstCrossing 保存条件の不等式が、repair point ではちょうど等号になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- fixed-chord point が cut `k` で critical roof に接触すること。 -/
def RoofContact
    {p H : ℕ}
    (x : FiberPoint p H)
    (k : ℕ) : Prop :=
  x.height k = criticalHeight k

/-- roof contact は signed critical defect が 0 であることと同値。 -/
theorem roofContact_iff_criticalDefectInt_eq_zero
    {p H : ℕ}
    (x : FiberPoint p H)
    (k : ℕ) :
    RoofContact x k ↔ criticalDefectInt x k = 0 := by
  unfold RoofContact criticalDefectInt
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have hCast :
        (x.height k : ℤ) = (criticalHeight k : ℤ) := by
      linarith
    exact_mod_cast hCast

/--
source `u` から target `v` への deformation で、target roof contact は
`displacement = source clearance` と exact に同値。
-/
theorem roofContact_iff_displacement_eq_clearance
    {p H : ℕ}
    (u v : FiberPoint p H)
    (k : ℕ) :
    RoofContact v k ↔
      profileDisplacement u v k = criticalDefectInt u k := by
  rw [roofContact_iff_criticalDefectInt_eq_zero]
  rw [criticalDefectInt_transport]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- target が roof に触れるなら displacement は source clearance を使い切る。 -/
theorem displacement_eq_clearance_of_roofContact
    {p H : ℕ}
    (u v : FiberPoint p H)
    {k : ℕ}
    (hRoof : RoofContact v k) :
    profileDisplacement u v k = criticalDefectInt u k :=
  (roofContact_iff_displacement_eq_clearance u v k).1 hRoof

/-- displacement が source clearance と一致した cut は target の roof contact。 -/
theorem roofContact_of_displacement_eq_clearance
    {p H : ℕ}
    (u v : FiberPoint p H)
    {k : ℕ}
    (hSat : profileDisplacement u v k = criticalDefectInt u k) :
    RoofContact v k :=
  (roofContact_iff_displacement_eq_clearance u v k).2 hSat

/--
source が FirstCrossing なら target FirstCrossing の条件は proper cuts で
`displacement ≤ clearance`。そのうち等号になる点がちょうど roof contact。
-/
theorem firstCrossing_saturation_iff_roofContact
    {p H : ℕ}
    (u v : FiberPoint p H)
    (_hFu : FirstCrossing u.word)
    (_hFv : FirstCrossing v.word)
    {k : ℕ}
    (_hkPos : 0 < k)
    (_hkLt : k < p) :
    profileDisplacement u v k = criticalDefectInt u k ↔
      RoofContact v k :=
  (roofContact_iff_displacement_eq_clearance u v k).symm

end RecordFerrers
end Collatz2
