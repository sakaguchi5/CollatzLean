import CollatzLean.Collatz3.CSTCarry.ProfileRowBridge
import CollatzLean.Collatz3.CSTCarry.FerrersAffineBudget

/-!
# Collatz3 CSTCarry: Critical.Profile と exact affine defect identity の bridge

`profileCarryRows h` は index `r=m-1,...,0` の順に

* boundary = `beattyIndex r`
* actual   = `checkpoint h r`

を並べる。

従って `FerrersAffineBudget` の boundary/actual Horner 値をそのまま
profile の roof/actual affine numerator として読むことができる。

このファイルは既存 `Critical.profileAffineNumerator` の定義を変更せず、
CSTCarry row orientation に合う薄い wrapper だけを追加する。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/-- profile carry rows を roof/boundary 側の Horner affine 値として読む。 -/
def profileRoofAffineFromRows
    {m : ℕ}
    (h : Profile m) : ℕ :=
  ferrersBoundaryAffine (profileCarryRows h)

/-- profile carry rows を actual/checkpoint 側の Horner affine 値として読む。 -/
def profileActualAffineFromRows
    {m : ℕ}
    (h : Profile m) : ℕ :=
  ferrersActualAffine (profileCarryRows h)

/-- profile row 一行の defect は Beatty roof と checkpoint の 2冪差そのもの。 -/
@[simp] theorem profileFerrersRow_defect_eq
    {m : ℕ}
    (h : Profile m)
    (r : Fin m) :
    (profileFerrersRow h r).defect =
      2 ^ beattyIndex r.1 - 2 ^ checkpoint h r := by
  rfl

/--
## profile-level exact affine difference

`S = B_roof - B_actual` を `profileCarryRows` に直接特殊化した形。
-/
theorem profileWeightedDefect_eq_roofAffine_sub_actualAffine
    {m : ℕ}
    (h : Profile m) :
    ferrersWeightedDefect (profileCarryRows h) =
      profileRoofAffineFromRows h - profileActualAffineFromRows h := by
  exact ferrersWeightedDefect_eq_boundaryAffine_sub_actualAffine
    (profileCarryRows h)

/-- subtraction を使わない additive exact identity。 -/
theorem profileRoofAffine_eq_actualAffine_add_weightedDefect
    {m : ℕ}
    (h : Profile m) :
    profileRoofAffineFromRows h =
      profileActualAffineFromRows h +
        ferrersWeightedDefect (profileCarryRows h) := by
  exact ferrersBoundaryAffine_eq_actualAffine_add_weightedDefect
    (profileCarryRows h)

/-- admissible profile では同じ rows が critical carry row 条件も満たす。 -/
theorem admissible_profile_affineBudget_and_criticalRows
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    profileRoofAffineFromRows h =
        profileActualAffineFromRows h +
          ferrersWeightedDefect (profileCarryRows h) ∧
      CriticalCarryRows m (profileCarryRows h) := by
  exact ⟨profileRoofAffine_eq_actualAffine_add_weightedDefect h,
    criticalCarryRows_profileCarryRows A⟩

end CSTCarry
end Collatz3
