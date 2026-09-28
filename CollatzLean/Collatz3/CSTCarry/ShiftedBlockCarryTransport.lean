import CollatzLean.Collatz3.CSTCarry.CarryScaleTransport
import CollatzLean.Collatz3.CSTCarry.ProfileBlockRows
import CollatzLean.Collatz3.CSTCarry.ShiftedBlockDefect

/-!
# Collatz3 CSTCarry: shifted local block と global block の exact carry transport

global block `[a,a+r)` の各 row は start roof `a` の scale

`2^beattyIndex a`

を共通因子として持つ。

このファイルでは weighted sum ではなく row ごとに scale relation を作り、
`canonicalCarryRun_scale` へ直接接続する。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/-- start roof から相対化した一つの local Ferrers row。 -/
def shiftedProfileFerrersRow
    {m : ℕ}
    (h : Profile m)
    (a j : ℕ)
    (hLocal :
      localDepth h a j ≤ shiftedBeattyIndex a j) :
    FerrersRow :=
  { boundary := shiftedBeattyIndex a j
    actual := localDepth h a j
    actual_le_boundary := hLocal }

/-- shifted local row の defect は `shiftedBeattyDefect` そのもの。 -/
@[simp] theorem shiftedProfileFerrersRow_defect
    {m : ℕ}
    (h : Profile m)
    (a j : ℕ)
    (hLocal :
      localDepth h a j ≤ shiftedBeattyIndex a j) :
    (shiftedProfileFerrersRow h a j hLocal).defect =
      shiftedBeattyDefect a j (localDepth h a j) := by
  rfl

/--
interval `[a,a+r)` の shifted local rows を carry 向き
`r-1,...,0` で読む。
-/
def shiftedProfileBlockCarryRows
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) :
    (r : ℕ) →
    (∀ j : ℕ, j < r →
      localDepth h a j ≤ beattyIndex j) →
    List FerrersRow
  | 0, _ => []
  | r + 1, hPrefix =>
      shiftedProfileFerrersRow h a r
          (le_trans (hPrefix r (by omega))
            (beattyIndex_le_shiftedBeattyIndex a r)) ::
        shiftedProfileBlockCarryRows h a r
          (fun j hj => hPrefix j (by omega))

@[simp] theorem shiftedProfileBlockCarryRows_length
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) :
    ∀ (r : ℕ)
      (hPrefix :
        ∀ j : ℕ, j < r →
          localDepth h a j ≤ beattyIndex j),
      (shiftedProfileBlockCarryRows h a r hPrefix).length = r
  | 0, _ => rfl
  | r + 1, hPrefix => by
      simp [shiftedProfileBlockCarryRows,
        shiftedProfileBlockCarryRows_length h a r]

/--
local critical block から shifted row constructor に必要な pointwise bound を供給する。
-/
theorem shiftedPrefixBound_of_localCritical
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsLocalCriticalBlock h a r) :
    ∀ j : ℕ, j < r →
      localDepth h a j ≤ beattyIndex j := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [localDepth]
  · exact B.2.2.2 j (Nat.pos_of_ne_zero hj0) hj

/-- local critical block の canonical shifted row list。 -/
def shiftedCriticalBlockCarryRows
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ)
    (B : IsLocalCriticalBlock h a r) :
    List FerrersRow :=
  shiftedProfileBlockCarryRows h a r
    (shiftedPrefixBound_of_localCritical B)

/--
global block rows と shifted local rows は row ごとに exact に

`global defect = 2^beattyIndex(a) * local defect`

を満たす。
-/
theorem profileBlockCarryRows_scaled_shifted
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a : ℕ}
    (hStartRoof : IsRoofCut h a) :
    ∀ (r : ℕ)
      (hEnd : a + r ≤ m)
      (hPrefix :
        ∀ j : ℕ, j < r →
          localDepth h a j ≤ beattyIndex j),
      RowsDefectScaledBy
        (2 ^ beattyIndex a)
        (shiftedProfileBlockCarryRows h a r hPrefix)
        (profileBlockCarryRows h a r hEnd)
  | 0, hEnd, hPrefix => by
      simp [shiftedProfileBlockCarryRows, profileBlockCarryRows,
        RowsDefectScaledBy]
  | r + 1, hEnd, hPrefix => by
      simp only [shiftedProfileBlockCarryRows, profileBlockCarryRows,
        RowsDefectScaledBy]
      constructor
      · have hColumn :=
          profileColumnDefect_eq_scaled_shiftedBeattyDefect
            A hStartRoof (by omega)
            (hPrefix r (by omega))
        rw [profileHeight_of_lt h (by omega)] at hColumn
        rw [FerrersRow.defect]
        simp only [
          profileFerrersRow_boundary,
          profileFerrersRow_actual
        ]
        simpa [shiftedProfileFerrersRow_defect] using hColumn
      · exact profileBlockCarryRows_scaled_shifted
          A hStartRoof r (by omega)
          (fun j hj => hPrefix j (by omega))

/-- local critical block に特殊化した row-by-row scale relation。 -/
theorem profileBlockCarryRows_scaled_shifted_of_localCritical
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r) :
    RowsDefectScaledBy
      (2 ^ beattyIndex a)
      (shiftedCriticalBlockCarryRows h a r B)
      (profileBlockCarryRows h a r B.2.1) := by
  exact profileBlockCarryRows_scaled_shifted
    A hStartRoof r B.2.1
    (shiftedPrefixBound_of_localCritical B)

/--
block start の roof scale を割った canonical carry transport。

`Hglobal = beattyIndex a + Hlocal` なら global block run は
shifted-local run の `2^beattyIndex a` 倍と exact に一致する。
-/
theorem profileBlockCanonicalCarry_scale
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r Hglobal Hlocal E : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r)
    (hH : Hglobal = beattyIndex a + Hlocal) :
    canonicalCarryDigits Hglobal
        (profileBlockCarryRows h a r B.2.1)
        (2 ^ beattyIndex a * E) =
          canonicalCarryDigits Hlocal
            (shiftedCriticalBlockCarryRows h a r B) E ∧
      canonicalFinalCarry Hglobal
        (profileBlockCarryRows h a r B.2.1)
        (2 ^ beattyIndex a * E) =
          2 ^ beattyIndex a *
            canonicalFinalCarry Hlocal
              (shiftedCriticalBlockCarryRows h a r B) E := by
  subst Hglobal
  exact canonicalCarryRun_scale
    (profileBlockCarryRows_scaled_shifted_of_localCritical
      A hStartRoof B)

/--
block start roof scale は canonical final carry を割り切る。

これは boundary divisibility を外部仮定にせず、
exact scale transport から直接得る形。
-/
theorem profileBlockCanonicalFinal_dvd_startScale
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r Hglobal Hlocal E : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r)
    (hH : Hglobal = beattyIndex a + Hlocal) :
    2 ^ beattyIndex a ∣
      canonicalFinalCarry Hglobal
        (profileBlockCarryRows h a r B.2.1)
        (2 ^ beattyIndex a * E) := by
  have hScale :=
    profileBlockCanonicalCarry_scale
      (E := E)
      A hStartRoof B hH
  refine ⟨
    canonicalFinalCarry Hlocal
      (shiftedCriticalBlockCarryRows h a r B) E,
    ?_⟩
  exact hScale.2

end CSTCarry
end Collatz3
