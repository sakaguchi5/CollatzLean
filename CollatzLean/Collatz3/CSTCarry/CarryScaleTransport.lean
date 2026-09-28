import CollatzLean.Collatz3.CSTCarry.CarryDeterministic
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: carry recurrence の exact 2-power scale transport

Carry recurrence は row そのものではなく `row.defect` のみを見る。

従って

* modulus,
* initial carry,
* 各 row defect,
* final carry

を同じ scale 倍すると digit 列は不変である。

ここでは任意 scale の forward theorem と、
`scale = 2^b` に特殊化した canonical run の exact theorem を置く。
-/

namespace Collatz3
namespace CSTCarry

/--
local row 列と global row 列の defect が pointwise に同じ scale だけ違うこと。
orientation は

`global.defect = scale * local.defect`

で固定する。
-/
def RowsDefectScaledBy
    (scale : ℕ) :
    List FerrersRow → List FerrersRow → Prop
  | [], [] => True
  | L :: Ls, G :: Gs =>
      G.defect = scale * L.defect ∧
        RowsDefectScaledBy scale Ls Gs
  | _, _ => False

/-- scaled row relation は長さを保存する。 -/
theorem RowsDefectScaledBy.length_eq
    {scale : ℕ} :
    ∀ {localRows globalRows : List FerrersRow},
      RowsDefectScaledBy scale localRows globalRows →
        localRows.length = globalRows.length
  | [], [], _ => rfl
  | [], _ :: _, h => by
      simp [RowsDefectScaledBy] at h
  | _ :: _, [], h => by
      simp [RowsDefectScaledBy] at h
  | _ :: Ls, _ :: Gs, h => by
      simp only [RowsDefectScaledBy] at h
      simp only [List.length_cons]
      exact congrArg Nat.succ (RowsDefectScaledBy.length_eq h.2)

namespace CarryRealizes

/--
CarryRealizes の forward scale transport。

local recurrence を scale 倍すると同じ ternary digit 列の global recurrence になる。
-/
theorem scale
    {scale M : ℕ}
    {localRows globalRows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (hRows : RowsDefectScaledBy scale localRows globalRows)
    (h : CarryRealizes M localRows E digits F) :
    CarryRealizes
      (scale * M)
      globalRows
      (scale * E)
      digits
      (scale * F) := by
  induction h generalizing globalRows with
  | nil E =>
      cases globalRows with
      | nil =>
          exact CarryRealizes.nil (scale * E)
      | cons G Gs =>
          simp [RowsDefectScaledBy] at hRows
  | cons L Ls E a E' F digits ha hEq hTail ih =>
      cases globalRows with
      | nil =>
          simp [RowsDefectScaledBy] at hRows
      | cons G Gs =>
          simp only [RowsDefectScaledBy] at hRows
          refine CarryRealizes.cons
            (R := G)
            (Rs := Gs)
            (E := scale * E)
            (a := a)
            (E' := scale * E')
            (F := scale * F)
            (digits := digits)
            ha ?_ ?_
          · calc
              scale * E + G.defect + (scale * M) * a
                  =
                scale * (E + L.defect + M * a) := by
                    rw [hRows.1]
                    ring
              _ = scale * (3 * E') := by rw [hEq]
              _ = 3 * (scale * E') := by ring
          · exact ih hRows.2

end CarryRealizes

/--
2-power scale に対する canonical run の exact transport。

`global H = b + Hlocal`、
`global initial = 2^b * local initial`、
row defects も `2^b` 倍なら、

* canonical ternary digits は完全一致,
* global final carry は local final carry の `2^b` 倍

となる。
-/
theorem canonicalCarryRun_scale
    {b H : ℕ}
    {localRows globalRows : List FerrersRow}
    {E : ℕ}
    (hRows :
      RowsDefectScaledBy (2 ^ b) localRows globalRows) :
    canonicalCarryDigits (b + H) globalRows (2 ^ b * E) =
        canonicalCarryDigits H localRows E ∧
      canonicalFinalCarry (b + H) globalRows (2 ^ b * E) =
        2 ^ b * canonicalFinalCarry H localRows E := by
  have hLocal :=
    canonicalCarryRun_realizes H localRows E
  have hScaledRaw :=
    CarryRealizes.scale hRows hLocal
  have hScaled :
      CarryRealizes
        (2 ^ (b + H))
        globalRows
        (2 ^ b * E)
        (canonicalCarryDigits H localRows E)
        (2 ^ b * canonicalFinalCarry H localRows E) := by
    simpa [pow_add, Nat.mul_assoc] using hScaledRaw
  have hCanonical := hScaled.eq_canonical_twoPow
  exact ⟨hCanonical.1.symm, hCanonical.2.symm⟩

end CSTCarry
end Collatz3
