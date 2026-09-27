import CollatzLean.Collatz3.CSTCarry.BinaryShift

/-!
# Collatz3 CSTCarry: 三進 final carry と binary shift の exact bridge

`FerrersCarry` の global invariant

  2^H * C + S = 3^P * F

を `mod 2^H` で読むと

  S = 3^P * F  (mod 2^H)

となる。
一方 `BinaryShift` は同じ合同式を解く canonical representative `U` である。
従って final carry `F` と binary shift `U` は mod `2^H` で exact に一致する。

`F < 2^H` が別途証明できれば、合同ではなく ordinary natural equality `F=U` になる。
未証明 frontier はこの最後の boundedness だけに分離される。
-/

namespace Collatz3
namespace CSTCarry

/-- `3^P U = S (mod 2^H)` の解は canonical shift class に一意。 -/
theorem binaryShiftClass_unique
    (P H S : ℕ)
    (x : ZMod (2 ^ H))
    (hx :
      (((3 ^ P : ℕ) : ZMod (2 ^ H)) * x) =
        ((S : ℕ) : ZMod (2 ^ H))) :
    x = binaryShiftClass P H S := by
  have hleading :
      (((3 ^ P : ℕ) : ZMod (2 ^ H))) =
        (↑(threePowBinaryUnit P H) : ZMod (2 ^ H)) := by
    simp [threePowBinaryUnit]
  have hx' :
      (↑(threePowBinaryUnit P H) : ZMod (2 ^ H)) * x =
        ((S : ℕ) : ZMod (2 ^ H)) := by
    rw [← hleading]
    exact hx
  calc
    x =
        (↑((threePowBinaryUnit P H)⁻¹) : ZMod (2 ^ H)) *
          ((↑(threePowBinaryUnit P H) : ZMod (2 ^ H)) * x) := by
            simp
    _ =
        (↑((threePowBinaryUnit P H)⁻¹) : ZMod (2 ^ H)) *
          ((S : ℕ) : ZMod (2 ^ H)) := by
            rw [hx']
    _ = binaryShiftClass P H S := rfl

namespace CarryRealizes

/--
初期 carry `0` の row recurrence の final carry は、Ferrers binary shift class と
`mod 2^H` で exact に一致する。
-/
theorem final_mod_eq_binaryShiftClass
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    ((F : ℕ) : ZMod (2 ^ H)) =
      binaryShiftClass rows.length H (ferrersWeightedDefect rows) := by
  apply binaryShiftClass_unique
  have hInv := h.invariant_zero
  have hCast := congrArg
    (fun n : ℕ => (n : ZMod (2 ^ H))) hInv
  have hCong :
      (((3 ^ rows.length : ℕ) : ZMod (2 ^ H)) *
          ((F : ℕ) : ZMod (2 ^ H))) =
        ((ferrersWeightedDefect rows : ℕ) : ZMod (2 ^ H)) := by
    simpa using hCast.symm
  exact hCong

/-- final carry の ordinary remainder は canonical Ferrers binary shift。 -/
theorem final_mod_eq_ferrersBinaryShift
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    F % (2 ^ H) = ferrersBinaryShift H rows := by
  have hClass := h.final_mod_eq_binaryShiftClass
  have hVal := congrArg ZMod.val hClass
  simpa [ferrersBinaryShift, binaryShift, ZMod.val_natCast] using hVal

/--
final carry が modulus 未満なら、三進 recurrence の final carry と binary shift は
自然数として exact に等しい。
-/
theorem final_eq_ferrersBinaryShift_of_lt
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hF : F < 2 ^ H) :
    F = ferrersBinaryShift H rows := by
  have hMod := h.final_mod_eq_ferrersBinaryShift
  rw [Nat.mod_eq_of_lt hF] at hMod
  exact hMod

end CarryRealizes
end CSTCarry
end Collatz3
