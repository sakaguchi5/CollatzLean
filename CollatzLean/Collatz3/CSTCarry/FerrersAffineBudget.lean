import CollatzLean.Collatz3.CSTCarry.FerrersCarry


/-!
# Collatz3 CSTCarry: Ferrers weighted defect の affine difference 表現

Ferrers row `R` は

* roof / boundary contribution `2^R.boundary`
* actual contribution `2^R.actual`
* defect `2^R.boundary - 2^R.actual`

を持つ。

row list は terminal-to-initial の向きに並び、`ferrersWeightedDefect` と同じ
Horner 順序 `x₀ + 3 x₁ + 3² x₂ + ...` で読む。

このファイルでは boundary/actual の affine 値を同じ Horner 順序で定義し、

  boundaryAffine = actualAffine + ferrersWeightedDefect

を exact に証明する。

従って weighted defect は単なる上界用の量ではなく、roof 側 affine numerator と
actual 側 affine numerator の exact difference として読める。
-/

namespace Collatz3
namespace CSTCarry

/--
terminal-to-initial row listの boundary 側 affine 値。
`ferrersWeightedDefect` と同じ low-3-power-first Horner convention を使う。
-/
def ferrersBoundaryAffine : List FerrersRow → ℕ
  | [] => 0
  | R :: Rs => 2 ^ R.boundary + 3 * ferrersBoundaryAffine Rs

/--
terminal-to-initial row listの actual 側 affine 値。
-/
def ferrersActualAffine : List FerrersRow → ℕ
  | [] => 0
  | R :: Rs => 2 ^ R.actual + 3 * ferrersActualAffine Rs

@[simp] theorem ferrersBoundaryAffine_nil :
    ferrersBoundaryAffine [] = 0 := rfl

@[simp] theorem ferrersBoundaryAffine_cons
    (R : FerrersRow) (Rs : List FerrersRow) :
    ferrersBoundaryAffine (R :: Rs) =
      2 ^ R.boundary + 3 * ferrersBoundaryAffine Rs := rfl

@[simp] theorem ferrersActualAffine_nil :
    ferrersActualAffine [] = 0 := rfl

@[simp] theorem ferrersActualAffine_cons
    (R : FerrersRow) (Rs : List FerrersRow) :
    ferrersActualAffine (R :: Rs) =
      2 ^ R.actual + 3 * ferrersActualAffine Rs := rfl

/--
## exact affine difference identity

任意の Ferrers row list について

`boundaryAffine = actualAffine + weightedDefect`。

profile admissibility や criticality は不要で、row の primitive 条件
`actual ≤ boundary` だけから従う。
-/
theorem ferrersBoundaryAffine_eq_actualAffine_add_weightedDefect
    (rows : List FerrersRow) :
    ferrersBoundaryAffine rows =
      ferrersActualAffine rows + ferrersWeightedDefect rows := by
  induction rows with
  | nil =>
      simp
  | cons R Rs ih =>
      have hPow : 2 ^ R.actual ≤ 2 ^ R.boundary :=
        Nat.pow_le_pow_right
          (by decide : 0 < (2 : ℕ))
          R.actual_le_boundary
      simp only [ferrersBoundaryAffine_cons, ferrersActualAffine_cons,
        ferrersWeightedDefect_cons]
      rw [ih]
      unfold FerrersRow.defect
      omega

/-- weighted defect を ordinary natural subtraction として読む exact 版。 -/
theorem ferrersWeightedDefect_eq_boundaryAffine_sub_actualAffine
    (rows : List FerrersRow) :
    ferrersWeightedDefect rows =
      ferrersBoundaryAffine rows - ferrersActualAffine rows := by
  have h := ferrersBoundaryAffine_eq_actualAffine_add_weightedDefect rows
  omega

/-- actual affine 値は boundary affine 値以下。 -/
theorem ferrersActualAffine_le_boundaryAffine
    (rows : List FerrersRow) :
    ferrersActualAffine rows ≤ ferrersBoundaryAffine rows := by
  have h := ferrersBoundaryAffine_eq_actualAffine_add_weightedDefect rows
  omega

/-- defect が 0 なら boundary/actual affine 値は一致する。 -/
theorem ferrersBoundaryAffine_eq_actualAffine_of_weightedDefect_eq_zero
    {rows : List FerrersRow}
    (hZero : ferrersWeightedDefect rows = 0) :
    ferrersBoundaryAffine rows = ferrersActualAffine rows := by
  have h := ferrersBoundaryAffine_eq_actualAffine_add_weightedDefect rows
  omega

/-- boundary/actual affine 値が一致すれば weighted defect は 0。 -/
theorem ferrersWeightedDefect_eq_zero_of_boundaryAffine_eq_actualAffine
    {rows : List FerrersRow}
    (hEq : ferrersBoundaryAffine rows = ferrersActualAffine rows) :
    ferrersWeightedDefect rows = 0 := by
  have h := ferrersBoundaryAffine_eq_actualAffine_add_weightedDefect rows
  omega

end CSTCarry
end Collatz3
