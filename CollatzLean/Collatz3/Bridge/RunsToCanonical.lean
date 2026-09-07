import CollatzLean.Collatz3.Semantics.Runs
import CollatzLean.Collatz3.Canonical.LiftClassification

/-!
# Collatz3: actual run から canonical arithmetic への一方向 bridge

基礎 affine arithmetic と actual Collatz semantics をここで初めて接続する。
逆向き `EndpointEquation -> Runs` は一般には置かない。
-/

namespace Collatz3

open Word
namespace OddStep

/-- 1 step の actual semantics は singleton word の endpoint equation を満たす。 -/
theorem endpointEquation_singleton
    {e x y : ℕ}
    (h : OddStep e x y) :
    EndpointEquation ([e] : Word) x y := by
  apply (Word.endpointEquation_iff ([e] : Word) x y).2
  simpa using h.equation

end OddStep

namespace Runs

/-- actual run は必ず対応 word の endpoint equation を満たす。 -/
theorem endpointEquation
    {w : Word} {x y : ℕ}
    (h : Runs w x y) :
    w.EndpointEquation x y := by
  induction h with
  | nil =>
      simp
  | @cons e w x m y hstep htail ih =>
      have hHead : EndpointEquation ([e] : Word) x m :=
        hstep.endpointEquation_singleton
      have hJoined := hHead.append ih
      simpa using hJoined

/-- 非空 actual run の start は canonical residue class に属する。 -/
theorem start_mod_eq_canonicalStart
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    x % Word.oddEndpointModulus w = Word.canonicalStart w := by
  exact (h.endpointEquation).start_mod_eq_canonicalStart
    (h.end_odd_of_nonempty hne)

/-- 非空 actual run は canonical pair からの一意な affine lift である。 -/
theorem exists_canonicalLift
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    ∃ k : ℕ,
      x = Word.canonicalStart w + Word.oddEndpointModulus w * k ∧
      y = Word.canonicalEnd w + 2 * (3 ^ Word.oddSteps w) * k := by
  have hEq : w.EndpointEquation x y := h.endpointEquation
  have hy : Odd y := h.end_odd_of_nonempty hne
  exact (Word.endpointEquation_and_odd_iff_exists_lift w x y).1 ⟨hEq, hy⟩

/-- canonical start は同じ非空 actual run の start 以下。 -/
theorem canonicalStart_le_start
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    Word.canonicalStart w ≤ x := by
  exact (h.endpointEquation).canonicalStart_le_start
    (h.end_odd_of_nonempty hne)

end Runs
end Collatz3
