import CollatzLean.Collatz3.Experimental2.FiniteComposition

/-!
# Collatz3 Experimental2: 二分 refinement と内部 carry

有限幅の二分木として block refinement を表し、
leaf roof と内部 carry の exact factorization を証明する。
-/

namespace Collatz3
namespace Experimental2

inductive WidthRefinement where
  | leaf (r : ℕ)
  | node (left right : WidthRefinement)
  deriving Repr

namespace WidthRefinement

def width : WidthRefinement → ℕ
  | .leaf r => r
  | .node l r => width l + width r

def leaves : WidthRefinement → List ℕ
  | .leaf r => [r]
  | .node l r => leaves l ++ leaves r

def internalCount : WidthRefinement → ℕ
  | .leaf _ => 0
  | .node l r => internalCount l + internalCount r + 1

def internalCarries
    (β : ℕ → ℕ) : WidthRefinement → List ℕ
  | .leaf _ => []
  | .node l r =>
      roofCarry β l.width r.width ::
        (l.internalCarries β ++ r.internalCarries β)

@[simp] theorem leaves_sum :
    ∀ t : WidthRefinement, t.leaves.sum = t.width
  | .leaf r => by simp [leaves, width]
  | .node l r => by simp [leaves, width, leaves_sum l, leaves_sum r]

@[simp] theorem internalCarries_length
    {β : ℕ → ℕ} :
    ∀ t : WidthRefinement,
      (t.internalCarries β).length = t.internalCount
  | .leaf r => by simp [internalCarries, internalCount]
  | .node l r => by
      simp [internalCarries, internalCount,
        internalCarries_length (β := β) l,
        internalCarries_length (β := β) r]

@[simp] theorem internalCount_add_one_eq_leaves_length :
    ∀ t : WidthRefinement,
      t.internalCount + 1 = t.leaves.length
  | .leaf r => by simp [internalCount, leaves]
  | .node l r => by
      have hL := internalCount_add_one_eq_leaves_length l
      have hR := internalCount_add_one_eq_leaves_length r
      simp only [internalCount, leaves, List.length_append]
      omega

end WidthRefinement

namespace HasUnitCarry

/-- refinement 内部 carry 列も bit list。 -/
theorem refinement_internalCarries_isBitList
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ t : WidthRefinement,
      IsBitList (t.internalCarries β)
  | .leaf _ => by
      intro c hc
      simp [WidthRefinement.internalCarries] at hc
  | .node l r => by
      intro c hc
      simp only [WidthRefinement.internalCarries,
        List.mem_cons, List.mem_append] at hc
      rcases hc with hRoot | hLeft | hRight
      · subst c
        exact U.carry_le_one l.width r.width
      · exact U.refinement_internalCarries_isBitList l c hLeft
      · exact U.refinement_internalCarries_isBitList r c hRight

/-- refinement tree の exact roof factorization。 -/
theorem refinement_roof_eq_leafRoofs_add_internalCarries
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ t : WidthRefinement,
      β t.width =
        (t.leaves.map β).sum + (t.internalCarries β).sum
  | .leaf r => by
      simp [WidthRefinement.width, WidthRefinement.leaves,
        WidthRefinement.internalCarries]
  | .node l r => by
      have hAdd := U.add_eq l.width r.width
      have hLeft := U.refinement_roof_eq_leafRoofs_add_internalCarries l
      have hRight := U.refinement_roof_eq_leafRoofs_add_internalCarries r
      simp only [WidthRefinement.width, WidthRefinement.leaves,
        WidthRefinement.internalCarries, List.map_append,
        List.sum_append, List.sum_cons]
      omega

/-- leaf 数 `-1` の最大 budget なら全内部 carry は `1`。 -/
theorem refinement_all_internalCarries_one_of_leafBudget
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (t : WidthRefinement)
    (hMax :
      (t.internalCarries β).sum = t.leaves.length - 1) :
    t.internalCarries β =
      List.replicate (t.leaves.length - 1) 1 := by
  have hCount :=
    WidthRefinement.internalCount_add_one_eq_leaves_length t
  have hLen :=
    WidthRefinement.internalCarries_length (β := β) t
  have hBudget :
      t.internalCount = t.leaves.length - 1 := by
    omega
  have hMaxLen :
      (t.internalCarries β).sum =
        (t.internalCarries β).length := by
    rw [hLen]
    omega
  have H :=
    U.refinement_internalCarries_isBitList t
  have hAll :=
    H.eq_replicate_one_of_sum_eq_length hMaxLen
  simpa [hLen, hBudget] using hAll

end HasUnitCarry
end Experimental2
end Collatz3
