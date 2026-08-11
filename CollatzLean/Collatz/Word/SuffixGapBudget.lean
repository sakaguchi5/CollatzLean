import CollatzLean.Collatz.Word.Geometry

/-!
# all-suffix contracting 語の exact gap budget

`AllSuffixesContracting` から得られる

  `3 * affineConst w < oddSteps w * 2 ^ twoSteps w`

を、単なる不等式ではなく exact equality に分解する。
各 nonempty suffix の contracting gap を、そこまでの head の2冪で重み付けして
再帰的に足した量を `suffixGapBudget` とする。
-/

namespace Collatz
namespace Word

/--
全 nonempty suffix の contracting gap を head 側2冪で重み付けした exact budget。
空語では0。
-/
def suffixGapBudget : Collatz.Word → ℕ
  | [] => 0
  | e :: w =>
      (2 ^ twoSteps (e :: w) - 3 ^ oddSteps (e :: w)) +
        2 ^ e * suffixGapBudget w

@[simp] theorem suffixGapBudget_nil :
    suffixGapBudget ([] : Collatz.Word) = 0 := rfl

@[simp] theorem suffixGapBudget_cons (e : ℕ) (w : Collatz.Word) :
    suffixGapBudget (e :: w) =
      (2 ^ twoSteps (e :: w) - 3 ^ oddSteps (e :: w)) +
        2 ^ e * suffixGapBudget w := rfl

/--
all-suffix contracting 語では sharp affine budget が exact equality になる。

`oddSteps*w 2^H = 3B + suffixGapBudget`。
-/
theorem AllSuffixesContracting.oddSteps_mul_twoPow_eq_three_mul_affine_add_suffixGapBudget
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w) :
    oddSteps w * 2 ^ twoSteps w =
      3 * affineConst w + suffixGapBudget w := by
  induction w with
  | nil =>
      simp [suffixGapBudget, oddSteps, twoSteps, affineConst]
  | cons e w ih =>
      change Contracting (e :: w) ∧ AllSuffixesContracting w at hAll
      rcases hAll with ⟨hWhole, hTail⟩
      have hi := ih hTail
      have hgap :
          3 ^ oddSteps (e :: w) +
              (2 ^ twoSteps (e :: w) - 3 ^ oddSteps (e :: w)) =
            2 ^ twoSteps (e :: w) := by
        exact Nat.add_sub_of_le (Nat.le_of_lt hWhole)
      calc
        oddSteps (e :: w) * 2 ^ twoSteps (e :: w)
            = 2 ^ (e + twoSteps w) +
                2 ^ e * (oddSteps w * 2 ^ twoSteps w) := by
                  simp only [oddSteps_cons, twoSteps_cons, pow_add]
                  ring
        _ =
            (3 ^ oddSteps (e :: w) +
                (2 ^ twoSteps (e :: w) - 3 ^ oddSteps (e :: w))) +
              2 ^ e *
                (3 * affineConst w + suffixGapBudget w) := by
                  rw [hgap, hi, twoSteps_cons]
        _ =
            3 * affineConst (e :: w) + suffixGapBudget (e :: w) := by
              simp only [affineConst_cons, suffixGapBudget_cons,
                oddSteps_cons, twoSteps_cons, pow_succ]
              ring

/-- 非空 all-suffix contracting 語では exact suffix-gap budget は正。 -/
theorem AllSuffixesContracting.suffixGapBudget_pos
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    0 < suffixGapBudget w := by
  cases w with
  | nil => contradiction
  | cons e w =>
      change Contracting (e :: w) ∧ AllSuffixesContracting w at hAll
      have hgap :
          0 < 2 ^ twoSteps (e :: w) - 3 ^ oddSteps (e :: w) :=
        Nat.sub_pos_of_lt hAll.1
      simp only [suffixGapBudget_cons]
      omega

end Word
end Collatz
