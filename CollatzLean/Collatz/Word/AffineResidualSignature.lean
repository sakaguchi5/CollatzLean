import CollatzLean.Collatz.Word.AffineLowerBound
import CollatzLean.Collatz.Word.AffineDecoder

/-!
# affine decoder residual の exact signature

forward decoder の universal lower boundを、既知の先頭指数で重み付けして強化する。
また残り1〜3文字では affine constant の形そのものが exact に決まる。
-/

namespace Collatz
namespace Word

/--
valid cons word では、先頭指数を使うことで generic lower bound を一段強化できる。
-/
theorem Valid.affineConst_cons_ge_headWeightedMinimum
    {e : ℕ} {w : Collatz.Word}
    (h : Valid (e :: w)) :
    3 ^ oddSteps w +
        2 ^ e * (3 ^ oddSteps w - 2 ^ oddSteps w) ≤
      affineConst (e :: w) := by
  have htail : Valid w := by
    intro a ha
    exact h a (by simp [ha])
  have hmin := htail.threePow_sub_twoPow_le_affineConst
  have hscaled :=
    Nat.mul_le_mul_left (2 ^ e) hmin
  simpa only [affineConst_cons] using
    Nat.add_le_add_left hscaled (3 ^ oddSteps w)

/-- 1文字 residual の affine constant は1。 -/
@[simp] theorem affineConst_singleton (e : ℕ) :
    affineConst ([e] : Collatz.Word) = 1 := by
  simp [affineConst]

/-- 2文字 residual は `3 + 2^e`。 -/
theorem affineConst_pair (e f : ℕ) :
    affineConst ([e, f] : Collatz.Word) = 3 + 2 ^ e := by
  simp [affineConst]

/-- 3文字 residual は `9 + 2^e * (3 + 2^f)`。 -/
theorem affineConst_triple (e f g : ℕ) :
    affineConst ([e, f, g] : Collatz.Word) =
      9 + 2 ^ e * (3 + 2 ^ f) := by
  simp [affineConst]

/-- valid length 1 residual の exact signature。 -/
theorem Valid.affine_signature_of_length_one
    {w : Collatz.Word}
    (h : Valid w)
    (hlen : w.length = 1) :
    affineConst w = 1 := by
  cases w with
  | nil =>
      simp at hlen
  | cons e w =>
      cases w with
      | nil =>
          simp [affineConst]
      | cons f w =>
          simp at hlen

/--
valid length 2 residual では `B-3` は先頭 exponent の純2冪。
-/
theorem Valid.exists_affine_sub_three_eq_twoPow_of_length_two
    {w : Collatz.Word}
    (h : Valid w)
    (hlen : w.length = 2) :
    ∃ e : ℕ, 0 < e ∧ affineConst w - 3 = 2 ^ e := by
  cases w with
  | nil =>
      simp at hlen
  | cons e w =>
      cases w with
      | nil =>
          simp at hlen
      | cons f w =>
          cases w with
          | nil =>
              have he : 0 < e := h e (by simp)
              refine ⟨e, he, ?_⟩
              simp [affineConst]
          | cons g w =>
              simp at hlen

/-- valid length 3 residual の exact nested signature。 -/
theorem Valid.exists_affine_signature_of_length_three
    {w : Collatz.Word}
    (h : Valid w)
    (hlen : w.length = 3) :
    ∃ e f : ℕ,
      0 < e ∧
      0 < f ∧
      affineConst w = 9 + 2 ^ e * (3 + 2 ^ f) := by
  cases w with
  | nil =>
      simp at hlen
  | cons e w =>
      cases w with
      | nil =>
          simp at hlen
      | cons f w =>
          cases w with
          | nil =>
              simp at hlen
          | cons g w =>
              cases w with
              | nil =>
                  have he : 0 < e := h e (by simp)
                  have hf : 0 < f := h f (by simp)
                  refine ⟨e, f, he, hf, ?_⟩
                  exact affineConst_triple e f g
              | cons a w =>
                  simp at hlen

end Word
end Collatz
