import Mathlib.Data.List.Basic


/-!
# Collatz3 Experimental2: 0/1 自然数列の有限算術

carry 固有の語彙を使わず、各成分が `0` または `1` の有限列に必要な算術だけをまとめる。
-/

namespace Collatz3
namespace Experimental2

/-- 自然数リストの全成分が `1` 以下。 -/
def IsBitList (xs : List ℕ) : Prop :=
  ∀ x : ℕ, x ∈ xs → x ≤ 1

namespace IsBitList

/-- bit list の総和は長さ以下。 -/
theorem sum_le_length
    {xs : List ℕ}
    (H : IsBitList xs) :
    xs.sum ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := H x (by simp)
      have hTail : IsBitList xs := by
        intro y hy
        exact H y (by simp [hy])
      have hIH := ih hTail
      simp only [List.sum_cons, List.length_cons]
      omega

/-- bit list では `sum + zero count = length`。 -/
theorem sum_add_count_zero_eq_length
    {xs : List ℕ}
    (H : IsBitList xs) :
    xs.sum + xs.count 0 = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := H x (by simp)
      have hTail : IsBitList xs := by
        intro y hy
        exact H y (by simp [hy])
      have hIH := ih hTail
      have hxCases : x = 0 ∨ x = 1 := by omega
      rcases hxCases with rfl | rfl <;> simp at hIH ⊢ <;> omega

/-- 総和が最大値 `length` なら全成分 `1`。 -/
theorem eq_replicate_one_of_sum_eq_length
    {xs : List ℕ}
    (H : IsBitList xs)
    (hSum : xs.sum = xs.length) :
    xs = List.replicate xs.length 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := H x (by simp)
      have hTail : IsBitList xs := by
        intro y hy
        exact H y (by simp [hy])
      have hTailBound := hTail.sum_le_length
      have hxOne : x = 1 := by
        simp only [List.sum_cons, List.length_cons] at hSum
        omega
      have hTailSum : xs.sum = xs.length := by
        simp only [List.sum_cons, List.length_cons] at hSum
        omega
      subst x
      have hIH := ih hTail hTailSum
      have hCons :
          1 :: xs = 1 :: List.replicate xs.length 1 :=
        congrArg (fun ys => 1 :: ys) hIH
      simpa only [List.length_cons, List.replicate_succ] using hCons

/-- 非空 bit list の総和が `length-1` なら `0` はちょうど一個。 -/
theorem count_zero_eq_one_of_sum_eq_length_sub_one
    {xs : List ℕ}
    (H : IsBitList xs)
    (hNonempty : xs ≠ [])
    (hSum : xs.sum = xs.length - 1) :
    xs.count 0 = 1 := by
  have hCount := H.sum_add_count_zero_eq_length
  have hPos : 0 < xs.length := List.length_pos_iff.mpr hNonempty
  omega

end IsBitList
end Experimental2
end Collatz3
