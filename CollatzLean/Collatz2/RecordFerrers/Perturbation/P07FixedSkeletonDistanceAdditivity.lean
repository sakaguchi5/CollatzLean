import CollatzLean.Collatz2.RecordFerrers.Perturbation.P06FerrersCoordinateLocality

/-!
# Record–Ferrers 摂動理論 7: 局所 support と L1 距離の加法性

fixed chord 上の displacement の絶対値和を距離として読む。
二つの変形の support が各 cut で重ならなければ、合成距離は二つの局所距離の和になる。
特に互いに離れた block replacement は metric 上で独立に足し合わされる。
-/

namespace Collatz2
namespace RecordFerrers

/-- fixed-chord profile displacement の L1 距離。terminal を含めても terminal 項は 0。 -/
def profileL1Distance
    {p H : ℕ}
    (u v : FiberPoint p H) : ℕ :=
  Finset.sum (Finset.range (p + 1))
    (fun k => Int.natAbs (profileDisplacement u v k))

/-- pointwise に support が重ならない二変形では L1 距離が exact に加法的。 -/
theorem profileL1Distance_add_of_pointwise_disjoint
    {p H : ℕ}
    (u v z : FiberPoint p H)
    (hDisjoint :
      ∀ k : ℕ,
        k ≤ p →
        profileDisplacement u v k = 0 ∨
          profileDisplacement v z k = 0) :
    profileL1Distance u z =
      profileL1Distance u v + profileL1Distance v z := by
  unfold profileL1Distance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkLe : k ≤ p := by
    have hkLt : k < p + 1 := Finset.mem_range.mp hk
    omega
  rw [profileDisplacement_comp u v z k]
  rcases hDisjoint k hkLe with hUV | hVZ
  · rw [hUV]
    simp
  · rw [hVZ]
    simp

/--
左 block replacement が右 block replacement より完全に手前なら、
二つの compact support は重ならず距離が加法的になる。
-/
theorem profileL1Distance_add_of_ordered_blockReplacements
    {p H s₁ t₁ s₂ t₂ : ℕ}
    {u v z : FiberPoint p H}
    (R₁ : BlockReplacement u v s₁ t₁)
    (R₂ : BlockReplacement v z s₂ t₂)
    (hSep : t₁ ≤ s₂) :
    profileL1Distance u z =
      profileL1Distance u v + profileL1Distance v z := by
  apply profileL1Distance_add_of_pointwise_disjoint u v z
  intro k hk
  by_cases hkRight : t₁ ≤ k
  · exact Or.inl (R₁.outside k hk (Or.inr hkRight))
  · have hkLeft : k ≤ s₂ := by omega
    exact Or.inr (R₂.outside k hk (Or.inl hkLeft))

end RecordFerrers
end Collatz2
