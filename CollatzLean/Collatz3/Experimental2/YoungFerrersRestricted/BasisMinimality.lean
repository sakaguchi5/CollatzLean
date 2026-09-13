import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisRecurrence

/-!
# Collatz3 Experimental2: basis arm の最小性と一意性

successive rank `s_i` と arm `a_i` を使うと leg は `a_i - s_i`。
Frobenius symbol の admissibility は

* `0 ≤ a_i`,
* `0 ≤ a_i - s_i`,
* arm が少なくとも1ずつ減少、
* leg も少なくとも1ずつ減少

だけで書ける。

`IsArmRealization ranks arms` はこの条件を薄い inductive relation として持つ。
その上で `basisArms ranks` が componentwise 最小であり、同じ weight を持つ realization は
basis arm そのものに一致することを証明する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- successive rank を実現する genuine Frobenius arm 列の最小条件。 -/
inductive IsArmRealization : List ℤ → List ℤ → Prop
  | nil : IsArmRealization [] []
  | single (s a : ℤ)
      (arm_nonneg : 0 ≤ a)
      (leg_nonneg : s ≤ a) :
      IsArmRealization [s] [a]
  | cons
      {s t : ℤ}
      {ss : List ℤ}
      {a b : ℤ}
      {as : List ℤ}
      (tail : IsArmRealization (t :: ss) (b :: as))
      (arm_nonneg : 0 ≤ a)
      (leg_nonneg : s ≤ a)
      (arm_strict : b + 1 ≤ a)
      (leg_strict : b + 1 + s - t ≤ a) :
      IsArmRealization (s :: t :: ss) (a :: b :: as)

/-- realization では rank 列と arm 列の長さが一致する。 -/
theorem IsArmRealization.length_eq
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    arms.length = ranks.length := by
  induction h with
  | nil => rfl
  | single => rfl
  | cons tail _ _ _ _ ih =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at ih ⊢
      exact ih

/-- basis arm 自身が rank vector を admissibly 実現する。 -/
theorem basisArms_realizes :
    ∀ ranks : List ℤ,
      IsArmRealization ranks (basisArms ranks)
  | [] => IsArmRealization.nil
  | [s] => by
      by_cases hs : s ≤ 0
      · simp only [basisArms, hs, ↓reduceIte]
        exact IsArmRealization.single s 0 (by omega) (by omega)
      · have hspos : 0 < s := lt_of_not_ge hs
        simp only [basisArms, hs, ↓reduceIte]
        exact IsArmRealization.single s s (by omega) (by omega)
  | s :: t :: ss => by
      have hTail := basisArms_realizes (t :: ss)
      have hLen := basisArms_length (t :: ss)
      cases hBasis : basisArms (t :: ss) with
      | nil =>
          simp [hBasis] at hLen
      | cons b as =>
          rw [hBasis] at hTail
          have hb0 : 0 ≤ b := by
            cases hTail with
            | single _ _ hb0 _ => exact hb0
            | cons _ hb0 _ _ _ => exact hb0
          have htleb : t ≤ b := by
            cases hTail with
            | single _ _ _ hleg => exact hleg
            | cons _ _ hleg _ _ => exact hleg
          by_cases hst : s ≤ t
          · have ha0 : 0 ≤ b + 1 := by omega
            have hsle : s ≤ b + 1 := by omega
            have harm : b + 1 ≤ b + 1 := le_rfl
            have hleg : b + 1 + s - t ≤ b + 1 := by omega
            simpa [basisArms, hBasis, hst] using
              IsArmRealization.cons hTail ha0 hsle harm hleg
          · have hts : t < s := lt_of_not_ge hst
            let a : ℤ := b + 1 + s - t
            have ha0 : 0 ≤ a := by
              dsimp [a]
              omega
            have hsle : s ≤ a := by
              dsimp [a]
              omega
            have harm : b + 1 ≤ a := by
              dsimp [a]
              omega
            have hleg : b + 1 + s - t ≤ a := by
              dsimp [a]
              exact le_rfl
            simpa [basisArms, hBasis, hst, a] using
              IsArmRealization.cons hTail ha0 hsle harm hleg

/-- componentwise `≤` なら和も `≤`。 -/
theorem sum_le_of_forall₂_le :
    ∀ {xs ys : List ℤ},
      List.Forall₂ (fun x y : ℤ => x ≤ y) xs ys →
      xs.sum ≤ ys.sum
  | [], [], List.Forall₂.nil => by simp
  | x :: xs, y :: ys, List.Forall₂.cons hxy htail => by
      have ih := sum_le_of_forall₂_le htail
      simp only [List.sum_cons]
      exact add_le_add hxy ih

/-- basis arm は任意の realization 以下。 -/
theorem basisArms_componentwise_minimal
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    List.Forall₂ (fun x y : ℤ => x ≤ y)
      (basisArms ranks) arms := by
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | single s a ha0 hleg =>
      by_cases hs : s ≤ 0
      · simp only [basisArms, hs, ↓reduceIte, List.forall₂_cons, List.forall₂_same,
         List.not_mem_nil, Std.le_refl,implies_true, and_true]
        exact ha0
      · have hspos : 0 < s := lt_of_not_ge hs
        have hsa : s ≤ a := hleg
        simp only [basisArms, hs, ↓reduceIte, List.forall₂_cons, List.forall₂_same,
         List.not_mem_nil, Std.le_refl,implies_true, and_true]
        exact hsa
  | @cons s t ss a b as hTail ha0 hleg hArm hLeg ih =>
      cases hBasis : basisArms (t :: ss) with
      | nil =>
          have hLen := basisArms_length (t :: ss)
          simp [hBasis] at hLen
      | cons q qs =>
          rw [hBasis] at ih
          cases ih with
          | cons hqb hRest =>
              by_cases hst : s ≤ t
              · have hqb1 : q + 1 ≤ b + 1 := by
                  omega
                have hhead : q + 1 ≤ a := by
                  exact le_trans hqb1 hArm
                simpa [basisArms, hBasis, hst] using
                  List.Forall₂.cons hhead
                    (List.Forall₂.cons hqb hRest)
              · have hts : t < s := lt_of_not_ge hst
                have hhead0 :
                    q + 1 + s - t ≤ b + 1 + s - t := by
                  omega
                have hhead :
                    q + 1 + s - t ≤ a :=
                  le_trans hhead0 hLeg
                simpa [basisArms, hBasis, hst] using
                  List.Forall₂.cons hhead
                    (List.Forall₂.cons hqb hRest)

/-- basis weight は任意 realization の symbol weight 以下。 -/
theorem basisWeightZ_le_symbolWeightZ
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    basisWeightZ ranks ≤ symbolWeightZ ranks arms := by
  have hsum := sum_le_of_forall₂_le (basisArms_componentwise_minimal h)
  unfold basisWeightZ symbolWeightZ
  omega

/-- componentwise `≤` かつ総和一致なら list 自体が一致する。 -/
theorem eq_of_forall₂_le_of_sum_eq :
    ∀ {xs ys : List ℤ},
      List.Forall₂ (fun x y : ℤ => x ≤ y) xs ys →
      xs.sum = ys.sum →
      xs = ys
  | [], [], List.Forall₂.nil, _ => rfl
  | x :: xs, y :: ys, List.Forall₂.cons hxy htail, hsum => by
      have htailLe := sum_le_of_forall₂_le htail
      have hHeadEq : x = y := by
        simp only [List.sum_cons] at hsum
        by_contra hne
        have hxylt : x < y := lt_of_le_of_ne hxy hne
        omega
      subst y
      have hTailSum : xs.sum = ys.sum := by
        simp only [List.sum_cons] at hsum
        omega
      have hTailEq := eq_of_forall₂_le_of_sum_eq htail hTailSum
      simp [hTailEq]

/--
同じ rank vector の realization が basis と同じ weight を持つなら、arm 列は basis と一致する。
これが weight 最小解の一意性。
-/
theorem arms_eq_basisArms_of_weight_eq
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms)
    (hWeight : symbolWeightZ ranks arms = basisWeightZ ranks) :
    arms = basisArms ranks := by
  have hComp := basisArms_componentwise_minimal h
  have hWeight' :
      (ranks.length : ℤ) +
            2 * arms.sum - ranks.sum =
        (ranks.length : ℤ) +
            2 * (basisArms ranks).sum - ranks.sum := by
    simpa [symbolWeightZ, basisWeightZ] using hWeight
  have hSum :
      arms.sum = (basisArms ranks).sum := by
    omega
  have hEq :=
    eq_of_forall₂_le_of_sum_eq hComp hSum.symm
  exact hEq.symm

/-- basis weight を達成する realization は basis arm に限る。 -/
theorem symbolWeightZ_eq_basisWeightZ_iff
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    symbolWeightZ ranks arms = basisWeightZ ranks ↔
      arms = basisArms ranks := by
  constructor
  · exact arms_eq_basisArms_of_weight_eq h
  · intro hEq
    subst arms
    rfl

end YoungFerrersRestricted
end Experimental2
end Collatz3
