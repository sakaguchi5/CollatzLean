import CollatzLean.Collatz2.RecordFerrers.Record.Canonicality
import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Record–Ferrers RF-A+3: Ferrers lattice / metric completion

既存 `FerrersShape.Le / meet / join / distance` を order-theoretic API と metric API にまとめる。
pointwise min/max が distributive lattice を作り、distance は Ferrers area difference と一致する。
また unit-cover chain の長さが distance と一致することを示す。
-/

namespace Collatz2
namespace RecordFerrers

namespace FerrersShape

instance instPartialOrder (p : ℕ) : PartialOrder (FerrersShape p) where
  le := FerrersShape.Le
  le_refl := FerrersShape.le_refl
  le_trans := fun _ _ _ => FerrersShape.le_trans
  le_antisymm := fun _ _ => FerrersShape.le_antisymm

instance instLattice (p : ℕ) : Lattice (FerrersShape p) where
  sup := FerrersShape.join
  le_sup_left := fun A B => FerrersShape.left_le_join A B
  le_sup_right := fun A B => FerrersShape.right_le_join A B
  sup_le := by
    intro A B C hAC hBC i
    change max (A.column i) (B.column i) ≤ C.column i
    exact max_le (hAC i) (hBC i)
  inf := FerrersShape.meet
  inf_le_left := fun A B => FerrersShape.meet_le_left A B
  inf_le_right := fun A B => FerrersShape.meet_le_right A B
  le_inf := by
    intro A B C hAB hAC i
    change A.column i ≤ min (B.column i) (C.column i)
    exact le_min (hAB i) (hAC i)

instance instDistribLattice (p : ℕ) : DistribLattice (FerrersShape p) where
  le_sup_inf := by
    intro A B C i
    change
      min (max (A.column i) (B.column i))
          (max (A.column i) (C.column i)) ≤
        max (A.column i) (min (B.column i) (C.column i))
    rw [← max_min_distrib_left]

/-- unweighted Ferrers area。 -/
def area
    {p : ℕ}
    (A : FerrersShape p) : ℕ :=
  Finset.sum (Finset.range p) (fun k => A.atNat k)

/-- Ferrers inclusion は area を単調にする。 -/
theorem area_mono
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B) :
    area A ≤ area B := by
  unfold area
  apply Finset.sum_le_sum
  intro k hk
  have hkLt : k < p := Finset.mem_range.mp hk
  simpa [FerrersShape.atNat, hkLt] using hAB ⟨k, hkLt⟩

/-- meet/join は ordinary area に対しても valuation。 -/
theorem area_meet_add_join
    {p : ℕ}
    (A B : FerrersShape p) :
    area (meet A B) + area (join A B) = area A + area B := by
  unfold area
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [atNat_meet, atNat_join]
  by_cases hab : A.atNat k ≤ B.atNat k
  · simp [min_eq_left hab, max_eq_right hab]
  · have hba : B.atNat k ≤ A.atNat k := le_of_not_ge hab
    simp [min_eq_right hba, max_eq_left hba, Nat.add_comm]

/-- inclusion 下では meet は左辺そのもの。 -/
theorem meet_eq_left_of_le
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B) :
    meet A B = A := by
  apply FerrersShape.ext
  intro i
  simp [meet, min_eq_left (hAB i)]

/-- inclusion 下では join は右辺そのもの。 -/
theorem join_eq_right_of_le
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B) :
    join A B = B := by
  apply FerrersShape.ext
  intro i
  simp [join, max_eq_right (hAB i)]

/-- L1 distance + intersection area = union area。 -/
theorem distance_add_area_meet_eq_area_join
    {p : ℕ}
    (A B : FerrersShape p) :
    distance A B + area (meet A B) = area (join A B) := by
  unfold distance area
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [atNat_meet, atNat_join]
  by_cases hab : A.atNat k ≤ B.atNat k
  · rw [min_eq_left hab, max_eq_right hab, Nat.sub_eq_zero_of_le hab]
    omega
  · have hba : B.atNat k ≤ A.atNat k := le_of_not_ge hab
    rw [min_eq_right hba, max_eq_left hba, Nat.sub_eq_zero_of_le hba]
    omega

/-- distance = union area - intersection area。 -/
theorem distance_eq_area_join_sub_area_meet
    {p : ℕ}
    (A B : FerrersShape p) :
    distance A B = area (join A B) - area (meet A B) := by
  have h := distance_add_area_meet_eq_area_join A B
  omega

/-- comparable shapes では distance = area difference。 -/
theorem distance_add_area_eq_of_le
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B) :
    distance A B + area A = area B := by
  have h := distance_add_area_meet_eq_area_join A B
  rw [meet_eq_left_of_le hAB, join_eq_right_of_le hAB] at h
  exact h

/-- comparable shapes では distance = `area B - area A`。 -/
theorem distance_eq_area_sub_of_le
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B) :
    distance A B = area B - area A := by
  have h := distance_add_area_eq_of_le hAB
  omega

/-- Ferrers distance が 0 なら shape は一致する。 -/
theorem eq_of_distance_zero
    {p : ℕ}
    {A B : FerrersShape p}
    (hZero : distance A B = 0) :
    A = B := by
  apply FerrersShape.ext
  intro i
  have hiMem : i.1 ∈ Finset.range p := Finset.mem_range.mpr i.isLt
  have hTermLe :
      (A.atNat i.1 - B.atNat i.1) +
          (B.atNat i.1 - A.atNat i.1) ≤ distance A B := by
    unfold distance
    exact Finset.single_le_sum_of_canonicallyOrdered
      (f := fun k =>
        (A.atNat k - B.atNat k) + (B.atNat k - A.atNat k))
      hiMem
  have hTermZero :
      (A.atNat i.1 - B.atNat i.1) +
          (B.atNat i.1 - A.atNat i.1) = 0 := by
    rw [hZero] at hTermLe
    omega
  have hAt : A.atNat i.1 = B.atNat i.1 := by
    omega
  simpa [FerrersShape.atNat, i.isLt] using hAt

@[simp] theorem distance_eq_zero_iff
    {p : ℕ}
    (A B : FerrersShape p) :
    distance A B = 0 ↔ A = B := by
  constructor
  · exact eq_of_distance_zero
  · intro h
    subst B
    exact distance_self A

/-- Ferrers L1 distance の triangle inequality。 -/
theorem distance_triangle
    {p : ℕ}
    (A B C : FerrersShape p) :
    distance A C ≤ distance A B + distance B C := by
  unfold distance
  calc
    Finset.sum (Finset.range p) (fun k =>
        (A.atNat k - C.atNat k) + (C.atNat k - A.atNat k))
        ≤ Finset.sum (Finset.range p) (fun k =>
            ((A.atNat k - B.atNat k) + (B.atNat k - A.atNat k)) +
              ((B.atNat k - C.atNat k) + (C.atNat k - B.atNat k))) := by
          apply Finset.sum_le_sum
          intro k hk
          omega
    _ =
        Finset.sum (Finset.range p) (fun k =>
            (A.atNat k - B.atNat k) + (B.atNat k - A.atNat k)) +
          Finset.sum (Finset.range p) (fun k =>
            (B.atNat k - C.atNat k) + (C.atNat k - B.atNat k)) := by
          rw [Finset.sum_add_distrib]

/-- one-cell cover: inclusion かつ distance 1。 -/
def IsUnitCover
    {p : ℕ}
    (A B : FerrersShape p) : Prop :=
  A.Le B ∧ distance A B = 1

/-- unit cover は area を exactly 1 増やす。 -/
theorem IsUnitCover.area_succ
    {p : ℕ}
    {A B : FerrersShape p}
    (h : IsUnitCover A B) :
    area B = area A + 1 := by
  have hArea := distance_add_area_eq_of_le h.1
  rw [h.2] at hArea
  omega

/-- inclusion と area +1 から unit cover を回収する。 -/
theorem isUnitCover_of_le_area_succ
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B)
    (hArea : area B = area A + 1) :
    IsUnitCover A B := by
  refine ⟨hAB, ?_⟩
  have h := distance_add_area_eq_of_le hAB
  omega

/-- unit-cell moves を連結した monotone chain。 -/
inductive UnitChain
    {p : ℕ} : FerrersShape p → FerrersShape p → ℕ → Prop
  | refl (A : FerrersShape p) : UnitChain A A 0
  | cons
      {A B C : FerrersShape p}
      {n : ℕ}
      (head : IsUnitCover A B)
      (tail : UnitChain B C n) :
      UnitChain A C (n + 1)

namespace UnitChain

/-- unit chain は始点から終点へ inclusion-monotone。 -/
theorem le
    {p : ℕ}
    {A B : FerrersShape p}
    {n : ℕ}
    (C : UnitChain A B n) :
    A.Le B := by
  induction C with
  | refl A => exact FerrersShape.le_refl A
  | cons hHead hTail ih =>
      exact FerrersShape.le_trans hHead.1 ih

/-- unit chain の終点 area = 始点 area + step 数。 -/
theorem area_eq_add_steps
    {p : ℕ}
    {A B : FerrersShape p}
    {n : ℕ}
    (C : UnitChain A B n) :
    area B = area A + n := by
  induction C with
  | refl A => simp
  | @cons A B C n hHead hTail ih =>
      have hStep := hHead.area_succ
      omega

/-- unit chain は常に geodesic: step 数が endpoint distance と一致。 -/
theorem distance_eq_steps
    {p : ℕ}
    {A B : FerrersShape p}
    {n : ℕ}
    (C : UnitChain A B n) :
    distance A B = n := by
  have hDist := distance_add_area_eq_of_le C.le
  have hArea := C.area_eq_add_steps
  omega

end UnitChain

end FerrersShape

namespace FiberShape

instance instPartialOrder (p H : ℕ) : PartialOrder (FiberShape p H) where
  le := FiberShape.Le
  le_refl := FiberShape.le_refl
  le_trans := fun _ _ _ => FiberShape.le_trans
  le_antisymm := by
    intro A B hAB hBA
    apply FiberShape.ext_shape
    exact FerrersShape.le_antisymm hAB hBA

instance instLattice (p H : ℕ) : Lattice (FiberShape p H) where
  sup := FiberShape.join
  le_sup_left := fun A B => FiberShape.left_le_join A B
  le_sup_right := fun A B => FiberShape.right_le_join A B
  sup_le := by
    intro A B C hAC hBC i
    change max (A.shape.column i) (B.shape.column i) ≤ C.shape.column i
    exact max_le (hAC i) (hBC i)
  inf := FiberShape.meet
  inf_le_left := fun A B => FiberShape.meet_le_left A B
  inf_le_right := fun A B => FiberShape.meet_le_right A B
  le_inf := by
    intro A B C hAB hAC i
    change A.shape.column i ≤ min (B.shape.column i) (C.shape.column i)
    exact le_min (hAB i) (hAC i)

instance instDistribLattice (p H : ℕ) : DistribLattice (FiberShape p H) where
  le_sup_inf := by
    intro A B C i
    change
      min (max (A.shape.column i) (B.shape.column i))
          (max (A.shape.column i) (C.shape.column i)) ≤
        max (A.shape.column i) (min (B.shape.column i) (C.shape.column i))
    rw [← max_min_distrib_left]

/-- fixed-fiber shape の ordinary Ferrers area。 -/
def area
    {p H : ℕ}
    (A : FiberShape p H) : ℕ :=
  FerrersShape.area A.shape

/-- fixed-fiber distance 0 iff equality。 -/
@[simp] theorem distance_eq_zero_iff
    {p H : ℕ}
    (A B : FiberShape p H) :
    FiberShape.distance A B = 0 ↔ A = B := by
  constructor
  · intro h
    apply FiberShape.ext_shape
    apply FerrersShape.eq_of_distance_zero
    exact h
  · intro h
    subst B
    simp [FiberShape.distance]

/-- fixed-fiber triangle inequality。 -/
theorem distance_triangle
    {p H : ℕ}
    (A B C : FiberShape p H) :
    FiberShape.distance A C ≤
      FiberShape.distance A B + FiberShape.distance B C :=
  FerrersShape.distance_triangle A.shape B.shape C.shape

end FiberShape

end RecordFerrers
end Collatz2
