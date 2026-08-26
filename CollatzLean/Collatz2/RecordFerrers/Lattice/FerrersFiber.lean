import CollatzLean.Collatz2.RecordFerrers.Core.ProfileDisplacement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Record–Ferrers Phase A: Ferrers fiber

fixed-chord word の prefix excess を nondecreasing Ferrers column profile として読む。
このファイルでは ambient Ferrers profile 上の meet / join / distance を独立化する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- `p` 本の column を持つ nondecreasing Ferrers profile。column 0 は word image では 0。 -/
structure FerrersShape (p : ℕ) where
  column : Fin p → ℕ
  mono : Monotone column

namespace FerrersShape



@[ext] theorem ext
    {p : ℕ}
    {A B : FerrersShape p}
    (h : ∀ i : Fin p, A.column i = B.column i) :
    A = B := by
  cases A with
  | mk a ha =>
      cases B with
      | mk b hb =>
          have hab : a = b := funext h
          subst b
          rfl

/-- pointwise Ferrers inclusion。 -/
def Le {p : ℕ} (A B : FerrersShape p) : Prop :=
  ∀ i : Fin p, A.column i ≤ B.column i

@[simp] theorem le_refl {p : ℕ} (A : FerrersShape p) : A.Le A := by
  intro i
  exact le_rfl

theorem le_trans
    {p : ℕ}
    {A B C : FerrersShape p}
    (hAB : A.Le B)
    (hBC : B.Le C) :
    A.Le C := by
  intro i
  exact (hAB i).trans (hBC i)

theorem le_antisymm
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B)
    (hBA : B.Le A) :
    A = B := by
  apply FerrersShape.ext
  intro i
  exact Nat.le_antisymm (hAB i) (hBA i)

/-- pointwise minimum。Ferrers intersection に対応。 -/
def meet {p : ℕ} (A B : FerrersShape p) : FerrersShape p :=
  { column := fun i => min (A.column i) (B.column i)
    mono := by
      intro i j hij
      exact min_le_min (A.mono hij) (B.mono hij) }

/-- pointwise maximum。Ferrers union に対応。 -/
def join {p : ℕ} (A B : FerrersShape p) : FerrersShape p :=
  { column := fun i => max (A.column i) (B.column i)
    mono := by
      intro i j hij
      exact max_le_max (A.mono hij) (B.mono hij) }

@[simp] theorem meet_column
    {p : ℕ}
    (A B : FerrersShape p)
    (i : Fin p) :
    (meet A B).column i = min (A.column i) (B.column i) := rfl

@[simp] theorem join_column
    {p : ℕ}
    (A B : FerrersShape p)
    (i : Fin p) :
    (join A B).column i = max (A.column i) (B.column i) := rfl

@[simp] theorem meet_le_left {p : ℕ} (A B : FerrersShape p) :
    (meet A B).Le A := by
  intro i
  simp [meet]

@[simp] theorem meet_le_right {p : ℕ} (A B : FerrersShape p) :
    (meet A B).Le B := by
  intro i
  simp [meet]

@[simp] theorem left_le_join {p : ℕ} (A B : FerrersShape p) :
    A.Le (join A B) := by
  intro i
  simp [join]

@[simp] theorem right_le_join {p : ℕ} (A B : FerrersShape p) :
    B.Le (join A B) := by
  intro i
  simp [join]

/-- natural-index accessor。range 外では 0。 -/
def atNat
    {p : ℕ}
    (A : FerrersShape p)
    (k : ℕ) : ℕ :=
  if hk : k < p then A.column ⟨k, hk⟩ else 0

@[simp] theorem atNat_of_lt
    {p : ℕ}
    (A : FerrersShape p)
    {k : ℕ}
    (hk : k < p) :
    A.atNat k = A.column ⟨k, hk⟩ := by
  simp [atNat, hk]

@[simp] theorem atNat_meet
    {p : ℕ}
    (A B : FerrersShape p)
    (k : ℕ) :
    (meet A B).atNat k = min (A.atNat k) (B.atNat k) := by
  by_cases hk : k < p
  · simp [atNat, hk, meet]
  · simp [atNat, hk]

@[simp] theorem atNat_join
    {p : ℕ}
    (A B : FerrersShape p)
    (k : ℕ) :
    (join A B).atNat k = max (A.atNat k) (B.atNat k) := by
  by_cases hk : k < p
  · simp [atNat, hk, join]
  · simp [atNat, hk]

/-- L1 / symmetric-difference 型の profile distance。 -/
def distance
    {p : ℕ}
    (A B : FerrersShape p) : ℕ :=
  Finset.sum (Finset.range p) (fun k =>
    (A.atNat k - B.atNat k) + (B.atNat k - A.atNat k))


@[simp] theorem distance_self
    {p : ℕ}
    (A : FerrersShape p) :
    distance A A = 0 := by
  simp [distance]

@[simp] theorem distance_comm
    {p : ℕ}
    (A B : FerrersShape p) :
    distance A B = distance B A := by
  unfold distance
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.add_comm]

end FerrersShape

namespace FiberPoint

/-- fixed-chord word を Ferrers excess profile へ送る。 -/
def toFerrersShape
    {p H : ℕ}
    (x : FiberPoint p H) : FerrersShape p :=
  { column := fun i => x.excessAt i.1
    mono := by
      intro i j hij
      have hijNat : i.1 ≤ j.1 := hij
      exact x.excess_mono hijNat (Nat.le_of_lt j.isLt) }

@[simp] theorem toFerrersShape_column
    {p H : ℕ}
    (x : FiberPoint p H)
    (i : Fin p) :
    x.toFerrersShape.column i = x.excessAt i.1 := rfl

@[simp] theorem toFerrersShape_atNat
    {p H : ℕ}
    (x : FiberPoint p H)
    {k : ℕ}
    (hk : k < p) :
    x.toFerrersShape.atNat k = x.excessAt k := by
  simp [FerrersShape.atNat, hk, toFerrersShape]

/-- fixed fiber image は rectangle height `H-p` 以下。 -/
theorem toFerrersShape_bounded
    {p H : ℕ}
    (x : FiberPoint p H)
    (i : Fin p) :
    x.toFerrersShape.column i ≤ H - p := by
  exact x.excess_le_rectangleHeight (Nat.le_of_lt i.isLt)

/-- word image の第0 column は 0。 -/
theorem toFerrersShape_first_zero
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p) :
    x.toFerrersShape.column ⟨0, hp⟩ = 0 := by
  simp [toFerrersShape]

/-- Ferrers profile encoding は fixed-chord word 上で injective。 -/
theorem toFerrersShape_injective
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hShape : x.toFerrersShape = y.toFerrersShape) :
    x = y := by
  apply FiberPoint.ext
  intro k hkLt
  have hCol := congrArg
    (fun S : FerrersShape p => S.column ⟨k, hkLt⟩) hShape
  change x.excessAt k = y.excessAt k at hCol
  have hx := x.index_le_height (Nat.le_of_lt hkLt)
  have hy := y.index_le_height (Nat.le_of_lt hkLt)
  unfold FiberPoint.excessAt at hCol
  omega

/-- fixed-chord point order = Ferrers inclusion。 -/
def FerrersLe
    {p H : ℕ}
    (x y : FiberPoint p H) : Prop :=
  x.toFerrersShape.Le y.toFerrersShape

end FiberPoint

/--
positive fixed-chord fiber と exact に対応する bounded Ferrers shape。
`p` columns のうち column 0 は常に 0 で、全 column は rectangle height `H-p` 以下。
-/
structure FiberShape (p H : ℕ) where
  shape : FerrersShape p
  p_pos : 0 < p
  p_le_H : p ≤ H
  first_zero : shape.column ⟨0, p_pos⟩ = 0
  bounded : ∀ i : Fin p, shape.column i ≤ H - p

namespace FiberShape

/-- underlying Ferrers shape equality だけで FiberShape equality が決まる。 -/
theorem ext_shape
    {p H : ℕ}
    {A B : FiberShape p H}
    (h : A.shape = B.shape) :
    A = B := by
  cases A
  cases B
  simp_all

/-- terminal column と合わせた excess profile。 -/
def extendedExcess
    {p H : ℕ}
    (S : FiberShape p H)
    (i : Fin (p + 1)) : ℕ :=
  if hi : i.1 < p then
    S.shape.column ⟨i.1, hi⟩
  else
    H - p

@[simp] theorem extendedExcess_zero
    {p H : ℕ}
    (S : FiberShape p H) :
    S.extendedExcess 0 = 0 := by
  have hp : (0 : ℕ) < p := S.p_pos
  simp [extendedExcess, hp, S.first_zero]

@[simp] theorem extendedExcess_last
    {p H : ℕ}
    (S : FiberShape p H) :
    S.extendedExcess (Fin.last p) = H - p := by
  simp [extendedExcess]

/-- consecutive extended excess columns are nondecreasing。 -/
theorem extendedExcess_castSucc_le_succ
    {p H : ℕ}
    (S : FiberShape p H)
    (i : Fin p) :
    S.extendedExcess i.castSucc ≤ S.extendedExcess i.succ := by
  by_cases hnext : i.1 + 1 < p
  · have hcur : i.1 < p := i.isLt
    have hmono :
        S.shape.column ⟨i.1, hcur⟩ ≤
          S.shape.column ⟨i.1 + 1, hnext⟩ := by
      apply S.shape.mono
      change i.1 ≤ i.1 + 1
      omega
    simpa [extendedExcess, hcur, hnext] using hmono
  · have hcur : i.1 < p := i.isLt
    have hbound := S.bounded i
    simpa [extendedExcess, hcur, hnext] using hbound

/-- column difference + baseline one gives the decoded positive exponent。 -/
def exponentAt
    {p H : ℕ}
    (S : FiberShape p H)
    (i : Fin p) : ℕ :=
  1 + (S.extendedExcess i.succ - S.extendedExcess i.castSucc)

/-- Ferrers shape から canonical exponent word を復号する。 -/
def toWord
    {p H : ℕ}
    (S : FiberShape p H) : Word :=
  List.ofFn S.exponentAt

/-- decoded exponents are all positive。 -/
theorem toWord_valid
    {p H : ℕ}
    (S : FiberShape p H) :
    Valid S.toWord := by
  intro e he
  unfold toWord at he
  rw [List.mem_ofFn] at he
  rcases he with ⟨i, rfl⟩
  unfold exponentAt
  omega

@[simp] theorem toWord_oddSteps
    {p H : ℕ}
    (S : FiberShape p H) :
    oddSteps S.toWord = p := by
  simp [toWord, oddSteps]

/-- decoded exponent partial sum telescopes to `index + extendedExcess`。 -/
theorem partialSum_exponentAt
    {p H : ℕ}
    (S : FiberShape p H)
    (i : Fin (p + 1)) :
    Fin.partialSum S.exponentAt i = i.1 + S.extendedExcess i := by
  refine Fin.induction ?_ ?_ i
  · simp
  · intro j ih
    rw [Fin.partialSum_succ, ih]
    unfold exponentAt
    have hle := S.extendedExcess_castSucc_le_succ j
    have hsub := Nat.sub_add_cancel hle
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega

/-- decoded word has exact total depth `H`。 -/
@[simp] theorem toWord_twoSteps
    {p H : ℕ}
    (S : FiberShape p H) :
    twoSteps S.toWord = H := by
  have hPartial :=
    S.partialSum_exponentAt (Fin.last p)
  have hLast :
      Fin.partialSum S.exponentAt (Fin.last p) = H := by
    rw [hPartial, S.extendedExcess_last]
    have hpH : p ≤ H := S.p_le_H
    change p + (H - p) = H
    omega
  unfold Fin.partialSum at hLast
  simp only [Fin.val_last] at hLast
  have hTake :
      List.take p (List.ofFn S.exponentAt) =
        List.ofFn S.exponentAt := by
    simp only [List.take_eq_self_iff, List.length_ofFn, Std.le_refl]
  rw [hTake] at hLast
  simpa [toWord, twoSteps] using hLast

/-- decoded word の proper prefix height は exact に shape column を復元する。 -/
theorem prefixTwoDepth_toWord
    {p H : ℕ}
    (S : FiberShape p H)
    {k : ℕ}
    (hk : k < p) :
    prefixTwoDepth S.toWord k = k + S.shape.atNat k := by
  let i : Fin (p + 1) := ⟨k, by omega⟩
  have hPartial := S.partialSum_exponentAt i
  have hEx : S.extendedExcess i = S.shape.atNat k := by
    simp [i, extendedExcess, FerrersShape.atNat, hk]
  unfold Fin.partialSum at hPartial
  change
    prefixTwoDepth S.toWord k = k + S.shape.atNat k
  unfold prefixTwoDepth toWord
  simpa [twoSteps, i, hEx] using hPartial

/-- exact decoded FiberPoint。 -/
def toFiberPoint
    {p H : ℕ}
    (S : FiberShape p H) : FiberPoint p H :=
  { word := S.toWord
    valid := S.toWord_valid
    oddSteps_eq := S.toWord_oddSteps
    twoSteps_eq := S.toWord_twoSteps }

/-- decoding followed by Ferrers encoding recovers the same shape。 -/
theorem toFerrersShape_toFiberPoint
    {p H : ℕ}
    (S : FiberShape p H) :
    S.toFiberPoint.toFerrersShape = S.shape := by
  apply FerrersShape.ext
  intro i
  have hDepth := S.prefixTwoDepth_toWord i.isLt
  change S.toFiberPoint.excessAt i.1 = S.shape.column i
  unfold FiberPoint.excessAt FiberPoint.height toFiberPoint
  rw [hDepth]
  simp [FerrersShape.atNat, i.isLt]

/-- pointwise inclusion on exact fixed-fiber shapes。 -/
def Le
    {p H : ℕ}
    (A B : FiberShape p H) : Prop :=
  A.shape.Le B.shape

@[simp] theorem le_refl
    {p H : ℕ}
    (A : FiberShape p H) : A.Le A :=
  FerrersShape.le_refl A.shape

theorem le_trans
    {p H : ℕ}
    {A B C : FiberShape p H}
    (hAB : A.Le B)
    (hBC : B.Le C) :
    A.Le C :=
  FerrersShape.le_trans hAB hBC

/-- FiberShape meet。fixed rectangle conditions も保存する。 -/
def meet
    {p H : ℕ}
    (A B : FiberShape p H) : FiberShape p H :=
  { shape := FerrersShape.meet A.shape B.shape
    p_pos := A.p_pos
    p_le_H := A.p_le_H
    first_zero := by
      have hA := A.first_zero
      have hB := B.first_zero
      simp [FerrersShape.meet, hA, hB]
    bounded := by
      intro i
      change
        min (A.shape.column i) (B.shape.column i) ≤ H - p
      exact
        (min_le_left (A.shape.column i) (B.shape.column i)).trans
          (A.bounded i) }

/-- FiberShape join。fixed rectangle conditions も保存する。 -/
def join
    {p H : ℕ}
    (A B : FiberShape p H) : FiberShape p H :=
  { shape := FerrersShape.join A.shape B.shape
    p_pos := A.p_pos
    p_le_H := A.p_le_H
    first_zero := by
      have hA := A.first_zero
      have hB := B.first_zero
      simp [FerrersShape.join, hA, hB]
    bounded := by
      intro i
      change
        max (A.shape.column i) (B.shape.column i) ≤ H - p
      exact max_le (A.bounded i) (B.bounded i) }

/-- meet is below both inputs。 -/
theorem meet_le_left
    {p H : ℕ}
    (A B : FiberShape p H) :
    (meet A B).Le A :=
  FerrersShape.meet_le_left A.shape B.shape

/-- meet is below both inputs。 -/
theorem meet_le_right
    {p H : ℕ}
    (A B : FiberShape p H) :
    (meet A B).Le B :=
  FerrersShape.meet_le_right A.shape B.shape

/-- both inputs are below join。 -/
theorem left_le_join
    {p H : ℕ}
    (A B : FiberShape p H) :
    A.Le (join A B) :=
  FerrersShape.left_le_join A.shape B.shape

/-- both inputs are below join。 -/
theorem right_le_join
    {p H : ℕ}
    (A B : FiberShape p H) :
    B.Le (join A B) :=
  FerrersShape.right_le_join A.shape B.shape

/-- fixed fiber distance = underlying Ferrers L1 distance。 -/
def distance
    {p H : ℕ}
    (A B : FiberShape p H) : ℕ :=
  FerrersShape.distance A.shape B.shape

end FiberShape

namespace FiberPoint

/-- positive fixed-chord point を exact bounded FiberShape に送る。 -/
def toFiberShape
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p) : FiberShape p H :=
  { shape := x.toFerrersShape
    p_pos := hp
    p_le_H := by
      have h := FiberPoint.oddSteps_le_twoSteps_of_valid x.valid
      rw [x.oddSteps_eq, x.twoSteps_eq] at h
      exact h
    first_zero := x.toFerrersShape_first_zero hp
    bounded := x.toFerrersShape_bounded }

/-- encoding after decoding is identity on FiberShape。 -/
theorem toFiberShape_toFiberPoint
    {p H : ℕ}
    (S : FiberShape p H) :
    S.toFiberPoint.toFiberShape S.p_pos = S := by
  apply FiberShape.ext_shape
  exact S.toFerrersShape_toFiberPoint

/-- decoding after encoding is identity on positive fixed-chord points。 -/
theorem toFiberPoint_toFiberShape
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p) :
    (x.toFiberShape hp).toFiberPoint = x := by
  apply FiberPoint.toFerrersShape_injective
  exact (x.toFiberShape hp).toFerrersShape_toFiberPoint

/--
positive fixed-chord valid word fiber と bounded Ferrers shapes の exact equivalence。
これが Phase A の `fixed (p,H) fiber = Ferrers lattice` の formal statement。
-/
def equivFiberShape
    {p H : ℕ}
    (hp : 0 < p) :
    FiberPoint p H ≃ FiberShape p H where
  toFun := fun x => x.toFiberShape hp
  invFun := fun S => S.toFiberPoint
  left_inv := fun x => x.toFiberPoint_toFiberShape hp
  right_inv := fun S => by
    simpa using (FiberPoint.toFiberShape_toFiberPoint S)

end FiberPoint

end RecordFerrers
end Collatz2
