import CollatzLean.Collatz2.RecordFerrers.Deformation.SplitMerge

/-!
# Record–Ferrers Phase A: block permutation

critical carry cocycle から、terminal block より前の adjacent interior blocks の交換が
carry condition を保存することを導く。arbitrary permutation は adjacent swaps の反復で
生成されるため、その局所生成則を pure theorem として保持する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 二つの adjacent blocks がともに interior である carry packet。 -/
def InteriorPairCarry (a r s : ℕ) : Prop :=
  criticalCarry a r = 1 ∧ criticalCarry (a + r) s = 1

/-- adjacent interior pair を交換しても二つの carry は 1 のまま。 -/
theorem interiorPairCarry_swap
    (a r s : ℕ)
    (h : InteriorPairCarry a r s) :
    InteriorPairCarry a s r := by
  have hLocal := mergeCompatible_of_two_interior_carries a r s h.1 h.2
  have hRS : criticalCarry r s = 1 := hLocal.1
  have hOuter : criticalCarry a (r + s) = 1 := hLocal.2
  have hSR : criticalCarry s r = 1 := by
    calc
      criticalCarry s r = criticalCarry r s := Skeleton.criticalCarry_comm s r
      _ = 1 := hRS
  have hCocycle := criticalCarry_cocycle a s r
  have hASLe := criticalCarry_le_one a s
  have hTailLe := criticalCarry_le_one (a + s) r
  rw [hSR] at hCocycle
  have hOuter' : criticalCarry a (s + r) = 1 := by
    simpa [Nat.add_comm] using hOuter
  rw [hOuter'] at hCocycle
  unfold InteriorPairCarry
  omega

namespace Skeleton

/-- list の先頭二 block を交換する pure operation。 -/
def swapFirstTwo : List ℕ → List ℕ
  | r :: s :: rs => s :: r :: rs
  | rs => rs

@[simp] theorem swapFirstTwo_three
    (r s t : ℕ)
    (rs : List ℕ) :
    swapFirstTwo (r :: s :: t :: rs) = s :: r :: t :: rs := rfl

/-- full carry condition で先頭二 block が interior なら、その交換も admissible。 -/
theorem carryCondition_swap_first_two_of_three
    (a r s t : ℕ)
    (rs : List ℕ)
    (h : carryConditionFrom a (r :: s :: t :: rs)) :
    carryConditionFrom a (s :: r :: t :: rs) := by
  change
    criticalCarry a r = 1 ∧
      criticalCarry (a + r) s = 1 ∧
        carryConditionFrom ((a + r) + s) (t :: rs) at h
  have hSwap : InteriorPairCarry a s r :=
    interiorPairCarry_swap a r s ⟨h.1, h.2.1⟩
  change
    criticalCarry a s = 1 ∧
      criticalCarry (a + s) r = 1 ∧
        carryConditionFrom ((a + s) + r) (t :: rs)
  refine ⟨hSwap.1, hSwap.2, ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2.2

/-- interior-only carry condition でも同じ adjacent swap law が成り立つ。 -/
theorem interiorCarry_swap_first_two_of_three
    (a r s t : ℕ)
    (rs : List ℕ)
    (h : interiorCarryConditionFrom a (r :: s :: t :: rs)) :
    interiorCarryConditionFrom a (s :: r :: t :: rs) := by
  change
    criticalCarry a r = 1 ∧
      criticalCarry (a + r) s = 1 ∧
        interiorCarryConditionFrom ((a + r) + s) (t :: rs) at h
  have hSwap : InteriorPairCarry a s r :=
    interiorPairCarry_swap a r s ⟨h.1, h.2.1⟩
  change
    criticalCarry a s = 1 ∧
      criticalCarry (a + s) r = 1 ∧
        interiorCarryConditionFrom ((a + s) + r) (t :: rs)
  refine ⟨hSwap.1, hSwap.2, ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2.2

end Skeleton

/--
二 block の affine translation の交換差。
`gap(r,H)=2^H-3^r` を使うと cross term だけに因数分解できる。
-/
def coefficientGap (r H : ℕ) : ℤ :=
  (2 ^ H : ℤ) - (3 ^ r : ℤ)

/-- adjacent block swap の exact affine difference。 -/
theorem affineConst_swap_two
    (u v : Word) :
    (affineConst (v ++ u) : ℤ) - (affineConst (u ++ v) : ℤ) =
      (affineConst u : ℤ) * coefficientGap (oddSteps v) (twoSteps v) -
        (affineConst v : ℤ) * coefficientGap (oddSteps u) (twoSteps u) := by
  have huvZ :
      (affineConst (u ++ v) : ℤ) =
        ((3 : ℤ) ^ oddSteps v) * (affineConst u : ℤ) +
          ((2 : ℤ) ^ twoSteps u) * (affineConst v : ℤ) := by
    exact_mod_cast affineConst_append u v
  have hvuZ :
      (affineConst (v ++ u) : ℤ) =
        ((3 : ℤ) ^ oddSteps u) * (affineConst v : ℤ) +
          ((2 : ℤ) ^ twoSteps v) * (affineConst u : ℤ) := by
    exact_mod_cast affineConst_append v u
  rw [huvZ, hvuZ]
  unfold coefficientGap
  ring

end RecordFerrers
end Collatz2
