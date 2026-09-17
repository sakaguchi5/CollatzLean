import CollatzLean.Collatz3.Arithmetic.AnchoredVanishing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Arithmetic: signed `{2,3}`-unit vocabulary

ESS / Subspace theorem へ渡すための最小語彙。

各項は

`± 2^a * 3^b`

だけを保持する。外部の深い数論定理そのものは導入せず、
Collatz 側が最終的に必要とする bounded-exponent corollary を `Prop` interface にする。
-/

namespace Collatz3
namespace Arithmetic

open scoped BigOperators

/-- 符号付き `{2,3}`-unit。 -/
structure SignedTwoThreeUnit where
  negative : Bool
  twoExp : ℕ
  threeExp : ℕ
  deriving DecidableEq, Repr

namespace SignedTwoThreeUnit

/-- 整数としての値。 -/
def value (t : SignedTwoThreeUnit) : ℤ :=
  (if t.negative then (-1 : ℤ) else 1) *
    (2 : ℤ) ^ t.twoExp *
      (3 : ℤ) ^ t.threeExp

/-- 正の `{2,3}`-unit。 -/
def pos (a b : ℕ) : SignedTwoThreeUnit :=
  ⟨false, a, b⟩

/-- 負の `{2,3}`-unit。 -/
def neg (a b : ℕ) : SignedTwoThreeUnit :=
  ⟨true, a, b⟩

/-- `-3^k` anchor。 -/
def negThree (k : ℕ) : SignedTwoThreeUnit :=
  neg 0 k

/-- 定数 `-1` anchor。 -/
def negOne : SignedTwoThreeUnit :=
  neg 0 0

@[simp] theorem value_pos (a b : ℕ) :
    value (pos a b) = (2 : ℤ) ^ a * (3 : ℤ) ^ b := by
  simp [value, pos]

@[simp] theorem value_neg (a b : ℕ) :
    value (neg a b) = -((2 : ℤ) ^ a * (3 : ℤ) ^ b) := by
  simp [value, neg]

@[simp] theorem value_negThree (k : ℕ) :
    value (negThree k) = -(3 : ℤ) ^ k := by
  simp [negThree]

@[simp] theorem value_negOne :
    value negOne = -1 := by
  simp [negOne]

end SignedTwoThreeUnit

/-- 整数が偶数であることを witness 付きで保持する。 -/
def IntEven (z : ℤ) : Prop :=
  ∃ q : ℤ, z = 2 * q

namespace IntEven

@[simp] theorem zero : IntEven 0 := by
  exact ⟨0, by norm_num⟩

/-- 偶数の有限和は偶数。 -/
theorem finset_sum
    {ι : Type*}
    (s : Finset ι)
    (f : ι → ℤ)
    (h : ∀ i ∈ s, IntEven (f i)) :
    IntEven (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact IntEven.zero
  | @insert a s ha ih =>
      rcases h a (by simp) with ⟨qa, hqa⟩
      have hTail : ∀ i ∈ s, IntEven (f i) := by
        intro i hi
        exact h i (by simp [hi])
      rcases ih hTail with ⟨qs, hqs⟩
      refine ⟨qa + qs, ?_⟩
      simp [Finset.sum_insert, ha, hqa, hqs]
      ring

end IntEven

namespace SignedTwoThreeUnit

/-- `twoExp > 0` の `{2,3}`-unit は符号によらず偶数。 -/
theorem value_even_of_twoExp_pos
    {t : SignedTwoThreeUnit}
    (h : 0 < t.twoExp) :
    IntEven (value t) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h) with
    ⟨a, ha⟩
  refine ⟨
    (if t.negative then (-1 : ℤ) else 1) *
      (2 : ℤ) ^ a *
        (3 : ℤ) ^ t.threeExp,
    ?_⟩
  unfold value
  rw [ha, pow_succ]
  ring

/-- `3^k` は常に奇数、を witness 付きで読む補題。 -/
theorem threePow_eq_two_mul_add_one (k : ℕ) :
    ∃ q : ℕ, 3 ^ k = 2 * q + 1 := by
  induction k with
  | zero =>
      exact ⟨0, by norm_num⟩
  | succ k ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨3 * q + 1, ?_⟩
      rw [pow_succ, hq]
      ring

/-- `-3^k` は偶数ではない。 -/
theorem negThree_not_even (k : ℕ) :
    ¬ IntEven (value (negThree k)) := by
  intro hEven
  rcases hEven with ⟨z, hz⟩
  rcases threePow_eq_two_mul_add_one k with ⟨q, hq⟩
  have hqInt :
      (3 : ℤ) ^ k = 2 * (q : ℤ) + 1 := by
    exact_mod_cast hq
  have hz' : -(3 : ℤ) ^ k = 2 * z := by
    simpa using hz
  omega

end SignedTwoThreeUnit

/--
ESS の nondegenerate S-unit finiteness から得られる、
この project が実際に必要とする bounded-exponent 版 interface。

固定項数 `N` に対し、nondegenerate な

`x₁ + ... + x_d = 1`,  `d ≤ N`

の中に `-3^k` が現れるなら `k` は一様有界、という主張。
この定義自体は axiom ではない。
-/
def NondegenerateTwoThreeUnitExponentBound : Prop :=
  ∀ N : ℕ,
    ∃ K : ℕ,
      ∀ {ι : Type} [DecidableEq ι],
        ∀ (term : ι → SignedTwoThreeUnit)
          (s : Finset ι)
          (k : ℕ),
          s.card ≤ N →
          NondegenerateSumOne
            (fun i => (term i).value) s →
          (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
          k < K

end Arithmetic
end Collatz3
