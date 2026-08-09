import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# 一段first-carry

二つの奇数値の差深さとlower側のactual指数だけから、
synchronized / captured / deferredを分類する。
-/

namespace Collatz
namespace OneStep

open TwoAdic

/-- `e < d`で上下が同じ指数`e`を使う同期carry。 -/
structure SynchronizedCarry
    (x y d e a u : ℕ) : Type where
  depth_lt : e < d
  upperNext : ℕ
  upperFactor : ExactFactor (3 * y + 1) e upperNext
  nextDifference : upperNext = a + 2 ^ (d - e) * (3 * u)
  nextDifferenceOdd : Odd (3 * u)

/-- first-carryの完全三分岐。 -/
inductive CarryOutcome
    (x y d e a u : ℕ) : Type
  | synchronized (data : SynchronizedCarry x y d e a u)
  | captured
      (depth_lt : d < e)
      (oddPart : ℕ)
      (exactFactor : ExactFactor (3 * y + 1) d oddPart)
  | deferred
      (depth_eq : d = e)
      (quotient : ℕ)
      (extraFactor : 3 * y + 1 = 2 ^ (d + 1) * quotient)

/-- lower指数が差深さより大きい場合、upper側は差深さでexactに止まる。 -/
theorem captured_of_depth_lt
    {x y d r a u : ℕ}
    (hr : 0 < r)
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ (d + r) * a)
    (ha : Odd a) :
    ∃ b : ℕ, ExactFactor (3 * y + 1) d b := by
  cases r with
  | zero => simp at hr
  | succ s =>
      rcases hu with ⟨ku, rfl⟩
      rcases ha with ⟨ka, rfl⟩
      let b := 2 ^ (s + 1) * (2 * ka + 1) + 3 * (2 * ku + 1)
      refine ⟨b, ?_, ?_⟩
      · unfold b
        calc
          3 * y + 1
              = (3 * x + 1) + 3 * 2 ^ d * (2 * ku + 1) := by rw [hxy]; ring
          _ = 2 ^ (d + (s + 1)) * (2 * ka + 1) +
                3 * 2 ^ d * (2 * ku + 1) := by rw [hx]
          _ = 2 ^ d *
                (2 ^ (s + 1) * (2 * ka + 1) + 3 * (2 * ku + 1)) := by
                  rw [pow_add]
                  ring
      · refine ⟨2 ^ s * (2 * ka + 1) + 3 * ku + 1, ?_⟩
        unfold b
        rw [pow_succ]
        ring

/-- lower指数と差深さが一致するとupper側に追加carryが起こる。 -/
theorem deferred_of_depth_eq
    {x y d a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ d * a)
    (ha : Odd a) :
    ∃ c : ℕ, 3 * y + 1 = 2 ^ (d + 1) * c := by
  rcases hu with ⟨ku, rfl⟩
  rcases ha with ⟨ka, rfl⟩
  refine ⟨ka + 3 * ku + 2, ?_⟩
  calc
    3 * y + 1
        = (3 * x + 1) + 3 * 2 ^ d * (2 * ku + 1) := by rw [hxy]; ring
    _ = 2 ^ d * (2 * ka + 1) + 3 * 2 ^ d * (2 * ku + 1) := by rw [hx]
    _ = 2 ^ (d + 1) * (ka + 3 * ku + 2) := by
      rw [pow_succ]
      ring

/-- `e < d`ならupper側も指数`e`でexactに止まる。 -/
def synchronized_of_depth_lt
    {x y d e a u : ℕ}
    (hed : e < d)
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a)
    (ha : Odd a) :
    SynchronizedCarry x y d e a u := by
  let r := d - e
  have hr : 0 < r := by dsimp [r]; omega
  have hd : d = e + r := by dsimp [r]; omega
  let b := a + 2 ^ r * (3 * u)
  have hodd3u : Odd (3 * u) := (show Odd (3 : ℕ) by decide).mul hu
  have heven : Even (2 ^ r * (3 * u)) := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, r = s + 1 := ⟨r - 1, by omega⟩
    rw [hs]
    exact even_two_pow_succ_mul s (3 * u)
  have hbOdd : Odd b := by
    rcases ha with ⟨ka, hka⟩
    rcases heven with ⟨ke, hke⟩
    refine ⟨ka + ke, ?_⟩
    unfold b
    rw [hka, hke]
    ring
  refine ⟨hed, b, ?_, rfl, hodd3u⟩
  refine ⟨?_, hbOdd⟩
  unfold b
  calc
    3 * y + 1 = (3 * x + 1) + 3 * 2 ^ d * u := by rw [hxy]; ring
    _ = 2 ^ e * a + 3 * 2 ^ d * u := by rw [hx]
    _ = 2 ^ e * (a + 2 ^ r * (3 * u)) := by
      rw [hd, pow_add]
      ring

/-- first-carryを三枝へ分類する。結果はProp上の存在ではなく明示的なType値。 -/
noncomputable def classify
    {x y d e a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a)
    (ha : Odd a) :
    CarryOutcome x y d e a u := by
  classical
  by_cases hed : e < d
  · exact CarryOutcome.synchronized
      (synchronized_of_depth_lt hed hxy hu hx ha)
  · by_cases hde : d < e
    · let r := e - d
      have hr : 0 < r := by
        dsimp [r]
        omega
      have he : e = d + r := by
        dsimp [r]
        omega
      have hex := captured_of_depth_lt
        (r := r) hr hxy hu (by simpa [he] using hx) ha
      let b := Classical.choose hex
      have hb := Classical.choose_spec hex
      exact CarryOutcome.captured hde b hb
    · have hEq : d = e := by
        omega
      subst e
      have hex := deferred_of_depth_eq hxy hu hx ha
      let c := Classical.choose hex
      have hc := Classical.choose_spec hex
      exact CarryOutcome.deferred rfl c hc



/-- 同じ開始値の一段完全分解は一意。 -/
theorem next_unique
    {x e₁ e₂ y₁ y₂ : ℕ}
    (h₁ : 2 ^ e₁ * y₁ = 3 * x + 1)
    (h₂ : 2 ^ e₂ * y₂ = 3 * x + 1)
    (hy₁ : Odd y₁) (hy₂ : Odd y₂) :
    e₁ = e₂ ∧ y₁ = y₂ := by
  exact TwoAdic.unique ⟨h₁.symm, hy₁⟩ ⟨h₂.symm, hy₂⟩

end OneStep
end Collatz
