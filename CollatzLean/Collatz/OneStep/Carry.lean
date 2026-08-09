import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# 一段first-carry

二つの奇数値の差深さとlower側のactual指数だけから、
synchronized / captured / deferredを分類する。

有限入力から得られる分類値はcomputableに構成する。
Prop上の奇偶証明からType値を選択せず、captured odd partとdeferred quotientを
入力値の明示式として定義する。
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

/-- captured枝でupper側に残る明示odd part。 -/
def capturedOddPart (d e a u : ℕ) : ℕ :=
  2 ^ (e - d) * a + 3 * u

/-- `d < e`なら明示odd partでupper側はdepth `d`にexactに止まる。 -/
theorem capturedExactFactor
    {x y d e a u : ℕ}
    (hde : d < e)
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a) :
    ExactFactor (3 * y + 1) d (capturedOddPart d e a u) := by
  have hgap : 0 < e - d :=
    Nat.sub_pos_of_lt hde
  have he : e = d + (e - d) := by
    omega
  have hpow :
      2 ^ e = 2 ^ d * 2 ^ (e - d) := by
    calc
      2 ^ e = 2 ^ (d + (e - d)) := by
        rw [← he]
      _ = 2 ^ d * 2 ^ (e - d) := by
        rw [pow_add]
  constructor
  · unfold capturedOddPart
    calc
      3 * y + 1 =
          (3 * x + 1) + 3 * 2 ^ d * u := by
        rw [hxy]
        ring
      _ = 2 ^ e * a + 3 * 2 ^ d * u := by
        rw [hx]
      _ = 2 ^ d * (2 ^ (e - d) * a + 3 * u) := by
        rw [hpow]
        ring
  · obtain ⟨s, hs⟩ : ∃ s : ℕ, e - d = s + 1 :=
      ⟨e - d - 1, by omega⟩
    have hEven : Even (2 ^ (e - d) * a) := by
      rw [hs]
      exact even_two_pow_succ_mul s a
    have hOdd : Odd (3 * u) :=
      (show Odd (3 : ℕ) by decide).mul hu
    rcases hEven with ⟨ke, hke⟩
    rcases hOdd with ⟨ko, hko⟩
    refine ⟨ke + ko, ?_⟩
    unfold capturedOddPart
    rw [hke, hko]
    ring

/-- deferred枝で追加carry後に残る明示quotient。 -/
def deferredQuotient (a u : ℕ) : ℕ :=
  (a + 3 * u) / 2

/-- `d=e`なら明示quotientで少なくとも1bit追加carryする。 -/
theorem deferredExtraFactor
    {x y d a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ d * a)
    (ha : Odd a) :
    3 * y + 1 = 2 ^ (d + 1) * deferredQuotient a u := by
  rcases ha with ⟨ka, hka⟩
  rcases hu with ⟨ku, hku⟩
  let q := ka + 3 * ku + 2
  have hsum : a + 3 * u = 2 * q := by
    dsimp [q]
    rw [hka, hku]
    ring
  have hquot : deferredQuotient a u = q := by
    unfold deferredQuotient
    rw [hsum]
    simp
  calc
    3 * y + 1 = (3 * x + 1) + 3 * 2 ^ d * u := by
      rw [hxy]
      ring
    _ = 2 ^ d * a + 3 * 2 ^ d * u := by rw [hx]
    _ = 2 ^ d * (a + 3 * u) := by ring
    _ = 2 ^ d * (2 * q) := by rw [hsum]
    _ = 2 ^ (d + 1) * deferredQuotient a u := by
      rw [pow_succ, hquot]
      ring

/-- lower指数が差深さより大きい場合、upper側は差深さでexactに止まる。 -/
theorem captured_of_depth_lt
    {x y d r a u : ℕ}
    (hr : 0 < r)
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ (d + r) * a) :
    ∃ b : ℕ, ExactFactor (3 * y + 1) d b := by
  refine ⟨capturedOddPart d (d + r) a u, ?_⟩
  apply capturedExactFactor (by omega) hxy hu hx

/-- lower指数と差深さが一致するとupper側に追加carryが起こる。 -/
theorem deferred_of_depth_eq
    {x y d a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ d * a)
    (ha : Odd a) :
    ∃ c : ℕ, 3 * y + 1 = 2 ^ (d + 1) * c := by
  exact ⟨deferredQuotient a u, deferredExtraFactor hxy hu hx ha⟩

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

/-- first-carryをcomputableな明示Type値として三枝へ分類する。 -/
def classify
    {x y d e a u : ℕ}
    (hxy : y = x + 2 ^ d * u)
    (hu : Odd u)
    (hx : 3 * x + 1 = 2 ^ e * a)
    (ha : Odd a) :
    CarryOutcome x y d e a u := by
  by_cases hed : e < d
  · exact CarryOutcome.synchronized
      (synchronized_of_depth_lt hed hxy hu hx ha)
  · by_cases hde : d < e
    · exact CarryOutcome.captured
        hde
        (capturedOddPart d e a u)
        (capturedExactFactor hde hxy hu hx)
    · have hEq : d = e := by omega
      subst e
      exact CarryOutcome.deferred
        rfl
        (deferredQuotient a u)
        (deferredExtraFactor hxy hu hx ha)

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
