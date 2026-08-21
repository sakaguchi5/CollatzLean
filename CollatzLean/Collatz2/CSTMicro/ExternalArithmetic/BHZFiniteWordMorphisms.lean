import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalPhaseCoordinates

/-!
# BHZ finite-word morphisms

BHZ Proposition 3.3 で使う binary morphisms

  τ₀(0)=0,   τ₀(1)=01,
  τ₁(0)=10,  τ₁(1)=1

を有限 `List Bool` 上に実装する。

`false = 0`, `true = 1` と読む。

このファイルではさらに

* word power,
* τ_i の反復,
* cyclic permutation,
* cyclic root の infinite periodic reading,

を定義する。

後段では「actual shifted BHZ word の prefix が cyclic root の periodic reading と
一致する」という source-shaped statement を、既存
`CriticalShiftInitialPeriod` へ落とす。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- finite word `w^n`。 -/
def bhzWordPow
    (w : List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => bhzWordPow w n ++ w

@[simp] theorem bhzWordPow_zero
    (w : List Bool) :
    bhzWordPow w 0 = [] := rfl

@[simp] theorem bhzWordPow_succ
    (w : List Bool)
    (n : ℕ) :
    bhzWordPow w (n + 1) =
      bhzWordPow w n ++ w := rfl

@[simp] theorem bhzWordPow_length
    (w : List Bool)
    (n : ℕ) :
    (bhzWordPow w n).length = n * w.length := by
  induction n with
  | zero => simp [bhzWordPow]
  | succ n ih =>
      simp [bhzWordPow, ih, Nat.succ_mul]

/-- parity letter: even index = `0`, odd index = `1`。 -/
def bhzParityLetter : ℕ → Bool
  | 0 => false
  | n + 1 => !(bhzParityLetter n)

@[simp] theorem bhzParityLetter_zero :
    bhzParityLetter 0 = false := rfl

@[simp] theorem bhzParityLetter_succ
    (n : ℕ) :
    bhzParityLetter (n + 1) =
      !(bhzParityLetter n) := rfl

@[simp] theorem bhzParityLetter_add_two
    (n : ℕ) :
    bhzParityLetter (n + 2) =
      bhzParityLetter n := by
  simp [bhzParityLetter]

/-- BHZ letter morphism `τ_i`。 -/
def bhzTauLetter
    (i b : Bool) : List Bool :=
  match i, b with
  | false, false => [false]
  | false, true  => [false, true]
  | true,  false => [true, false]
  | true,  true  => [true]

/-- BHZ morphism `τ_i` を finite word に letterwise に適用する。 -/
def bhzTauWord
    (i : Bool)
    (w : List Bool) : List Bool :=
  w.flatMap (bhzTauLetter i)

@[simp] theorem bhzTauWord_nil
    (i : Bool) :
    bhzTauWord i [] = [] := by
  rfl

@[simp] theorem bhzTauWord_append
    (i : Bool)
    (u v : List Bool) :
    bhzTauWord i (u ++ v) =
      bhzTauWord i u ++ bhzTauWord i v := by
  simp [bhzTauWord]

@[simp] theorem bhzTauWord_single_self
    (i : Bool) :
    bhzTauWord i [i] = [i] := by
  cases i <;> rfl

@[simp] theorem bhzTauWord_single_not
    (i : Bool) :
    bhzTauWord i [!i] = [i, !i] := by
  cases i <;> rfl

/-- `τ_i^n`。 -/
def bhzTauIter
    (i : Bool) : ℕ → List Bool → List Bool
  | 0, w => w
  | n + 1, w =>
      bhzTauWord i (bhzTauIter i n w)

@[simp] theorem bhzTauIter_zero
    (i : Bool)
    (w : List Bool) :
    bhzTauIter i 0 w = w := rfl

@[simp] theorem bhzTauIter_succ
    (i : Bool)
    (n : ℕ)
    (w : List Bool) :
    bhzTauIter i (n + 1) w =
      bhzTauWord i (bhzTauIter i n w) := rfl

/-- `τ_i^n` は空語を空語に保つ。 -/
@[simp] theorem bhzTauIter_nil
    (i : Bool)
    (n : ℕ) :
    bhzTauIter i n [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [bhzTauIter, ih]

@[simp] theorem bhzTauIter_append
    (i : Bool)
    (n : ℕ)
    (u v : List Bool) :
    bhzTauIter i n (u ++ v) =
      bhzTauIter i n u ++ bhzTauIter i n v := by
  induction n with
  | zero => simp [bhzTauIter]
  | succ n ih =>
      simp [bhzTauIter, ih]

@[simp] theorem bhzTauIter_single_self
    (i : Bool)
    (n : ℕ) :
    bhzTauIter i n [i] = [i] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [bhzTauIter, ih]

/-- `τ_i` は self-letter の有限冪 `[i]^n` を固定する。 -/
@[simp] theorem bhzTauWord_wordPow_single_self
    (i : Bool)
    (n : ℕ) :
    bhzTauWord i (bhzWordPow [i] n) =
      bhzWordPow [i] n := by
  induction n with
  | zero => simp [bhzWordPow]
  | succ n ih =>
      simp [bhzWordPow, ih]

/-- `τ_i^n(!i) = i^n !i`。 -/
theorem bhzTauIter_single_not
    (i : Bool)
    (n : ℕ) :
    bhzTauIter i n [!i] =
      bhzWordPow [i] n ++ [!i] := by
  induction n with
  | zero => simp [bhzTauIter, bhzWordPow]
  | succ n ih =>
      rw [bhzTauIter_succ, ih, bhzTauWord_append]
      rw [bhzTauWord_wordPow_single_self, bhzTauWord_single_not]
      simp [bhzWordPow, List.append_assoc]

/-- finite words の cyclic permutation relation。 -/
def BHZIsCyclicPermutation
    (u v : List Bool) : Prop :=
  ∃ x y : List Bool,
    u = x ++ y ∧
    v = y ++ x

namespace BHZIsCyclicPermutation

/-- cyclic permutation は length を保存する。 -/
theorem length_eq
    {u v : List Bool}
    (H : BHZIsCyclicPermutation u v) :
    v.length = u.length := by
  rcases H with ⟨x, y, hu, hv⟩
  rw [hu, hv]
  simp [Nat.add_comm]

/-- reflexive。 -/
theorem refl
    (u : List Bool) :
    BHZIsCyclicPermutation u u := by
  refine ⟨[], u, ?_, ?_⟩ <;> simp

end BHZIsCyclicPermutation

/--
finite root `w` を無限 periodic word として読む。
empty root は便宜上 `false` を返す。
-/
def bhzPeriodicBit
    (w : List Bool)
    (n : ℕ) : Bool :=
  if h : 0 < w.length then
    w.get ⟨n % w.length, Nat.mod_lt n h⟩
  else
    false

/-- root length だけ進めても periodic reading は不変。 -/
theorem bhzPeriodicBit_add_length
    (w : List Bool)
    (n : ℕ) :
    bhzPeriodicBit w (n + w.length) =
      bhzPeriodicBit w n := by
  by_cases h : 0 < w.length
  · simp [bhzPeriodicBit, h]
  · have hz : w.length = 0 := Nat.eq_zero_of_not_pos h
    simp [bhzPeriodicBit, hz]

/--
BHZ source theorem が与える「cyclic standard/semistandard word の initial power」を
finite-word のまま表す。

`canonical` は morphism から作った canonical root、`root` は実際に prefix の先頭に
現れる cyclic permutation。
-/
structure BHZCriticalCyclicPrefixPower
    (s : ℕ)
    (canonical : List Bool)
    (length : ℕ) : Type where
  root : List Bool
  cyclic : BHZIsCyclicPermutation canonical root
  initialAgreement :
    ∀ i : ℕ,
      i < length →
        criticalShiftBit s i =
          bhzPeriodicBit root i

namespace BHZCriticalCyclicPrefixPower

/-- source cyclic power が使う actual root と canonical root は同じ length。 -/
theorem root_length_eq
    {s length : ℕ}
    {canonical : List Bool}
    (H : BHZCriticalCyclicPrefixPower s canonical length) :
    H.root.length = canonical.length :=
  H.cyclic.length_eq

end BHZCriticalCyclicPrefixPower

end ExternalArithmetic
end CSTMicro
end Collatz2
