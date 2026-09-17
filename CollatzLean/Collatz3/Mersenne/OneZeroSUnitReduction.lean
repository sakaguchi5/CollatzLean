import CollatzLean.Collatz3.Mersenne.OneZeroSparseComplement
import CollatzLean.Collatz3.Arithmetic.TwoThreeUnit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Collatz3 Mersenne: sparse-complement equation の `{2,3}`-S-unit reduction

exact equation

`3^k(2^n-1) + 2^r*missing + 2^r = 2^(L+r) + 1`

を、項数が target zero defect で抑えられた符号付き `{2,3}`-unit 和へ変換する。

このファイルで無条件に行うことは次の四点。

1. `missingBits` を有限個の 2 冪項へ展開する。
2. sparse equation を有限 `{2,3}`-unit zero-sum にする。
3. `-3^k` を含む極小消滅部分和を取る。
4. parity により、その極小部分和が必ず `-1` も含むことを示す。

深い ESS / Subspace theorem はここへ入れない。
-/

namespace Collatz3
namespace Mersenne
namespace SparseSUnit

open Arithmetic
open Arithmetic.SignedTwoThreeUnit

/--
`missingBits` の `1` を、絶対 exponent `r+i` の正の 2 冪 unit に展開する。
-/
def missingTerms (r : ℕ) : List Bool → List SignedTwoThreeUnit
  | [] => []
  | b :: bs =>
      (if b then [pos r 0] else []) ++
        missingTerms (r + 1) bs

/-- missing term の個数は missing word の one-count そのもの。 -/
theorem missingTerms_length
    (r : ℕ)
    (bits : List Bool) :
    (missingTerms r bits).length = Binary.oneCount bits := by
  induction bits generalizing r with
  | nil =>
      simp [missingTerms, Binary.oneCount]
  | cons b bs ih =>
      cases b <;>
        simp [missingTerms, Binary.oneCount, ih, Nat.add_comm]

/-- missing term の整数和は `2^r * value(missingBits)` に exact に一致する。 -/
theorem missingTerms_value_sum
    (r : ℕ)
    (bits : List Bool) :
    ((missingTerms r bits).map SignedTwoThreeUnit.value).sum =
      (2 : ℤ) ^ r * (Binary.valueLSB bits : ℤ) := by
  induction bits generalizing r with
  | nil =>
      simp [missingTerms, Binary.valueLSB]
  | cons b bs ih =>
      cases b <;>
        simp [missingTerms, Binary.valueLSB, ih, pow_succ] <;>
        ring

/-- `r>0` なら missing 由来の全 unit は 2-adic exponent が正。 -/
theorem missingTerms_twoExp_pos
    {r : ℕ} {bits : List Bool} {t : SignedTwoThreeUnit}
    (hr : 0 < r)
    (ht : t ∈ missingTerms r bits) :
    0 < t.twoExp := by
  induction bits generalizing r with
  | nil =>
      simp [missingTerms] at ht
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [missingTerms, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ht
          exact ih (by omega) ht
      | true =>
          simp only [missingTerms, ↓reduceIte, List.cons_append,
                      List.nil_append, List.mem_cons] at ht
          rcases ht with hHead | hTail
          · subst t
            simpa [pos] using hr
          · exact ih (by omega) hTail

/--
二つの odd anchor `-1`, `-3^k` を除いた even-side の unit 列。
-/
def evenTerms
    (k n r length : ℕ)
    (bits : List Bool) :
    List SignedTwoThreeUnit :=
  pos n k ::
    (missingTerms r bits ++
      [pos r 0, neg (length + r) 0])

/-- even-side の項数は `oneCount + 3`。 -/
theorem evenTerms_length
    (k n r length : ℕ)
    (bits : List Bool) :
    (evenTerms k n r length bits).length =
      Binary.oneCount bits + 3 := by
  simp [evenTerms, missingTerms_length]

/-- even-side の整数和。 -/
theorem evenTerms_value_sum
    (k n r length : ℕ)
    (bits : List Bool) :
    ((evenTerms k n r length bits).map SignedTwoThreeUnit.value).sum =
      (2 : ℤ) ^ n * (3 : ℤ) ^ k +
        (2 : ℤ) ^ r * (Binary.valueLSB bits : ℤ) +
          (2 : ℤ) ^ r -
            (2 : ℤ) ^ (length + r) := by
  simp [evenTerms, missingTerms_value_sum]
  ring

/-- `n>0, r>0` なら even-side の全項は実際に偶数。 -/
theorem evenTerms_twoExp_pos
    {k n r length : ℕ} {bits : List Bool}
    {t : SignedTwoThreeUnit}
    (hn : 0 < n)
    (hr : 0 < r)
    (ht : t ∈ evenTerms k n r length bits) :
    0 < t.twoExp := by
  simp only [evenTerms, List.mem_cons, List.mem_append] at ht
  rcases ht with hLead | hMissing | hShift | hTop
  · subst t
    simpa [pos] using hn
  · exact missingTerms_twoExp_pos hr hMissing
  · subst t
    simpa [pos] using hr
  · rcases hTop with hTop | hNil
    · subst t
      have hTopPos : 0 < length + r := by
        omega
      simpa [neg] using hTopPos
    · simp at hNil

/--
二つの odd anchor と even-side を型レベルで分離した有限 index。

`Sum (Fin 2) ...` にしておくことで parity anchor の識別を単純に保つ。
-/
abbrev SparseIndex
    (k n r length : ℕ)
    (bits : List Bool) :=
  Sum (Fin 2) (Fin (evenTerms k n r length bits).length)

/-- index が指す符号付き `{2,3}`-unit。 -/
def indexedTerm
    (k n r length : ℕ)
    (bits : List Bool) :
    SparseIndex k n r length bits → SignedTwoThreeUnit
  | Sum.inl i =>
      if i.1 = 0 then negOne else negThree k
  | Sum.inr i =>
      (evenTerms k n r length bits).get i

/-- constant `-1` の index。 -/
def oneIndex
    (k n r length : ℕ)
    (bits : List Bool) :
    SparseIndex k n r length bits :=
  Sum.inl ⟨0, by decide⟩

/-- `-3^k` の index。 -/
def threeIndex
    (k n r length : ℕ)
    (bits : List Bool) :
    SparseIndex k n r length bits :=
  Sum.inl ⟨1, by decide⟩

@[simp] theorem indexedTerm_oneIndex
    (k n r length : ℕ)
    (bits : List Bool) :
    indexedTerm k n r length bits
      (oneIndex k n r length bits) = negOne := by
  simp [indexedTerm, oneIndex]

@[simp] theorem indexedTerm_threeIndex
    (k n r length : ℕ)
    (bits : List Bool) :
    indexedTerm k n r length bits
      (threeIndex k n r length bits) = negThree k := by
  simp [indexedTerm, threeIndex]

@[simp] theorem oneIndex_ne_threeIndex
    (k n r length : ℕ)
    (bits : List Bool) :
    oneIndex k n r length bits ≠
      threeIndex k n r length bits := by
  simp [oneIndex, threeIndex]

/-- `Finset.univ` で list 全体を走査した和は通常の `List.sum`。 -/
private theorem finset_univ_sum_get_map_eq_sum
    {α : Type*}
    (f : α → ℤ)
    (xs : List α) :
    Finset.sum
        (Finset.univ : Finset (Fin xs.length))
        (fun i => f (xs.get i)) =
      (xs.map f).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      change
        Finset.sum
            (Finset.univ : Finset (Fin (xs.length + 1)))
            (fun i => f ((x :: xs).get i)) =
          f x + (xs.map f).sum
      calc
        Finset.sum
            (Finset.univ : Finset (Fin (xs.length + 1)))
            (fun i => f ((x :: xs).get i))
            =
          f x +
            Finset.sum
              (Finset.univ : Finset (Fin xs.length))
              (fun i => f (xs.get i)) := by
          simpa using
            (Fin.sum_univ_succ
              (fun i : Fin (xs.length + 1) =>
                f ((x :: xs).get i)))
        _ = f x + (xs.map f).sum := by
          rw [ih]

/-- sparse equation を整数環上で減算を展開した形。 -/
theorem sparseEquation_int
    {k n r length : ℕ}
    {bits : List Bool}
    (hEq :
      3 ^ k * (2 ^ n - 1) +
          2 ^ r * Binary.valueLSB bits + 2 ^ r =
        2 ^ (length + r) + 1) :
    (-1 : ℤ) - (3 : ℤ) ^ k +
          (2 : ℤ) ^ n * (3 : ℤ) ^ k +
          (2 : ℤ) ^ r * (Binary.valueLSB bits : ℤ) +
          (2 : ℤ) ^ r -
          (2 : ℤ) ^ (length + r) = 0 := by
  have hPowPos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hPow : 1 ≤ 2 ^ n := by
    omega
  have hCast := congrArg (fun z : ℕ => (z : ℤ)) hEq
  push_cast [Nat.cast_sub hPow] at hCast
  calc
    (-1 : ℤ) - (3 : ℤ) ^ k +
          (2 : ℤ) ^ n * (3 : ℤ) ^ k +
          (2 : ℤ) ^ r * (Binary.valueLSB bits : ℤ) +
          (2 : ℤ) ^ r -
          (2 : ℤ) ^ (length + r)
        =
        ((3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1) +
          (2 : ℤ) ^ r * (Binary.valueLSB bits : ℤ) +
          (2 : ℤ) ^ r) -
          ((2 : ℤ) ^ (length + r) + 1) := by ring
    _ = 0 := by rw [hCast]; ring

/--
`sparseEquation` と `r>0` だけから `n>0` が従う。
`n=0` なら左辺は偶数、右辺は奇数になる。
-/
theorem sparseEquation_n_pos
    {k n r length : ℕ}
    {bits : List Bool}
    (hr : 0 < r)
    (hEq :
      3 ^ k * (2 ^ n - 1) +
          2 ^ r * Binary.valueLSB bits + 2 ^ r =
        2 ^ (length + r) + 1) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  have hEq' :
      2 ^ r * Binary.valueLSB bits + 2 ^ r =
        2 ^ (length + r) + 1 := by
    simpa using hEq
  obtain ⟨q, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hLeft :
      2 ^ (q + 1) * Binary.valueLSB bits + 2 ^ (q + 1) =
        2 * (2 ^ q * Binary.valueLSB bits + 2 ^ q) := by
    rw [pow_succ]
    ring
  have hRight :
      2 ^ (length + (q + 1)) + 1 =
        2 * 2 ^ (length + q) + 1 := by
    rw [show length + (q + 1) = (length + q) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hLeft, hRight] at hEq'
  omega

/-- 全 sparse index の個数は `oneCount + 5`。 -/
theorem sparseIndex_card
    (k n r length : ℕ)
    (bits : List Bool) :
    Fintype.card (SparseIndex k n r length bits) =
      Binary.oneCount bits + 5 := by
  simp [SparseIndex, evenTerms_length]
  omega

/-- sparse equation は全 index 上の exact zero-sum を与える。 -/
theorem indexedTerm_univ_sum_zero
    {k n r length : ℕ}
    {bits : List Bool}
    (hEq :
      3 ^ k * (2 ^ n - 1) +
          2 ^ r * Binary.valueLSB bits + 2 ^ r =
        2 ^ (length + r) + 1) :
    Finset.sum
        (Finset.univ : Finset (SparseIndex k n r length bits))
        (fun i => (indexedTerm k n r length bits i).value) = 0 := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp [indexedTerm, evenTerms_value_sum]
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    (sparseEquation_int hEq)

/--
parity anchor。

`n>0, r>0` の sparse zero-sum で `-3^k` を含む部分和は、
同じ部分和の中に必ず constant `-1` も含む。
-/
theorem vanishing_contains_one
    {k n r length : ℕ}
    {bits : List Bool}
    (hn : 0 < n)
    (hr : 0 < r)
    {s : Finset (SparseIndex k n r length bits)}
    (hThree : threeIndex k n r length bits ∈ s)
    (hZero :
      Finset.sum s
        (fun i => (indexedTerm k n r length bits i).value) = 0) :
    oneIndex k n r length bits ∈ s := by
  classical
  by_contra hOne
  let three := threeIndex k n r length bits
  let one := oneIndex k n r length bits
  let term := indexedTerm k n r length bits
  have hEvenEach :
      ∀ i ∈ s.erase three,
        IntEven ((term i).value) := by
    intro i hi
    have hiData := Finset.mem_erase.mp hi
    have hiNeThree : i ≠ three := hiData.1
    have hiS : i ∈ s := hiData.2
    rcases i with i | i
    · have hCases : i.1 = 0 ∨ i.1 = 1 := by
        omega
      rcases hCases with hZeroIdx | hOneIdx
      · have hiFin :
            i = (⟨0, by decide⟩ : Fin 2) := by
          apply Fin.ext
          exact hZeroIdx
        have hiEq :
            (Sum.inl i :
              SparseIndex k n r length bits) = one := by
          simpa [one, oneIndex] using
            congrArg
              (fun j : Fin 2 =>
                (Sum.inl j :
                  SparseIndex k n r length bits))
              hiFin
        rw [hiEq] at hiS
        exact False.elim (hOne hiS)
      · have hiFin :
            i = (⟨1, by decide⟩ : Fin 2) := by
          apply Fin.ext
          exact hOneIdx
        have hiEq :
            (Sum.inl i :
              SparseIndex k n r length bits) = three := by
          simpa [three, threeIndex] using
            congrArg
              (fun j : Fin 2 =>
                (Sum.inl j :
                  SparseIndex k n r length bits))
              hiFin
        exact False.elim (hiNeThree hiEq)
    · apply SignedTwoThreeUnit.value_even_of_twoExp_pos
      apply evenTerms_twoExp_pos hn hr
      exact List.get_mem _ _
  have hEvenSum :
      IntEven
        (Finset.sum (s.erase three)
          (fun i => (term i).value)) :=
    IntEven.finset_sum _ _ hEvenEach
  rcases hEvenSum with ⟨q, hq⟩
  have hDecomp :
      Finset.sum (s.erase three)
          (fun i => (term i).value) +
        (term three).value = 0 := by
    rw [Finset.sum_erase_add
      s
      (fun i => (term i).value)
      hThree]
    exact hZero
  apply SignedTwoThreeUnit.negThree_not_even k
  refine ⟨-q, ?_⟩
  have hThreeValue :
      term three = negThree k := by
    simp [term, three]
  rw [hq, hThreeValue] at hDecomp
  omega

/--
任意の sparse-complement equation から nondegenerate `{2,3}`-unit certificate を得る。

返すものは Prop 内の existential に留め、外部数論層へ必要な三事実だけを渡す。
ここまで外部数論仮定は一切使わない。
-/
theorem exists_nondegenerateCertificate
    {k n r length : ℕ}
    {bits : List Bool}
    (hr : 0 < r)
    (hEq :
      3 ^ k * (2 ^ n - 1) +
          2 ^ r * Binary.valueLSB bits + 2 ^ r =
        2 ^ (length + r) + 1) :
    ∃ selected : Finset (SparseIndex k n r length bits),
      selected.card ≤ Binary.oneCount bits + 5 ∧
      NondegenerateSumOne
        (fun i => (indexedTerm k n r length bits i).value)
        selected ∧
      threeIndex k n r length bits ∈ selected := by
  classical
  let term := indexedTerm k n r length bits
  let three := threeIndex k n r length bits
  let one := oneIndex k n r length bits
  have hn : 0 < n := sparseEquation_n_pos hr hEq
  have hUnivZero :
      Vanishes
        (fun i => (term i).value)
        (Finset.univ : Finset (SparseIndex k n r length bits)) := by
    unfold Vanishes
    simpa [term] using indexedTerm_univ_sum_zero hEq
  rcases exists_anchorMinimalVanishing
      (v := fun i => (term i).value)
      three
      (s₀ := (Finset.univ : Finset (SparseIndex k n r length bits)))
      (by simp)
      hUnivZero with
    ⟨s, hsUniv, hMinimal⟩
  have hOne : one ∈ s := by
    apply vanishing_contains_one hn hr hMinimal.anchor_mem
    exact hMinimal.sum_eq_zero
  let selected := s.erase one
  have hNondegenerate :
      NondegenerateSumOne
        (fun i => (term i).value)
        selected := by
    apply hMinimal.erase_neg_one hOne
    simp [term, one]
  have hThreeSelected : three ∈ selected := by
    apply Finset.mem_erase.mpr
    constructor
    · simpa [one, three] using
        (oneIndex_ne_threeIndex k n r length bits).symm
    · exact hMinimal.anchor_mem
  refine ⟨selected, ?_, hNondegenerate, hThreeSelected⟩
  calc
    selected.card ≤
        (Finset.univ : Finset (SparseIndex k n r length bits)).card :=
      Finset.card_le_card (Finset.subset_univ selected)
    _ = Binary.oneCount bits + 5 := by
      simpa only [Finset.card_univ] using
        sparseIndex_card k n r length bits

end SparseSUnit
end Mersenne
end Collatz3
