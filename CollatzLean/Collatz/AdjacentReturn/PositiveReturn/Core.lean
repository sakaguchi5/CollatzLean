import CollatzLean.Collatz.AdjacentReturn.CanonicalContractingChain
import CollatzLean.Collatz.AdjacentReturn.FirstCrossingArithmetic

/-!
# positive canonical return chain の核

contracting 側では canonical shift 後の first crossing 自体が正の canonical return になる。
この層を Exact/Late や prepend-one quotient より上に置き、以後の refinement の共通入口とする。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn

/--
canonical contracting chain に first crossing の選択と Baker 型 gap 入力を保持した正本。

`positive return` は追加仮定ではなく、future-minimum 性と canonicality から導く。
-/
structure CanonicalChain (O : OddOrbit) where
  core : CanonicalContractingChain O
  gapBound : External.TwoThreeGapPolynomialBound
  crossing : ∀ n : ℕ, FirstCrossingData (core.state n)

namespace CanonicalChain

/-- 第 `n` block の state。 -/
def state {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) : State O :=
  C.core.state n

/-- 第 `n` block の first crossing。 -/
def firstCrossing {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    FirstCrossingData (C.state n) := by
  simpa [state] using C.crossing n

/-- 第 `n` first crossing の有限語。 -/
def word {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) : Collatz.Word :=
  (C.state n).word.take (C.firstCrossing n).length

@[simp] theorem word_length
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    (C.word n).length = (C.firstCrossing n).length := by
  unfold word
  exact (C.firstCrossing n).word_length

/-- first-crossing word は valid。 -/
theorem word_valid
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    Word.Valid (C.word n) := by
  let F := C.firstCrossing n
  have hfull :
      Word.Valid
        (((C.state n).word.take F.length) ++
          ((C.state n).word.drop F.length)) := by
    rw [List.take_append_drop]
    exact (C.state n).word_valid
  simpa [word, F] using hfull.prefix

/-- first-crossing start は canonical start そのもの。 -/
theorem start_eq_canonicalStart
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    (C.state n).startValue = Word.canonicalStart (C.word n) := by
  let F := C.firstCrossing n
  have h := C.core.firstCrossing_positive_canonical n F
  simpa [word, F, state] using h.1

/-- first-crossing endpoint は canonical end そのもの。 -/
theorem endpoint_eq_canonicalEnd
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    (C.firstCrossing n).endpointValue = Word.canonicalEnd (C.word n) := by
  let F := C.firstCrossing n
  have h := C.core.firstCrossing_positive_canonical n F
  simpa [word, F, state] using h.2.1

/-- 正の canonical return。 -/
theorem positive
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    Word.canonicalStart (C.word n) < Word.canonicalEnd (C.word n) := by
  rw [← C.start_eq_canonicalStart n, ← C.endpoint_eq_canonicalEnd n]
  exact (C.firstCrossing n).start_lt_endpoint

/-- actual return gap は canonical start/end 差そのもの。 -/
theorem canonicalEnd_eq_start_add_returnGap
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    Word.canonicalEnd (C.word n) =
      Word.canonicalStart (C.word n) + (C.firstCrossing n).returnGap := by
  rw [← C.endpoint_eq_canonicalEnd n, ← C.start_eq_canonicalStart n]
  exact (C.firstCrossing n).endpointValue_eq_startValue_add_returnGap

/-- positive return の sharp gap bound。 -/
theorem three_mul_returnGap_lt_length
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    3 * (C.firstCrossing n).returnGap < (C.firstCrossing n).length :=
  (C.firstCrossing n).three_mul_returnGap_lt_length

/-- positive return first crossing は長さ13以上。 -/
theorem thirteen_le_length
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    13 ≤ (C.firstCrossing n).length :=
  (C.firstCrossing n).thirteen_le_length

/-- chain 上の first-crossing 長は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {O : OddOrbit} (C : CanonicalChain O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      M < (C.firstCrossing n).length := by
  intro M
  obtain ⟨J, hJ⟩ := C.core.firstCrossing_lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro n hn
  exact hJ n hn (C.firstCrossing n)

/-- Baker 型入力から endpoint の uniform polynomial bound を得る。 -/
theorem endpoint_polynomial_bound
    {O : OddOrbit} (C : CanonicalChain O) :
    ∃ K A : ℕ,
      ∀ n : ℕ,
        3 * (C.firstCrossing n).endpointValue ≤
          (C.firstCrossing n).returnSlack *
            (K * ((C.firstCrossing n).length + 1) ^ A) := by
  obtain ⟨K, A, h⟩ :=
    FirstCrossingData.endpoint_le_returnSlack_polynomial C.gapBound
  exact ⟨K, A, fun n => h O (C.state n) (C.firstCrossing n)⟩

/-- start も同じ polynomial budget 以下。 -/
theorem start_polynomial_bound
    {O : OddOrbit} (C : CanonicalChain O) :
    ∃ K A : ℕ,
      ∀ n : ℕ,
        3 * (C.state n).startValue ≤
          (C.firstCrossing n).returnSlack *
            (K * ((C.firstCrossing n).length + 1) ^ A) := by
  obtain ⟨K, A, h⟩ := C.endpoint_polynomial_bound
  refine ⟨K, A, ?_⟩
  intro n
  have hstart :
      3 * (C.state n).startValue ≤
        3 * (C.firstCrossing n).endpointValue :=
    Nat.mul_le_mul_left 3 (C.firstCrossing n).start_le_endpoint
  exact le_trans hstart (h n)

/-- 既存 canonical contracting chain を positive-return 正本へ持ち上げる。 -/
noncomputable def ofCanonicalContractingChain
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (hGap : External.TwoThreeGapPolynomialBound) :
    CanonicalChain O := by
  classical
  refine {
    core := C
    gapBound := hGap
    crossing := ?_
  }
  intro n
  exact Classical.choice
    ((C.state n).existsFirstCrossingData
    (C.blockData n).contracting)

end CanonicalChain

/-- positive canonical return chain が存在する。 -/
def HasCanonicalChain : Prop :=
  ∃ O : OddOrbit, Nonempty (CanonicalChain O)

end PositiveReturn
end AdjacentReturn
end Collatz
