import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZFiniteWordMorphisms
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalPrefixPowerCandidate

/-!
# BHZ critical standard / semistandard words

BHZ の directive morphism

  τ₀^a₁ ∘ τ₁^a₂ ∘ ... ∘ τ_(k-1)^a_k

を actual critical partial quotients `criticalBHZa` で構成する。

BHZ Lemma 3.4 / Proposition 3.3 で使う canonical roots は

standard:
  τ₀^a₁ ... τ_(k-1)^a_k (i),       i = k mod 2

semistandard:
  τ₀^a₁ ... τ_(k-2)^a_(k-1)
    τ_(k-1)^(a_k-c_k) (i).

このファイルでは source theorem の prefix claim はまだ仮定しない。
finite morphism algebraだけから root length を exact に証明する：

  |standard_k| = q_k,

  |semistandard_k|
    = q_k - c_k q_(k-1).

従って次段の `BHZCriticalProposition33WordFormula` は paper の cyclic-prefix claim
だけを担えばよく、root arithmetic は Lean 内で閉じる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- Every actual BHZ denominator is positive. -/
theorem criticalBHZq_pos
    (k : ℕ) :
    0 < criticalBHZq k := by
  unfold criticalBHZq
  exact criticalPowerP_pos (by omega)

namespace CriticalBHZPhasePacket

/-- packet coordinate also has the source convention `c₁=0`. -/
@[simp] theorem digit_one
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) :
    P.digit 1 = 0 := by
  unfold CriticalBHZPhasePacket.digit
  exact BHZCriticalPhaseExpansion.digit_one P.expansion

end CriticalBHZPhasePacket

/--
First `k` BHZ directive morphisms applied to a finite word.

`k=0` is identity; the `(k+1)`st stage first applies
`τ_(k mod 2)^a_(k+1)` and then the already-built outer directive.
-/
def bhzCriticalDirectiveImage :
    ℕ → List Bool → List Bool
  | 0, w => w
  | k + 1, w =>
      bhzCriticalDirectiveImage k
        (bhzTauIter
          (bhzParityLetter k)
          (criticalBHZa (k + 1))
          w)

@[simp] theorem bhzCriticalDirectiveImage_zero
    (w : List Bool) :
    bhzCriticalDirectiveImage 0 w = w := rfl

/-- directive composition preserves the empty word. -/
@[simp] theorem bhzCriticalDirectiveImage_nil
    (k : ℕ) :
    bhzCriticalDirectiveImage k [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [bhzCriticalDirectiveImage, ih]

@[simp] theorem bhzCriticalDirectiveImage_succ
    (k : ℕ)
    (w : List Bool) :
    bhzCriticalDirectiveImage (k + 1) w =
      bhzCriticalDirectiveImage k
        (bhzTauIter
          (bhzParityLetter k)
          (criticalBHZa (k + 1))
          w) := rfl

/-- directive composition is a word morphism. -/
@[simp] theorem bhzCriticalDirectiveImage_append
    (k : ℕ)
    (u v : List Bool) :
    bhzCriticalDirectiveImage k (u ++ v) =
      bhzCriticalDirectiveImage k u ++
        bhzCriticalDirectiveImage k v := by
  induction k generalizing u v with
  | zero => rfl
  | succ k ih =>
      simp [bhzCriticalDirectiveImage, ih]

/-- directive image commutes with finite word powers. -/
theorem bhzCriticalDirectiveImage_wordPow
    (k n : ℕ)
    (w : List Bool) :
    bhzCriticalDirectiveImage k (bhzWordPow w n) =
      bhzWordPow (bhzCriticalDirectiveImage k w) n := by
  induction n with
  | zero => simp [bhzWordPow]
  | succ n ih =>
      simp [bhzWordPow, ih]

/-- canonical standard word at BHZ level `k`. -/
def bhzCriticalStandardWord
    (k : ℕ) : List Bool :=
  bhzCriticalDirectiveImage k [bhzParityLetter k]

/-- the opposite one-letter image at the same directive level. -/
def bhzCriticalCompanionWord
    (k : ℕ) : List Bool :=
  bhzCriticalDirectiveImage k [!(bhzParityLetter k)]

/-- The companion at level `k+1` is the standard word at level `k`. -/
theorem bhzCriticalCompanionWord_succ
    (k : ℕ) :
    bhzCriticalCompanionWord (k + 1) =
      bhzCriticalStandardWord k := by
  unfold bhzCriticalCompanionWord bhzCriticalStandardWord
  rw [bhzCriticalDirectiveImage_succ]
  simp

/--
Standard words satisfy the usual Sturmian recurrence

  S_(k+1) = S_k ^ a_(k+1) ++ companion_k.
-/
theorem bhzCriticalStandardWord_succ
    (k : ℕ) :
    bhzCriticalStandardWord (k + 1) =
      bhzWordPow
          (bhzCriticalStandardWord k)
          (criticalBHZa (k + 1)) ++
        bhzCriticalCompanionWord k := by
  unfold bhzCriticalStandardWord
  rw [bhzCriticalDirectiveImage_succ]
  rw [bhzParityLetter_succ]
  rw [bhzTauIter_single_not]
  rw [bhzCriticalDirectiveImage_append]
  rw [bhzCriticalDirectiveImage_wordPow]
  rfl

/-- Two-step standard-word recurrence. -/
theorem bhzCriticalStandardWord_add_two
    (k : ℕ) :
    bhzCriticalStandardWord (k + 2) =
      bhzWordPow
          (bhzCriticalStandardWord (k + 1))
          (criticalBHZa (k + 2)) ++
        bhzCriticalStandardWord k := by
  have h := bhzCriticalStandardWord_succ (k + 1)
  rw [bhzCriticalCompanionWord_succ] at h
  simpa [Nat.add_assoc] using h

/--
BHZ standard root has exact denominator length `q_k`.
-/
theorem bhzCriticalStandardWord_length
    (k : ℕ) :
    (bhzCriticalStandardWord k).length =
      criticalBHZq k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · simp [
          bhzCriticalStandardWord,
          bhzCriticalDirectiveImage,
          bhzParityLetter,
          criticalBHZq_zero
        ]
      · rcases k with _ | k
        · simp [
            bhzCriticalStandardWord,
            bhzCriticalDirectiveImage,
            bhzParityLetter,
            criticalBHZa_one,
            criticalBHZq_one
          ]
        · have hWord := bhzCriticalStandardWord_add_two k
          rw [hWord, List.length_append, bhzWordPow_length]
          rw [ih (k + 1) (by omega)]
          rw [ih k (by omega)]
          have hRec :=
            criticalBHZq_recurrence
              (k := k + 2) (by omega)
          simpa [Nat.add_assoc] using hRec.symm

/-- Standard candidate root is literally the repository denominator. -/
@[simp] theorem bhzCriticalStandardRoot_eq_criticalPowerP
    (k : ℕ) :
    bhzCriticalStandardRoot k =
      criticalPowerP (k + 1) := by
  rfl

/--
Canonical semistandard word at level `k`.

For `k=0` we use the empty placeholder; Proposition 3.3 only calls this family
when `k>=1` and `0<c_k<a_k`.
-/
def bhzCriticalSemistandardWord
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) :
    ℕ → List Bool
  | 0 => []
  | k + 1 =>
      bhzCriticalDirectiveImage k
        (bhzTauIter
          (bhzParityLetter k)
          (criticalBHZa (k + 1) - P.digit (k + 1))
          [bhzParityLetter (k + 1)])

/-- One-step source form of the semistandard word. -/
theorem bhzCriticalSemistandardWord_succ
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalSemistandardWord P (k + 1) =
      bhzWordPow
          (bhzCriticalStandardWord k)
          (criticalBHZa (k + 1) - P.digit (k + 1)) ++
        bhzCriticalCompanionWord k := by
  simp only [bhzCriticalSemistandardWord]
  rw [bhzParityLetter_succ]
  rw [bhzTauIter_single_not]
  rw [bhzCriticalDirectiveImage_append]
  rw [bhzCriticalDirectiveImage_wordPow]
  rfl

/-- For nontrivial levels the companion becomes `S_(k-2)`. -/
theorem bhzCriticalSemistandardWord_add_two
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalSemistandardWord P (k + 2) =
      bhzWordPow
          (bhzCriticalStandardWord (k + 1))
          (criticalBHZa (k + 2) - P.digit (k + 2)) ++
        bhzCriticalStandardWord k := by
  have h := bhzCriticalSemistandardWord_succ P (k + 1)
  rw [bhzCriticalCompanionWord_succ] at h
  simpa [Nat.add_assoc] using h

/--
Semistandard canonical word has exact source root length

  q_k - c_k q_(k-1).
-/
theorem bhzCriticalSemistandardWord_length
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hDigit : P.digit k ≤ criticalBHZa k) :
    (bhzCriticalSemistandardWord P k).length =
      bhzCriticalSemistandardRoot P k := by
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · omega
  have hWord :=
    bhzCriticalSemistandardWord_add_two P k
  rw [hWord, List.length_append, bhzWordPow_length]
  rw [bhzCriticalStandardWord_length, bhzCriticalStandardWord_length]
  have hRec :=
    criticalBHZq_recurrence
      (k := k + 2) (by omega)
  unfold bhzCriticalSemistandardRoot
  have hPred1 : k + 2 - 1 = k + 1 := by omega
  have hPred2 : k + 2 - 2 = k := by omega
  rw [hPred1, hPred2] at hRec
  rw [hPred1]
  have hMulLe :
      P.digit (k + 2) * criticalBHZq (k + 1) ≤
        criticalBHZa (k + 2) * criticalBHZq (k + 1) :=
    Nat.mul_le_mul_right _ hDigit
  rw [Nat.sub_mul]
  rw [hRec]
  exact (Nat.sub_add_comm hMulLe).symm

/--
Strict source condition `c_k<a_k` makes the semistandard root positive.
-/
theorem bhzCriticalSemistandardRoot_pos
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hDigit : P.digit k < criticalBHZa k) :
    0 < bhzCriticalSemistandardRoot P k := by
  have hQPos : 0 < criticalBHZq (k - 1) :=
    criticalBHZq_pos (k - 1)
  have hMulLt :
      P.digit k * criticalBHZq (k - 1) <
        criticalBHZa k * criticalBHZq (k - 1) :=
    (Nat.mul_lt_mul_right hQPos).2 hDigit
  have hRec := criticalBHZq_recurrence (k := k) hk
  have hMulLtQ :
      P.digit k * criticalBHZq (k - 1) <
        criticalBHZq k := by
    calc
      P.digit k * criticalBHZq (k - 1)
          < criticalBHZa k * criticalBHZq (k - 1) := hMulLt
      _ ≤ criticalBHZa k * criticalBHZq (k - 1) +
            criticalBHZq (k - 2) := Nat.le_add_right _ _
      _ = criticalBHZq k := hRec.symm
  unfold bhzCriticalSemistandardRoot
  exact Nat.sub_pos_of_lt hMulLtQ

/--
Semistandard root in the repository's `criticalPowerP` coordinate.
This is the direct handoff form for the next Rhin stage.
-/
theorem bhzCriticalSemistandardRoot_eq_criticalPowerP
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 1 ≤ k) :
    bhzCriticalSemistandardRoot P k =
      criticalPowerP (k + 1) -
        P.digit k * criticalPowerP k := by
  unfold bhzCriticalSemistandardRoot criticalBHZq
  have hPred : k - 1 + 1 = k := by omega
  rw [hPred]

/--
Equivalent recurrence form

  root = (a_k-c_k) q_(k-1) + q_(k-2).
-/
theorem bhzCriticalSemistandardRoot_eq_residual_recurrence
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hDigit : P.digit k ≤ criticalBHZa k) :
    bhzCriticalSemistandardRoot P k =
      (criticalBHZa k - P.digit k) *
          criticalBHZq (k - 1) +
        criticalBHZq (k - 2) := by
  have hRec := criticalBHZq_recurrence (k := k) hk
  have hMulLe :
      P.digit k * criticalBHZq (k - 1) ≤
        criticalBHZa k * criticalBHZq (k - 1) :=
    Nat.mul_le_mul_right _ hDigit
  unfold bhzCriticalSemistandardRoot
  rw [Nat.sub_mul]
  rw [hRec]
  omega

end ExternalArithmetic
end CSTMicro
end Collatz2
