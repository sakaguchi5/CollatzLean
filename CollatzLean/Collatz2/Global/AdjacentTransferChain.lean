import CollatzLean.Collatz2.Orbit.FutureMinimumSelection
import CollatzLean.Collatz2.Canonical.ReplayExtremality
import CollatzLean.Collatz2.Local.Defect

/-!
# Collatz2: adjacent future-minimum affine-transfer chain

global 発散側の正本は ExpandingTower / ContractingTower ではない。

非有界 orbit と選択済み future minima から、
隣接する minima 間の actual word / Runs / AffineTransfer の無限列を得る。
determinant sign はこの lossless chain の projection として次ファイルで分類する。
-/

namespace Collatz2

/--
非有界 orbit 上の adjacent future-minimum transfer chain。

選択手続きそのものは保持しない。
`FutureMinima` と unboundedness だけが global source data。
-/
structure AdjacentTransferChain (O : OddOrbit) where
  unbounded : O.Unbounded
  minima : O.FutureMinima

namespace AdjacentTransferChain

/-- 非有界 orbit から一つの adjacent transfer chain を選ぶ。 -/
noncomputable def ofUnbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    AdjacentTransferChain O where
  unbounded := hU
  minima := OddOrbit.FutureMinimumSelection.futureMinima O hU

/-- 第 `n` block の開始 future-minimum index。 -/
def startIndex
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ℕ :=
  C.minima.index n

/-- 第 `n` block の終了 future-minimum index。 -/
def endIndex
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ℕ :=
  C.minima.index (n + 1)

/-- adjacent index 間の長さ。 -/
def length
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ℕ :=
  C.endIndex n - C.startIndex n

/-- adjacent future-minimum 間の actual exponent word。 -/
def word
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    Word :=
  O.segment (C.startIndex n) (C.length n)

/-- 第 `n` block の lossless affine transfer。 -/
def transfer
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    AffineTransfer :=
  AffineTransfer.ofWord (C.word n)

/-- block の actual start value。 -/
def startValue
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ℕ :=
  O.value (C.startIndex n)

/-- block の actual endpoint value。 -/
def endValue
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ℕ :=
  O.value (C.endIndex n)

/-- block start は future minimum。 -/
theorem startFutureMinimum
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    O.FutureMinimumAt (C.startIndex n) :=
  C.minima.minimum n

/-- block endpoint も future minimum。 -/
theorem endFutureMinimum
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    O.FutureMinimumAt (C.endIndex n) :=
  C.minima.minimum (n + 1)

/-- end index は start + length。 -/
theorem endIndex_eq_startIndex_add_length
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.endIndex n = C.startIndex n + C.length n := by
  have hle :
      C.minima.index n ≤ C.minima.index (n + 1) :=
    (C.minima.index_strict (Nat.lt_succ_self n)).le
  change
    C.minima.index (n + 1) =
      C.minima.index n +
        (C.minima.index (n + 1) - C.minima.index n)
  simpa [Nat.add_comm] using
    (Nat.sub_add_cancel hle).symm

/-- adjacent block の長さは正。 -/
theorem length_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    0 < C.length n := by
  unfold length endIndex startIndex
  exact Nat.sub_pos_of_lt
    (C.minima.index_strict (Nat.lt_succ_self n))

@[simp] theorem word_length
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    (C.word n).length = C.length n := by
  simp [word]

/-- adjacent block word は非空。 -/
theorem word_nonempty
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.word n ≠ [] := by
  intro h
  have hzero : C.length n = 0 := by
    simpa using congrArg List.length h
  exact (C.length_pos n).ne' hzero

/-- adjacent block は actual normalized run。 -/
theorem runs
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    Runs (C.word n) (C.startValue n) (C.endValue n) := by
  unfold word startValue endValue
  rw [C.endIndex_eq_startIndex_add_length n]
  exact O.runsSegment (C.startIndex n) (C.length n)

/-- adjacent block word は valid。 -/
theorem word_valid
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    Word.Valid (C.word n) :=
  (C.runs n).valid

/-- adjacent block の affine realization。 -/
theorem realizes
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    Word.Realizes
      (C.word n)
      (C.startValue n)
      (C.endValue n) :=
  (C.runs n).realizes

/-- 非有界 future-minimum chain の adjacent value は strict に増える。 -/
theorem startValue_lt_endValue
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.startValue n < C.endValue n := by
  exact C.minima.value_strict (Nat.lt_succ_self n)

/--
各 adjacent block は actual positive return。
PositiveReturn 自体は start-defect sign の corollary。
-/
theorem positiveReturn
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    Word.PositiveReturn
      (C.word n)
      (C.startValue n)
      (C.endValue n) := by
  exact (Word.positiveReturn_iff).2
    ⟨C.realizes n, C.startValue_lt_endValue n⟩

/-- 各 block の start defect は正。 -/
theorem startDefect_pos
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    0 < Word.startDefect (C.word n) (C.startValue n) :=
  (C.positiveReturn n).2

/-- determinant sign profile の positive 側。 -/
def PositiveAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    Prop :=
  AffineTransfer.PositiveDeterminant (C.transfer n)

/-- determinant sign profile の negative 側。 -/
def NegativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    Prop :=
  AffineTransfer.NegativeDeterminant (C.transfer n)

/-- 各 block determinant は0ではない。 -/
theorem determinant_ne_zero
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    (C.transfer n).determinant ≠ 0 := by
  simpa [transfer] using
    Word.determinant_ne_zero_of_valid_nonempty
      (C.word_valid n)
      (C.word_nonempty n)

/-- 各 block の sign は positive または negative。 -/
theorem positive_or_negative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.PositiveAt n ∨ C.NegativeAt n := by
  simpa [PositiveAt, NegativeAt, transfer] using
    Word.positive_or_negative_determinant_of_valid_nonempty
      (C.word_valid n)
      (C.word_nonempty n)

/-- positive determinant は従来名 Expanding と同値。 -/
theorem positiveAt_iff_expanding
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.PositiveAt n ↔ Word.Expanding (C.word n) := by
  rfl

/-- negative determinant は従来名 Contracting と同値。 -/
theorem negativeAt_iff_contracting
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.NegativeAt n ↔ Word.Contracting (C.word n) := by
  rfl

/--
negative determinant block は actual positive return との符号ねじれを持つ。
-/
theorem contracting_positiveReturn
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Word.Contracting (C.word n) ∧
      Word.PositiveReturn
        (C.word n)
        (C.startValue n)
        (C.endValue n) := by
  exact ⟨(C.negativeAt_iff_contracting n).1 hN, C.positiveReturn n⟩

/--
第3段階との接続。
negative determinant の adjacent positive return は replay extremality により
canonical (`q=0`) positive return を強制する。
-/
theorem canonical_positive_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    Word.canonicalStart (C.word n) <
      Word.canonicalEnd (C.word n) := by
  have hC : Word.Contracting (C.word n) :=
    (C.negativeAt_iff_contracting n).1 hN
  exact
    (C.runs n).canonical_positive_of_contracting_positive
      (C.word_nonempty n)
      hC
      (C.startValue_lt_endValue n)

end AdjacentTransferChain
end Collatz2
