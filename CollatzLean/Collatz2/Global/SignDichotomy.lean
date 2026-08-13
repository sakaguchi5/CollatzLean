import CollatzLean.Collatz2.Global.AdjacentTransferChain

/-!
# Collatz2: cofinal determinant-sign dichotomy

Expanding / Contracting を global primitive branch にしない。

nonzero determinant の sign profile に対して、まずより強い

  positive determinant cofinal
    ∨ eventually negative determinant

を取る。従来の positive cofinal / negative cofinal dichotomy はその corollary。
-/

namespace Collatz2

/-- 自然数列上で property `P` が arbitrarily late に現れる。 -/
def Cofinal (P : ℕ → Prop) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n

namespace Cofinal

/-- cofinal でない property はある位置以後ずっと偽。 -/
theorem eventually_not_of_not
    {P : ℕ → Prop}
    (h : ¬ Cofinal P) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ P n := by
  classical
  by_contra hnone
  apply h
  intro N
  by_contra hN
  apply hnone
  refine ⟨N, ?_⟩
  intro n hn hPn
  exact hN ⟨n, hn, hPn⟩

end Cofinal

namespace AdjacentTransferChain

/-- positive determinant が cofinal。 -/
def PositiveDeterminantCofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    Prop :=
  Cofinal (fun n => C.PositiveAt n)

/-- negative determinant が cofinal。 -/
def NegativeDeterminantCofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    Prop :=
  Cofinal (fun n => C.NegativeAt n)

/-- ある位置以後、全 adjacent block の determinant が負。 -/
def EventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C.NegativeAt n

/--
eventually negative なら当然 negative determinant は cofinal。
-/
theorem negativeDeterminantCofinal_of_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (h : C.EventuallyNegative) :
    C.NegativeDeterminantCofinal := by
  rcases h with ⟨N, hN⟩
  intro M
  let n := max M N
  exact ⟨n, le_max_left _ _, hN n (le_max_right _ _)⟩

/--
nonzero determinant の sign profile に対する強い global dichotomy。
positive sign が cofinal でなければ、その否定は tail 全体で negative sign を強制する。
-/
theorem positiveCofinal_or_eventuallyNegative
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    C.PositiveDeterminantCofinal ∨ C.EventuallyNegative := by
  classical
  by_cases hP : C.PositiveDeterminantCofinal
  · exact Or.inl hP
  · right
    obtain ⟨N, hN⟩ := Cofinal.eventually_not_of_not hP
    refine ⟨N, ?_⟩
    intro n hn
    have hnotP : ¬ C.PositiveAt n := hN n hn
    rcases C.positive_or_negative n with hPos | hNeg
    · exact False.elim (hnotP hPos)
    · exact hNeg

/--
従来の cofinal sign dichotomy は強い dichotomy の corollary。
-/
theorem determinantSignCofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    C.PositiveDeterminantCofinal ∨
      C.NegativeDeterminantCofinal := by
  rcases C.positiveCofinal_or_eventuallyNegative with hP | hN
  · exact Or.inl hP
  · exact Or.inr (C.negativeDeterminantCofinal_of_eventuallyNegative hN)

/-- 従来名 Expanding が cofinal。 -/
def ExpandingCofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    Prop :=
  Cofinal (fun n => Word.Expanding (C.word n))

/-- 従来名 Contracting が cofinal。 -/
def ContractingCofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    Prop :=
  Cofinal (fun n => Word.Contracting (C.word n))

/-- positive determinant cofinal と Expanding cofinal は同じ命題。 -/
theorem positiveDeterminantCofinal_iff_expandingCofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    C.PositiveDeterminantCofinal ↔ C.ExpandingCofinal := by
  rfl

/-- negative determinant cofinal と Contracting cofinal は同じ命題。 -/
theorem negativeDeterminantCofinal_iff_contractingCofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    C.NegativeDeterminantCofinal ↔ C.ContractingCofinal := by
  rfl

/--
Expanding / Contracting の global 二分岐は determinant-sign dichotomy の corollary。
-/
theorem expanding_or_contracting_cofinal
    {O : OddOrbit}
    (C : AdjacentTransferChain O) :
    C.ExpandingCofinal ∨ C.ContractingCofinal := by
  rcases C.determinantSignCofinal with hP | hN
  · exact Or.inl
      ((C.positiveDeterminantCofinal_iff_expandingCofinal).1 hP)
  · exact Or.inr
      ((C.negativeDeterminantCofinal_iff_contractingCofinal).1 hN)

end AdjacentTransferChain
end Collatz2
