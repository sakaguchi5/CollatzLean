import CollatzLean.Collatz2.Global.SignDichotomy

/-!
# Collatz2: unbounded-orbit reduction to determinant sign

第4段階の global checkpoint。

`HasUnboundedOddOrbit` から future minima を選び、
lossless `AdjacentTransferChain` を構成する。
その後の二分岐は transfer determinant の nonzero sign profile に対する
cofinal dichotomy だけから生じる。

従って Expanding / Contracting は発散側の primitive 仮定ではなく corollary。
-/

namespace Collatz2

/-- positive determinant が cofinal な adjacent transfer chain が存在する。 -/
def HasPositiveDeterminantCofinalChain : Prop :=
  ∃ O : OddOrbit,
    ∃ C : AdjacentTransferChain O,
      C.PositiveDeterminantCofinal

/-- negative determinant が cofinal な adjacent transfer chain が存在する。 -/
def HasNegativeDeterminantCofinalChain : Prop :=
  ∃ O : OddOrbit,
    ∃ C : AdjacentTransferChain O,
      C.NegativeDeterminantCofinal

/--
非有界 odd-only 軌道は determinant sign の二つの cofinal branch のどちらかへ落ちる。
-/
theorem unbounded_to_determinant_sign_cofinal :
    HasUnboundedOddOrbit →
      HasPositiveDeterminantCofinalChain ∨
        HasNegativeDeterminantCofinalChain := by
  classical
  rintro ⟨O, hU⟩
  let C : AdjacentTransferChain O :=
    AdjacentTransferChain.ofUnbounded O hU
  rcases C.determinantSignCofinal with hP | hN
  · exact Or.inl ⟨O, C, hP⟩
  · exact Or.inr ⟨O, C, hN⟩

/-- 従来名 Expanding が cofinal な chain が存在する。 -/
def HasExpandingCofinalChain : Prop :=
  ∃ O : OddOrbit,
    ∃ C : AdjacentTransferChain O,
      C.ExpandingCofinal

/-- 従来名 Contracting が cofinal な chain が存在する。 -/
def HasContractingCofinalChain : Prop :=
  ∃ O : OddOrbit,
    ∃ C : AdjacentTransferChain O,
      C.ContractingCofinal

/--
発散側の Expanding / Contracting 二分岐。
これは上の determinant-sign theorem の従来名による読み替え。
-/
theorem unbounded_to_expanding_or_contracting :
    HasUnboundedOddOrbit →
      HasExpandingCofinalChain ∨
        HasContractingCofinalChain := by
  classical
  rintro ⟨O, hU⟩
  let C : AdjacentTransferChain O :=
    AdjacentTransferChain.ofUnbounded O hU
  rcases C.expanding_or_contracting_cofinal with hE | hC
  · exact Or.inl ⟨O, C, hE⟩
  · exact Or.inr ⟨O, C, hC⟩

/--
両 cofinal sign branch を排除できれば非有界 odd-only 軌道は存在しない。
-/
theorem no_unbounded_odd_orbit
    (hE : ¬ HasExpandingCofinalChain)
    (hC : ¬ HasContractingCofinalChain) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_to_expanding_or_contracting hU with hExp | hCon
  · exact hE hExp
  · exact hC hCon

end Collatz2
