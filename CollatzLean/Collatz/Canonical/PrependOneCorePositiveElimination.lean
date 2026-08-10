import CollatzLean.Collatz.Canonical.PrependOneCoreBranches
import CollatzLean.Collatz.External.TwoThreeEffectiveGap

/-!
# prepend-one CORE の positive quotient 完全排除

`j = 1,2` の CORE failure は既に

* `j = 1` なら `2*g < p`
* `j = 2` なら `4*g < p`

を強制する。

ここではEllison型2-3 gap外部入力とLean内有限検証により、
全 contracting prepend-one word で `p <= g` を得る。
したがって positive replay quotient `j > 0` は長さに関係なくCOREを満たし、
`PrependOneCorePrinciple` に残る未解決枝は `j = 0` だけになる。
-/

namespace Collatz
namespace Word

/--
Ellison型gap入力のもとでは、contracting prepend-one word のgapは
全長で odd-step 数以上になる。
-/
theorem prependOne_contractingGap_ge_oddSteps
    (hGap : External.TwoThreeEffectiveGapInput)
    {v : Collatz.Word}
    (hC : Word.Contracting (1 :: v)) :
    Word.oddSteps v + 1 ≤
      Word.contractingGap (1 :: v) := by
  have hcontract :
      3 ^ Word.oddSteps (1 :: v) <
        2 ^ Word.twoSteps (1 :: v) := by
    simpa [Word.Contracting] using hC
  have h :=
    External.twoThreeGap_ge_exponent
      hGap
      (p := Word.oddSteps (1 :: v))
      (H := Word.twoSteps (1 :: v))
      hcontract
  simpa [Word.contractingGap] using h

/--
Ellison型gap入力のもとでは、任意の positive replay quotient がCOREを満たす。
`j=1,2` に限らず `j>0` 全体を一括で閉じる。
-/
theorem prependOneCore_positive
    (hGap : External.TwoThreeEffectiveGapInput)
    {v : Collatz.Word} {quotient : ℕ}
    (hvne : v ≠ [])
    (hC : Word.Contracting (1 :: v))
    (hAll : Word.AllSuffixesContracting v)
    (hq : 0 < quotient) :
    PrependOneCoreCondition v quotient := by
  have hgap :
      Word.oddSteps v + 1 ≤
        Word.contractingGap (1 :: v) :=
    prependOne_contractingGap_ge_oddSteps hGap hC
  have hqOne : 1 ≤ quotient := by omega
  have hgapQ :
      Word.contractingGap (1 :: v) ≤
        Word.contractingGap (1 :: v) * quotient := by
    have h :=
      Nat.mul_le_mul_left
        (Word.contractingGap (1 :: v)) hqOne
    simpa using h
  have hlarge :
      Word.oddSteps v + 1 ≤
        2 * Word.contractingGap (1 :: v) * quotient := by
    calc
      Word.oddSteps v + 1
          ≤ Word.contractingGap (1 :: v) := hgap
      _ ≤ Word.contractingGap (1 :: v) * quotient := hgapQ
      _ ≤ 2 * Word.contractingGap (1 :: v) * quotient := by
        nlinarith
  exact prependOneCore_of_gap_length hvne hC hAll hlarge

/-- Ellison型gap入力のもとで quotient `1` 枝は全長で閉じる。 -/
theorem prependOneCoreOnePrinciple_of_ellison
    (hGap : External.TwoThreeEffectiveGapInput) :
    PrependOneCoreOnePrinciple := by
  intro v boundary hvne _hvalid hC hAll _D
  exact prependOneCore_positive hGap hvne hC hAll (by omega)

/-- Ellison型gap入力のもとで quotient `2` 枝も全長で閉じる。 -/
theorem prependOneCoreTwoPrinciple_of_ellison
    (hGap : External.TwoThreeEffectiveGapInput) :
    PrependOneCoreTwoPrinciple := by
  intro v boundary hvne _hvalid hC hAll _D
  exact prependOneCore_positive hGap hvne hC hAll (by omega)

/--
Ellison型gap入力のもとでは、元のCORE原理に必要なのは quotient `0` 枝だけ。
-/
theorem prependOneCorePrinciple_of_ellison_zero
    (hGap : External.TwoThreeEffectiveGapInput)
    (hZero : PrependOneCoreZeroPrinciple) :
    PrependOneCorePrinciple := by
  exact prependOneCorePrinciple_of_three_branches
    hZero
    (prependOneCoreOnePrinciple_of_ellison hGap)
    (prependOneCoreTwoPrinciple_of_ellison hGap)


end Word
end Collatz
