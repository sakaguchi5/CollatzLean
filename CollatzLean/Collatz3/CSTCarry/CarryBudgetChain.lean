import CollatzLean.Collatz3.CSTCarry.ZeroDefectHead

/-!
# Collatz3 CSTCarry: strict terminal budget + 任意個の weak block の telescope

前段の `complementBudget_telescope` は二 block 版だった。
Record 分解では terminal block の後ろに複数の interior block が続くため、
これを有限個へ反復した形を置く。

新しい数学仮定は導入しない。
各 piece が

* digit 数 = row 数,
* weak complement budget,

を満たすことだけを再帰 predicate にまとめる。
-/

namespace Collatz3
namespace CSTCarry

/-- budget telescope 用の薄い block data。 -/
structure CarryBudgetPiece where
  rows : List FerrersRow
  digits : List ℕ

namespace CarryBudgetPiece

/-- piece の digit 数と row 数が一致。 -/
def LengthCompatible (B : CarryBudgetPiece) : Prop :=
  B.digits.length = B.rows.length

/-- piece が interior 用 weak budget を満たす。 -/
def WeakBudget (M : ℕ) (B : CarryBudgetPiece) : Prop :=
  WeakComplementBudget M B.rows B.digits

end CarryBudgetPiece

/-- weak interior piece 列。 -/
def WeakBudgetChain (M : ℕ) : List CarryBudgetPiece → Prop
  | [] => True
  | B :: Bs =>
      B.LengthCompatible ∧ B.WeakBudget M ∧ WeakBudgetChain M Bs

/-- piece 列の row を順に flatten。 -/
def rowsOfBudgetPieces : List CarryBudgetPiece → List FerrersRow
  | [] => []
  | B :: Bs => B.rows ++ rowsOfBudgetPieces Bs

/-- piece 列の digits を同じ順に flatten。 -/
def digitsOfBudgetPieces : List CarryBudgetPiece → List ℕ
  | [] => []
  | B :: Bs => B.digits ++ digitsOfBudgetPieces Bs

/--
terminal strict budget の後ろへ任意個の weak interior block を付けても
全体は strict complement budget を保つ。
-/
theorem complementBudget_telescope_chain
    {M : ℕ}
    {terminalRows : List FerrersRow}
    {terminalDigits : List ℕ}
    {blocks : List CarryBudgetPiece}
    (hTerminalLen : terminalDigits.length = terminalRows.length)
    (hTerminal : ComplementBudget M terminalRows terminalDigits)
    (hBlocks : WeakBudgetChain M blocks) :
    ComplementBudget M
      (terminalRows ++ rowsOfBudgetPieces blocks)
      (terminalDigits ++ digitsOfBudgetPieces blocks) := by
  induction blocks generalizing terminalRows terminalDigits with
  | nil =>
      simpa [rowsOfBudgetPieces, digitsOfBudgetPieces] using hTerminal
  | cons B Bs ih =>
      simp only [WeakBudgetChain] at hBlocks
      have hBLen : B.digits.length = B.rows.length :=
        hBlocks.1
      have hBWeak : WeakComplementBudget M B.rows B.digits :=
        hBlocks.2.1
      have hNext :
          ComplementBudget M
            (terminalRows ++ B.rows)
            (terminalDigits ++ B.digits) :=
        complementBudget_telescope
          hTerminalLen hTerminal hBWeak
      have hNextLen :
          (terminalDigits ++ B.digits).length =
            (terminalRows ++ B.rows).length := by
        simp [hTerminalLen, hBLen]
      have hTail := ih hNextLen hNext hBlocks.2.2
      simpa [rowsOfBudgetPieces, digitsOfBudgetPieces, List.append_assoc] using hTail

end CSTCarry
end Collatz3
