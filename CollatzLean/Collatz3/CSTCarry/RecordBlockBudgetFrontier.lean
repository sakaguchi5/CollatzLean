import CollatzLean.Collatz3.CSTCarry.RecordCarryDigitFactorization
import CollatzLean.Collatz3.Critical.RecordCarryBlockExact

/-!
# Collatz3 CSTCarry: Record block budget の現在の frontier

ここまでで

* actual profile rows の block slicing、
* block weighted defect と shifted-local defect の exact scaling、
* canonical digit / final carry の row split、
* zero-defect head の strict-bound preservation、

は追加仮定なしで閉じた。

残る数学的核心を fake theorem にせず predicate として一箇所に切り出す。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/--
terminal local critical block に必要な shifted-local strict budget。
`D` はその actual ternary digit slice の complement value を入れる場所である。
-/
def ShiftedTerminalBlockBudget
    {m : ℕ}
    (h : Profile m)
    (a r D : ℕ) : Prop :=
  shiftedBlockWeightedDefect h a r <
    2 ^ criticalTwoDepth r * (D + 1)

/--
terminal Record block の actual row defect budget は、terminal carry `0` の下で
上の shifted-local budget と exact に同値。
これは frontier の仮定ではなく、既証明 scaling の公開 wrapper。
-/
theorem terminalRecordBlock_actualBudget_iff_shifted
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r D : ℕ}
    (Brec : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hStartRoof : IsRoofCut h a)
    (hTerminal : a + r = m)
    (hNo : NoPrematureCarryOneRoofReturn h a r)
    (hCarryZero : beattyCarry a r = 0) :
    ferrersWeightedDefect
          (profileBlockCarryRows h a r (Nat.le_of_eq hTerminal)) <
        2 ^ criticalTwoDepth m * (D + 1) ↔
      ShiftedTerminalBlockBudget h a r D := by
  have B : IsLocalCriticalBlock h a r :=
    (isLocalCriticalBlock_iff_noPrematureCarryOneRoofReturn_and_terminalCarryZero
      A Brec hStartRoof hTerminal).2 ⟨hNo, hCarryZero⟩
  exact profileBlockRows_terminal_strictBudget_iff_shiftedLocal
    A hStartRoof B hTerminal hCarryZero

end CSTCarry
end Collatz3
