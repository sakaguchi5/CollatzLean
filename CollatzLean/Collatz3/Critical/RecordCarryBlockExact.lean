import CollatzLean.Collatz3.Critical.RecordCarryExact

/-!
# Collatz3: 一 block 単位の exact carry characterization

chain 全体の再帰定理に埋もれていた interior / terminal の局所同値を、
一 block の名前付き theorem として切り出す。
-/

namespace Collatz3
namespace Critical

/--
roof-to-roof strict record block では terminal minimal depth は自動である。
従って local criticality に残る exact 条件は、途中の
`premature roof return + carry 1` が無いことだけ。
-/
theorem isLocalCriticalBlock_iff_noPrematureCarryOneRoofReturn_of_roofRecordBlock
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hStartRoof : IsRoofCut h a)
    (hEndRoof : IsRoofCut h (a + r)) :
    IsLocalCriticalBlock h a r ↔
      NoPrematureCarryOneRoofReturn h a r := by
  have hEnd : a + r ≤ m := Nat.le_of_lt hEndRoof.lt_width
  have hPrefixIff :=
    localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
      A hStartRoof hEnd
  constructor
  · intro L
    exact hPrefixIff.1 L.2.2.2
  · intro C
    have hMinimal :=
      interior_localDepth_eq_criticalTwoDepth
        A B hStartRoof hEndRoof
    exact
      ⟨B.length_pos,
        hEnd,
        hMinimal,
        hPrefixIff.2 C⟩

/--
terminal strict record block では local criticality は exact に

* premature carry-1 roof return が無いこと、
* terminal carry が `0` であること

の二条件に分解される。
-/
theorem isLocalCriticalBlock_iff_noPrematureCarryOneRoofReturn_and_terminalCarryZero
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hStartRoof : IsRoofCut h a)
    (hTerminal : a + r = m) :
    IsLocalCriticalBlock h a r ↔
      (NoPrematureCarryOneRoofReturn h a r ∧
        beattyCarry a r = 0) := by
  have hEnd : a + r ≤ m := Nat.le_of_eq hTerminal
  have hPrefixIff :=
    localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
      A hStartRoof hEnd
  have hTerminalIff :=
    terminalMinimal_iff_beattyCarry_eq_zero
      A hStartRoof hTerminal
  constructor
  · intro L
    exact
      ⟨hPrefixIff.1 L.2.2.2,
        hTerminalIff.1 L.2.2.1⟩
  · rintro ⟨hNo, hZero⟩
    exact
      ⟨B.length_pos,
        hEnd,
        hTerminalIff.2 hZero,
        hPrefixIff.2 hNo⟩

end Critical
end Collatz3
