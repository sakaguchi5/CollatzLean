import CollatzLean.Collatz3.Experimental2.RoofPath

/-!
# Collatz3 Experimental2: Record 型 chain の exact carry law

`RoofPath` では一つの局所区間について

* `localDepth + roofSlack = blockRoof + carry`,
* local failure `↔` roof return と carry `1`,
* terminal minimality `↔` terminal carry `0`

までを既に証明している。

このファイルでは新しい profile 構造を導入せず、その局所 law を有限 block chain へ持ち上げる。
保存するのは chain-level の combinatorial predicate だけであり、
`Critical`, `Ferrers`, `RecordFerrers`, actual Collatz orbit には依存しない。

中心結果は

`完全 carry compatibility ↔ 全 block の local criticality`

である。また外部の record/skeleton geometry が interior carry `1` を保証する場合には、
terminal carry と premature return 排除だけを保存する contextual 版へ弱められる。
-/

namespace Collatz3
namespace Experimental2

/--
proper local prefix で禁止する exact event。

途中で再び roof に乗り、その接合 carry が `1` になることを排除する。
-/
def NoPrematureCarryOneRoofReturn
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a r : ℕ) : Prop :=
  ∀ j : ℕ,
    0 < j →
    j < r →
    ¬ (IsProperRoofCut β m height (a + j) ∧
      roofCarry β a j = 1)

/--
proper-prefix roof bound と premature carry-1 roof return 排除は exact に同値。

これは `RoofPath.localFailure_iff_roofReturn_and_carryOne` の有限区間版。
-/
theorem localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ}
    (hStart : IsProperRoofCut β m height a)
    (hEnd : a + r ≤ m) :
    (∀ j : ℕ,
      0 < j →
      j < r →
      localDepth height a j ≤ β j) ↔
      NoPrematureCarryOneRoofReturn β m height a r := by
  constructor
  · intro hBound j hjPos hjLt hBad
    have hEndLt : a + j < m := by omega
    have hFail :=
      (localFailure_iff_roofReturn_and_carryOne
        U A hStart hEndLt).2 hBad
    exact (Nat.not_lt_of_ge (hBound j hjPos hjLt)) hFail
  · intro hNo j hjPos hjLt
    by_contra hNot
    have hFail : β j < localDepth height a j := by omega
    have hEndLt : a + j < m := by omega
    have hBad :=
      (localFailure_iff_roofReturn_and_carryOne
        U A hStart hEndLt).1 hFail
    exact hNo j hjPos hjLt hBad

/--
interior roof-to-roof block では minimal local depth と carry `1` が exact に同値。

terminal では `carry = 0` になるのに対し、interior endpoint 自身が roof 上なので
局所保存式の slack が `0` になり、`criticalDepth = β(r)+1` を作るには carry `1` が必要になる。
-/
theorem interiorMinimal_iff_carryOne
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ}
    (hStart : IsProperRoofCut β m height a)
    (hEnd : IsProperRoofCut β m height (a + r)) :
    localDepth height a r = criticalDepth β r ↔
      roofCarry β a r = 1 := by
  have hMono :=
    A.height_le_add a r (Nat.le_of_lt hEnd.2.1)
  have hEndLe := A.1 (a + r) hEnd.2.1
  have hExact :=
    U.localDepth_add_roofSlack_eq_blockRoof_add_carry
      hMono hStart.2.2 hEndLe
  have hSlackZero : roofSlack β height (a + r) = 0 :=
    (roofSlack_eq_zero_iff_of_le hEndLe).2 hEnd.2.2
  rw [hSlackZero, Nat.add_zero] at hExact
  unfold criticalDepth
  constructor <;> intro h <;> omega

/-- 一 block の generic local critical geometry。 -/
def IsLocalRoofCriticalBlock
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a r : ℕ) : Prop :=
  0 < r ∧
    a + r ≤ m ∧
    localDepth height a r = criticalDepth β r ∧
    ∀ j : ℕ,
      0 < j →
      j < r →
      localDepth height a j ≤ β j

/--
roof cut で区切られ、最後だけ terminal `m` に着地する有限 block chain。

record rank や Ferrers order は保存しない。
-/
def RoofBlockChainFrom
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      0 < r ∧ a + r = m
  | a, r :: s :: rs =>
      0 < r ∧
        IsProperRoofCut β m height (a + r) ∧
        RoofBlockChainFrom β m height (a + r) (s :: rs)

/-- interior boundary carry がすべて `1`。terminal carry は含めない。 -/
def InteriorCarryOneFrom
    (β : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => False
  | _a, [_r] => True
  | a, r :: s :: rs =>
      roofCarry β a r = 1 ∧
        InteriorCarryOneFrom β (a + r) (s :: rs)

/-- 最後の block だけ terminal carry `0` を要求する predicate。 -/
def TerminalCarryZeroFrom
    (β : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] => roofCarry β a r = 0
  | a, r :: s :: rs =>
      TerminalCarryZeroFrom β (a + r) (s :: rs)

/--
contextual carry compatibility。

interior carry `1` は外部の record/skeleton geometry から供給されるものとして保存せず、
各 block の premature return 排除と最後の carry `0` だけを持つ。
-/
def ContextualCarryCompatibleFrom
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      NoPrematureCarryOneRoofReturn β m height a r ∧
        roofCarry β a r = 0
  | a, r :: s :: rs =>
      NoPrematureCarryOneRoofReturn β m height a r ∧
        ContextualCarryCompatibleFrom β m height (a + r) (s :: rs)

/-- interior carry `1` も明示した完全 carry compatibility。 -/
def FullCarryCompatibleFrom
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      NoPrematureCarryOneRoofReturn β m height a r ∧
        roofCarry β a r = 0
  | a, r :: s :: rs =>
      NoPrematureCarryOneRoofReturn β m height a r ∧
        roofCarry β a r = 1 ∧
        FullCarryCompatibleFrom β m height (a + r) (s :: rs)

/-- 全 block が generic local critical geometry を満たすこと。 -/
def LocalRoofCriticalBlocksFrom
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => True
  | a, r :: rs =>
      IsLocalRoofCriticalBlock β m height a r ∧
        LocalRoofCriticalBlocksFrom β m height (a + r) rs

/--
roof block chain 上では完全 carry compatibility と全 local criticality が exact に同値。

これが `Critical.RecordCarryExact` へ specialization できる generic chain law の中心定理。
-/
theorem fullCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsProperRoofCut β m height a →
      RoofBlockChainFrom β m height a rs →
      (FullCarryCompatibleFrom β m height a rs ↔
        LocalRoofCriticalBlocksFrom β m height a rs)
  | _a, [], _hStart, hFalse => False.elim hFalse
  | a, [r], hStart, hOne => by
      simp only [FullCarryCompatibleFrom, LocalRoofCriticalBlocksFrom]
      have hEnd : a + r ≤ m := Nat.le_of_eq hOne.2
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          U A hStart hEnd
      have hTerminalIff :=
        terminalMinimal_iff_carryZero U A hStart hOne.2
      constructor
      · intro C
        refine ⟨?_, by trivial⟩
        refine ⟨hOne.1, hEnd, hTerminalIff.2 C.2, ?_⟩
        exact hPrefixIff.2 C.1
      · intro L
        have B := L.1
        refine ⟨?_, ?_⟩
        · exact hPrefixIff.1 B.2.2.2
        · exact hTerminalIff.1 B.2.2.1
  | a, r :: s :: rs, hStart, hMany => by
      simp only [FullCarryCompatibleFrom, LocalRoofCriticalBlocksFrom]
      have hEndRoof : IsProperRoofCut β m height (a + r) := hMany.2.1
      have hEnd : a + r ≤ m := Nat.le_of_lt hEndRoof.2.1
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          U A hStart hEnd
      have hTailIff :=
        fullCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
          U A (a + r) (s :: rs) hEndRoof hMany.2.2
      constructor
      · intro C
        have hMinimal :=
          (interiorMinimal_iff_carryOne U A hStart hEndRoof).2 C.2.1
        refine ⟨?_, hTailIff.1 C.2.2⟩
        refine ⟨hMany.1, hEnd, hMinimal, ?_⟩
        exact hPrefixIff.2 C.1
      · intro L
        have hCarryOne :=
          (interiorMinimal_iff_carryOne U A hStart hEndRoof).1 L.1.2.2.1
        refine ⟨?_, hCarryOne, ?_⟩
        · exact hPrefixIff.1 L.1.2.2.2
        · exact hTailIff.2 L.2

/--
外部 context が interior carry `1` を保証するなら、contextual compatibility だけで
全 local criticalityを特徴付けられる。
-/
theorem contextualCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsProperRoofCut β m height a →
      RoofBlockChainFrom β m height a rs →
      InteriorCarryOneFrom β a rs →
      (ContextualCarryCompatibleFrom β m height a rs ↔
        LocalRoofCriticalBlocksFrom β m height a rs)
  | _a, [], _hStart, hFalse, _hInterior => False.elim hFalse
  | a, [r], hStart, hOne, _hInterior => by
      simpa [ContextualCarryCompatibleFrom, FullCarryCompatibleFrom] using
        (fullCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
          U A a [r] hStart hOne)
  | a, r :: s :: rs, hStart, hMany, hInterior => by
      simp only [
        ContextualCarryCompatibleFrom,
        LocalRoofCriticalBlocksFrom,
        InteriorCarryOneFrom
      ] at hInterior ⊢
      have hEndRoof : IsProperRoofCut β m height (a + r) := hMany.2.1
      have hEnd : a + r ≤ m := Nat.le_of_lt hEndRoof.2.1
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          U A hStart hEnd
      have hMinimal :=
        (interiorMinimal_iff_carryOne U A hStart hEndRoof).2 hInterior.1
      have hTailIff :=
        contextualCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
          U A (a + r) (s :: rs) hEndRoof hMany.2.2 hInterior.2
      constructor
      · intro C
        refine ⟨?_, hTailIff.1 C.2⟩
        refine ⟨hMany.1, hEnd, hMinimal, ?_⟩
        exact hPrefixIff.2 C.1
      · intro L
        refine ⟨?_, hTailIff.2 L.2⟩
        exact hPrefixIff.1 L.1.2.2.2

end Experimental2
end Collatz3
