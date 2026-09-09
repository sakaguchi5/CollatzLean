import CollatzLean.Collatz3.Experimental.UnitCarryRoof


/-!
# Collatz3 experimental: 一般 roof path の exact carry 幾何

0/1-carry 屋根 `β` の下を進み、terminal だけ `β(m)+1` に着地する有限 height path を考える。

このファイルの目的は、現行 Collatz3 の Beatty 固有語彙を使わずに次の二本を再証明すること。

* local failure `<->` premature roof return + carry `1`
* terminal minimality `<->` terminal carry `0`

定義は実験に必要な最小限だけに留め、record cut / Ferrers / actual Collatz orbit は導入しない。
-/

namespace Collatz3
namespace Experimental

/--
幅 `m` の一般 critical roof path。

* proper cut `k<m` では屋根 `β(k)` 以下、
* proper step では height が strict に増加、
* terminal `m` では `criticalDepth β m = β(m)+1` に着地する。
-/
def IsAdmissibleRoofPath
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  (∀ k : ℕ, k < m → height k ≤ β k) ∧
    (∀ k : ℕ, k < m → height k < height (k + 1)) ∧
      height m = criticalDepth β m

/-- proper cut `a` が屋根に exact に乗ること。 -/
def IsRoofCut
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a : ℕ) : Prop :=
  0 < a ∧
    a < m ∧
      height a = β a

/-- start `a` から `j` 進んだ局所 height 増分。 -/
def localDepth
    (height : ℕ → ℕ)
    (a j : ℕ) : ℕ :=
  height (a + j) - height a

namespace IsAdmissibleRoofPath

/-- admissible path は有限範囲内で weak monotone。 -/
theorem height_le_add
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height)
    (a j : ℕ)
    (hEnd : a + j ≤ m) :
    height a ≤ height (a + j) := by
  revert hEnd
  induction j with
  | zero =>
      intro hEnd
      simp
  | succ j ih =>
      intro hEnd
      have hPrev : a + j ≤ m := by
        omega
      have hIH := ih hPrev
      have hStepIndex : a + j < m := by
        omega
      have hStep := A.2.1 (a + j) hStepIndex
      have hStep' :
          height (a + j) < height (a + (j + 1)) := by
        simpa [Nat.add_assoc] using hStep
      exact le_trans hIH (Nat.le_of_lt hStep')

/-- local depth を start height に足すと global height に exact に戻る。 -/
theorem height_add_localDepth
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height)
    {a j : ℕ}
    (hEnd : a + j ≤ m) :
    height a + localDepth height a j = height (a + j) := by
  have hMono := height_le_add A a j hEnd
  unfold localDepth
  omega

end IsAdmissibleRoofPath

/--
第三の基本実験: proper local prefix が屋根を破ることと、
途中の global roof return と carry `1` の同時発生は exact に同値。

屋根へ戻ること単独、carry `1` 単独は失敗条件ではない。
-/
theorem localFailure_iff_roofReturn_and_carryOne
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a j : ℕ}
    (hStartRoof : IsRoofCut β m height a)
    (hjPos : 0 < j)
    (hEndLt : a + j < m) :
    β j < localDepth height a j ↔
      IsRoofCut β m height (a + j) ∧
        roofCarry β a j = 1 := by
  have hDepthAdd :=
    IsAdmissibleRoofPath.height_add_localDepth A (Nat.le_of_lt hEndLt)
  have hStart := hStartRoof.2.2
  have hEndLe : height (a + j) ≤ β (a + j) :=
    A.1 (a + j) hEndLt
  have hCarry := HasUnitCarry.add_eq U a j
  have hCarryLe := HasUnitCarry.carry_le_one U a j
  constructor
  · intro hFail
    have hOne : roofCarry β a j = 1 := by
      rw [hStart] at hDepthAdd
      omega
    have hEndEq : height (a + j) = β (a + j) := by
      rw [hStart] at hDepthAdd
      rw [hOne] at hCarry
      omega
    refine ⟨?_, hOne⟩
    exact ⟨by omega, hEndLt, hEndEq⟩
  · rintro ⟨hEndRoof, hOne⟩
    have hEndEq := hEndRoof.2.2
    rw [hStart] at hDepthAdd
    rw [hOne] at hCarry
    omega

/--
第四の基本実験: terminal block の局所深さが最小 critical depth に一致することと、
terminal carry が `0` であることは exact に同値。
-/
theorem terminalMinimal_iff_carryZero
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ}
    (hStartRoof : IsRoofCut β m height a)
    (hTerminal : a + r = m) :
    localDepth height a r = criticalDepth β r ↔
      roofCarry β a r = 0 := by
  have hDepthAdd :=
    IsAdmissibleRoofPath.height_add_localDepth A (Nat.le_of_eq hTerminal)
  have hStart := hStartRoof.2.2
  have hTerminalHeight :
      height (a + r) = criticalDepth β m := by
    rw [hTerminal]
    exact A.2.2
  have hLocal :
      β a + localDepth height a r = criticalDepth β m := by
    rw [hStart, hTerminalHeight] at hDepthAdd
    exact hDepthAdd
  have hCarry := HasUnitCarry.add_eq U a r
  rw [hTerminal] at hCarry
  unfold criticalDepth at hLocal ⊢
  constructor
  · intro hMinimal
    omega
  · intro hZero
    omega

end Experimental
end Collatz3
