import CollatzLean.Collatz3.Experimental2.CarryCore

/-!
# Collatz3 Experimental2: roof path の局所 exact law

path 全体の admissibility と、局所算術に本当に必要な条件を分離する。

中心は

`localDepth + roofSlack = block roof + carry`

という保存式であり、local failure や terminal minimality はその corollary として導く。
-/

namespace Collatz3
namespace Experimental2

def IsRoofBoundedPath
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, k < m → height k ≤ β k

def IsStrictPath
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, k < m → height k < height (k + 1)

def HasCriticalTerminal
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  height m = criticalDepth β m

def IsAdmissibleRoofPath
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  IsRoofBoundedPath β m height ∧
    IsStrictPath m height ∧
      HasCriticalTerminal β m height

def IsOnRoof
    (β height : ℕ → ℕ)
    (a : ℕ) : Prop :=
  height a = β a

def IsProperRoofCut
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a : ℕ) : Prop :=
  0 < a ∧ a < m ∧ IsOnRoof β height a

def localDepth
    (height : ℕ → ℕ)
    (a j : ℕ) : ℕ :=
  height (a + j) - height a

def roofSlack
    (β height : ℕ → ℕ)
    (k : ℕ) : ℕ :=
  β k - height k

namespace IsAdmissibleRoofPath

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
      have hPrev : a + j ≤ m := by omega
      have hIH := ih hPrev
      have hStepIndex : a + j < m := by omega
      have hStep := A.2.1 (a + j) hStepIndex
      have hStep' : height (a + j) < height (a + (j + 1)) := by
        simpa [Nat.add_assoc] using hStep
      exact le_trans hIH (Nat.le_of_lt hStep')

end IsAdmissibleRoofPath

/-- roof bound の下で slack `0` と roof 上は同値。 -/
theorem roofSlack_eq_zero_iff_of_le
    {β height : ℕ → ℕ}
    {k : ℕ}
    (hLe : height k ≤ β k) :
    roofSlack β height k = 0 ↔ IsOnRoof β height k := by
  unfold roofSlack IsOnRoof
  omega

namespace HasUnitCarry

/--
局所保存式。

path 全体ではなく、start の roof equality・endpoint bound・局所 monotonicity だけを使う。
-/
theorem localDepth_add_roofSlack_eq_blockRoof_add_carry
    {β height : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a j : ℕ}
    (hMono : height a ≤ height (a + j))
    (hStart : IsOnRoof β height a)
    (hEndLe : height (a + j) ≤ β (a + j)) :
    localDepth height a j + roofSlack β height (a + j) =
      β j + roofCarry β a j := by
  have hCarry := U.add_eq a j
  unfold IsOnRoof at hStart
  unfold localDepth roofSlack
  rw [hStart]
  omega

/-- terminal endpoint が critical depth の場合の exact local depth。 -/
theorem terminalLocalDepth_eq_criticalDepth_add_carry
    {β height : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a r : ℕ}
    (hMono : height a ≤ height (a + r))
    (hStart : IsOnRoof β height a)
    (hTerminal :
      height (a + r) = criticalDepth β (a + r)) :
    localDepth height a r =
      criticalDepth β r + roofCarry β a r := by
  have hCarry := U.add_eq a r
  unfold IsOnRoof at hStart
  unfold criticalDepth at hTerminal ⊢
  unfold localDepth
  rw [hStart, hTerminal]
  omega

end HasUnitCarry

/-- admissible path 上の local failure exact law。 -/
theorem localFailure_iff_roofReturn_and_carryOne
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a j : ℕ}
    (hStart : IsProperRoofCut β m height a)
    (hEndLt : a + j < m) :
    β j < localDepth height a j ↔
      IsProperRoofCut β m height (a + j) ∧
        roofCarry β a j = 1 := by
  have hMono := A.height_le_add a j (Nat.le_of_lt hEndLt)
  have hEndLe := A.1 (a + j) hEndLt
  have hExact :=
    U.localDepth_add_roofSlack_eq_blockRoof_add_carry
      hMono hStart.2.2 hEndLe
  have hSlackIff := roofSlack_eq_zero_iff_of_le hEndLe
  have hCarryLe := U.carry_le_one a j
  constructor
  · intro hFail
    have hCarryOne : roofCarry β a j = 1 := by omega
    have hSlackZero : roofSlack β height (a + j) = 0 := by omega
    have hEndRoof := hSlackIff.mp hSlackZero
    have hPos : 0 < a + j := by
      exact lt_of_lt_of_le hStart.1 (Nat.le_add_right a j)
    exact ⟨⟨hPos, hEndLt, hEndRoof⟩, hCarryOne⟩
  · rintro ⟨hEndRoof, hCarryOne⟩
    have hSlackZero := hSlackIff.mpr hEndRoof.2.2
    omega

/-- admissible path の terminal minimality exact law。 -/
theorem terminalMinimal_iff_carryZero
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ}
    (hStart : IsProperRoofCut β m height a)
    (hTerminalIndex : a + r = m) :
    localDepth height a r = criticalDepth β r ↔
      roofCarry β a r = 0 := by
  have hMono := A.height_le_add a r (Nat.le_of_eq hTerminalIndex)
  have hTerminal :
      height (a + r) = criticalDepth β (a + r) := by
    rw [hTerminalIndex]
    exact A.2.2
  have hExact :=
    U.terminalLocalDepth_eq_criticalDepth_add_carry
      hMono hStart.2.2 hTerminal
  omega

end Experimental2
end Collatz3
