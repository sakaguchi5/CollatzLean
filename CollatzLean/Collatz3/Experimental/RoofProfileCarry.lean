import CollatzLean.Collatz3.Experimental.UnitCarryRoof

/-!
# Collatz3 experimental: generic roof / profile / carry geometry

`Critical.Profile` と `Critical.RecordCarryExact` に現れる局所構造のうち、
`beattyIndex` 固有でない部分を abstract unit-carry roof `β` 上へ持ち上げる。

保存する primitive は

* unit-carry roof `β`,
* finite extra-depth profile,
* roof から profile height を引いた checkpoint の strictness

だけである。

そこから

* local depth,
* roof cut,
* proper-prefix failure,
* `carry = 1` と premature roof return の exact 同値,
* terminal minimality と terminal carry `0` の exact 同値,
* finite block chain に対する local criticality

を derived theorem として導く。

この層には `2`, `3`, `beattyIndex`, `RecordFerrers`, actual orbit は現れない。
-/

namespace Collatz3
namespace Experimental

/-- 幅 `m` の abstract roof profile。各 column は roof からの extra depth を持つ。 -/
abbrev RoofProfile (m : ℕ) := Fin m → ℕ

/-- profile column `k` の checkpoint。 -/
def roofCheckpoint
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m)
    (k : Fin m) : ℕ :=
  β k.1 - h k

/-- roof 以下かつ adjacent checkpoint が strict に増加するという最小 admissibility。 -/
def AdmissibleRoofProfile
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m) : Prop :=
  (∀ k : Fin m, h k ≤ β k.1) ∧
    (∀ k : ℕ, (hk : k + 1 < m) →
      roofCheckpoint β h ⟨k, by omega⟩ <
        roofCheckpoint β h ⟨k + 1, hk⟩)

/--
profile の global height path。

`k < m` では checkpoint、terminal `k = m` では `criticalDepth β m = β(m)+1` を使う。
このファイルでは `k ≤ m` の範囲しか利用しない。
-/
def roofProfileHeight
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m)
    (k : ℕ) : ℕ :=
  if hk : k < m then
    roofCheckpoint β h ⟨k, hk⟩
  else
    criticalDepth β m

/-- interior height は checkpoint そのもの。 -/
@[simp] theorem roofProfileHeight_of_lt
    {β : ℕ → ℕ}
    {m : ℕ}
    (h : RoofProfile m)
    {k : ℕ}
    (hk : k < m) :
    roofProfileHeight β h k =
      roofCheckpoint β h ⟨k, hk⟩ := by
  simp [roofProfileHeight, hk]

/-- terminal height は `β(m)+1`。 -/
@[simp] theorem roofProfileHeight_terminal
    {β : ℕ → ℕ}
    {m : ℕ}
    (h : RoofProfile m) :
    roofProfileHeight β h m = criticalDepth β m := by
  simp [roofProfileHeight]

namespace AdmissibleRoofProfile

/-- admissible profile は各 relevant column で roof 以下。 -/
theorem depth_le
    {β : ℕ → ℕ}
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    (k : Fin m) :
    h k ≤ β k.1 :=
  A.1 k

/-- adjacent interior checkpoint は strict。 -/
theorem checkpoint_strict
    {β : ℕ → ℕ}
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    {k : ℕ}
    (hk : k + 1 < m) :
    roofCheckpoint β h ⟨k, by omega⟩ <
      roofCheckpoint β h ⟨k + 1, hk⟩ :=
  A.2 k hk

/-- interior profile height は roof value 以下。 -/
theorem height_le_roof
    {β : ℕ → ℕ}
    {m : ℕ}
    {h : RoofProfile m}
    {k : ℕ}
    (hk : k < m) :
    roofProfileHeight β h k ≤ β k := by
  rw [roofProfileHeight_of_lt h hk]
  unfold roofCheckpoint
  exact Nat.sub_le _ _

end AdmissibleRoofProfile
open AdmissibleRoofProfile
/-- unit-carry roof は一 step で weak monotone。 -/
theorem roof_le_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (k : ℕ) :
    β k ≤ β (k + 1) := by
  have h := (U k 1).1
  omega

/--
admissible profile height は relevant range で一 step strict に増える。

interior では admissibility、最後の terminal step では `criticalDepth = β(m)+1` を使う。
-/
theorem roofProfileHeight_lt_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    {k : ℕ}
    (hk : k < m) :
    roofProfileHeight β h k < roofProfileHeight β h (k + 1) := by
  by_cases hNext : k + 1 < m
  · rw [roofProfileHeight_of_lt h hk]
    rw [roofProfileHeight_of_lt h hNext]
    exact A.checkpoint_strict hNext
  · have hEq : k + 1 = m := by omega
    have hHeightLe := height_le_roof (β := β) (h := h) hk
    have hRoofLe := roof_le_succ U k
    rw [hEq] at hRoofLe
    rw [hEq, roofProfileHeight_terminal]
    unfold criticalDepth
    omega

/-- start から `j` 進んだ local depth。 -/
def roofLocalDepth
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m)
    (a j : ℕ) : ℕ :=
  roofProfileHeight β h (a + j) - roofProfileHeight β h a

@[simp] theorem roofLocalDepth_zero
    {β : ℕ → ℕ}
    {m : ℕ}
    (h : RoofProfile m)
    (a : ℕ) :
    roofLocalDepth β h a 0 = 0 := by
  simp [roofLocalDepth]

/-- admissible profile height は `a` から `a+j` まで weak monotone。 -/
theorem roofProfileHeight_le_add
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h) :
    ∀ (a j : ℕ),
      a + j ≤ m →
      roofProfileHeight β h a ≤ roofProfileHeight β h (a + j)
  | a, 0, _hEnd => by
      simp
  | a, Nat.succ j, hEnd => by
      have hPrev : a + j ≤ m := by omega
      have hStepIndex : a + j < m := by omega
      have hIH := roofProfileHeight_le_add U A a j hPrev
      have hStep := roofProfileHeight_lt_succ U A hStepIndex
      have hStep' :
          roofProfileHeight β h (a + j) <
            roofProfileHeight β h (a + Nat.succ j) := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hStep
      exact le_trans hIH (Nat.le_of_lt hStep')

/-- local depth を start height と足すと global height に戻る。 -/
theorem roofProfileHeight_add_localDepth
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    {a j : ℕ}
    (hEnd : a + j ≤ m) :
    roofProfileHeight β h a + roofLocalDepth β h a j =
      roofProfileHeight β h (a + j) := by
  have hMono := roofProfileHeight_le_add U A a j hEnd
  have hSub := Nat.sub_add_cancel hMono
  simpa [roofLocalDepth, Nat.add_comm] using hSub

/-- interior pointが global roof に exact に乗ること。 -/
def IsRoofCutAt
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m)
    (a : ℕ) : Prop :=
  0 < a ∧
    a < m ∧
    roofProfileHeight β h a = β a

namespace IsRoofCutAt

/-- roof cut は正位置。 -/
theorem pos
    {β : ℕ → ℕ}
    {m : ℕ}
    {h : RoofProfile m}
    {a : ℕ}
    (R : IsRoofCutAt β h a) :
    0 < a := R.1

/-- roof cut は terminal より手前。 -/
theorem lt_width
    {β : ℕ → ℕ}
    {m : ℕ}
    {h : RoofProfile m}
    {a : ℕ}
    (R : IsRoofCutAt β h a) :
    a < m := R.2.1

/-- roof cut の height equation。 -/
theorem height_eq
    {β : ℕ → ℕ}
    {m : ℕ}
    {h : RoofProfile m}
    {a : ℕ}
    (R : IsRoofCutAt β h a) :
    roofProfileHeight β h a = β a := R.2.2

end IsRoofCutAt

/-- proper local positionで禁止すべき exact event。 -/
def NoPrematureCarryOneRoofReturn
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m)
    (a r : ℕ) : Prop :=
  ∀ j : ℕ,
    0 < j →
    j < r →
    ¬ (IsRoofCutAt β h (a + j) ∧ roofCarry β a j = 1)

/--
local prefix が roof `β(j)` を破ることと、
`premature roof return + carry 1` は exact に同値。
-/
theorem localPrefixFailure_iff_prematureCarryOneRoofReturn
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    {a j : ℕ}
    (hStartRoof : IsRoofCutAt β h a)
    (hjPos : 0 < j)
    (hEndLt : a + j < m) :
    β j < roofLocalDepth β h a j ↔
      IsRoofCutAt β h (a + j) ∧ roofCarry β a j = 1 := by
  have hDepthAdd :=
    roofProfileHeight_add_localDepth U A (Nat.le_of_lt hEndLt)
  have hStart := hStartRoof.height_eq
  have hEndLe := height_le_roof (β := β) (h := h) hEndLt
  have hCarry := U.add_eq a j
  have hCarryLe := U.carry_le_one a j
  constructor
  · intro hFail
    have hOne : roofCarry β a j = 1 := by
      rw [hStart] at hDepthAdd
      omega
    have hEndEq :
        roofProfileHeight β h (a + j) = β (a + j) := by
      rw [hStart] at hDepthAdd
      rw [hOne] at hCarry
      omega
    refine ⟨?_, hOne⟩
    exact ⟨by omega, hEndLt, hEndEq⟩
  · rintro ⟨hEndRoof, hOne⟩
    have hEndEq := hEndRoof.height_eq
    rw [hStart] at hDepthAdd
    rw [hOne] at hCarry
    omega

/--
proper-prefix roof bound と premature carry-1 roof return 排除は exact に同値。
-/
theorem localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    {a r : ℕ}
    (hStartRoof : IsRoofCutAt β h a)
    (hEnd : a + r ≤ m) :
    (∀ j : ℕ,
      0 < j →
      j < r →
      roofLocalDepth β h a j ≤ β j) ↔
      NoPrematureCarryOneRoofReturn β h a r := by
  constructor
  · intro hBound j hjPos hjLt hBad
    have hEndLt : a + j < m := by omega
    have hFail :=
      (localPrefixFailure_iff_prematureCarryOneRoofReturn
        U A hStartRoof hjPos hEndLt).2 hBad
    exact (Nat.not_lt_of_ge (hBound j hjPos hjLt)) hFail
  · intro hNo j hjPos hjLt
    by_contra hNot
    have hFail : β j < roofLocalDepth β h a j := by omega
    have hEndLt : a + j < m := by omega
    have hBad :=
      (localPrefixFailure_iff_prematureCarryOneRoofReturn
        U A hStartRoof hjPos hEndLt).1 hFail
    exact hNo j hjPos hjLt hBad

/--
interior roof-to-roof block では minimal local depth と carry `1` が exact に同値。
-/
theorem interiorMinimal_iff_carry_eq_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    {a r : ℕ}
    (hStartRoof : IsRoofCutAt β h a)
    (hEndRoof : IsRoofCutAt β h (a + r)) :
    roofLocalDepth β h a r = criticalDepth β r ↔
      roofCarry β a r = 1 := by
  have hEndLe : a + r ≤ m := Nat.le_of_lt hEndRoof.lt_width
  have hDepthAdd := roofProfileHeight_add_localDepth U A hEndLe
  have hStart := hStartRoof.height_eq
  have hEnd := hEndRoof.height_eq
  have hCarry := U.add_eq a r
  rw [hStart, hEnd] at hDepthAdd
  unfold criticalDepth
  constructor <;> intro h <;> omega

/--
terminal block では minimal terminal depth と terminal carry `0` が exact に同値。

terminal global height が `β(m)+1` であるため、interior block と carry の向きが反転する。
-/
theorem terminalMinimal_iff_carry_eq_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h)
    {a r : ℕ}
    (hStartRoof : IsRoofCutAt β h a)
    (hTerminal : a + r = m) :
    roofLocalDepth β h a r = criticalDepth β r ↔
      roofCarry β a r = 0 := by
  have hDepthAdd :=
    roofProfileHeight_add_localDepth U A (Nat.le_of_eq hTerminal)
  have hStart := hStartRoof.height_eq
  have hTerminalHeight :
      roofProfileHeight β h (a + r) = criticalDepth β m := by
    rw [hTerminal]
    exact roofProfileHeight_terminal h
  have hCarry := U.add_eq a r
  rw [hStart, hTerminalHeight] at hDepthAdd
  rw [hTerminal] at hCarry
  unfold criticalDepth at hDepthAdd ⊢
  constructor <;> intro h <;> omega

/-- 一 block の generic local critical geometry。 -/
def IsLocalRoofCriticalBlock
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m)
    (a r : ℕ) : Prop :=
  0 < r ∧
    a + r ≤ m ∧
    roofLocalDepth β h a r = criticalDepth β r ∧
    ∀ j : ℕ,
      0 < j →
      j < r →
      roofLocalDepth β h a j ≤ β j

/--
roof cut で区切られ、最後だけ terminal に着地する finite block chain。
record rank のような追加構造は保存しない。
-/
def RoofBlockChainFrom
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      0 < r ∧ a + r = m
  | a, r :: s :: rs =>
      0 < r ∧
        IsRoofCutAt β h (a + r) ∧
        RoofBlockChainFrom β h (a + r) (s :: rs)

/-- interior boundary carry がすべて `1` であること。terminal carry はここに含めない。 -/
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
current RecordCarryExact と同じ「contextual」carry compatibility。
interior carry `1` は外部の record/skeleton geometry から与えるため、ここには保存しない。
-/
def ContextualCarryCompatibleFrom
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      NoPrematureCarryOneRoofReturn β h a r ∧
        roofCarry β a r = 0
  | a, r :: s :: rs =>
      NoPrematureCarryOneRoofReturn β h a r ∧
        ContextualCarryCompatibleFrom β h (a + r) (s :: rs)

/-- interior carry `1` も明示した完全 carry compatibility。 -/
def FullCarryCompatibleFrom
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      NoPrematureCarryOneRoofReturn β h a r ∧
        roofCarry β a r = 0
  | a, r :: s :: rs =>
      NoPrematureCarryOneRoofReturn β h a r ∧
        roofCarry β a r = 1 ∧
        FullCarryCompatibleFrom β h (a + r) (s :: rs)

/-- 全 block が generic local critical geometry を持つこと。 -/
def LocalRoofCriticalBlocksFrom
    (β : ℕ → ℕ)
    {m : ℕ}
    (h : RoofProfile m) : ℕ → List ℕ → Prop
  | _a, [] => True
  | a, r :: rs =>
      IsLocalRoofCriticalBlock β h a r ∧
        LocalRoofCriticalBlocksFrom β h (a + r) rs

/--
roof block chain 上では完全 carry compatibility と全 local criticality が exact に同値。

これは `Critical.RecordCarryExact` の Collatz 非依存核に対応する。
-/
theorem fullCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsRoofCutAt β h a →
      RoofBlockChainFrom β h a rs →
      (FullCarryCompatibleFrom β h a rs ↔
        LocalRoofCriticalBlocksFrom β h a rs)
  | _a, [], _hRoof, hFalse => False.elim hFalse
  | a, [r], hRoof, hOne => by
      simp only [FullCarryCompatibleFrom, LocalRoofCriticalBlocksFrom]
      have hEnd : a + r ≤ m := Nat.le_of_eq hOne.2
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          U A hRoof hEnd
      have hTerminalIff :=
        terminalMinimal_iff_carry_eq_zero U A hRoof hOne.2
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
  | a, r :: s :: rs, hRoof, hMany => by
      simp only [FullCarryCompatibleFrom, LocalRoofCriticalBlocksFrom]
      have hEndRoof : IsRoofCutAt β h (a + r) := hMany.2.1
      have hEnd : a + r ≤ m := Nat.le_of_lt hEndRoof.lt_width
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          U A hRoof hEnd
      have hTailIff :=
        fullCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
          U A (a + r) (s :: rs) hEndRoof hMany.2.2
      constructor
      · intro C
        have hMinimal :=
          (interiorMinimal_iff_carry_eq_one U A hRoof hEndRoof).2 C.2.1
        refine ⟨?_, hTailIff.1 C.2.2⟩
        refine ⟨hMany.1, hEnd, hMinimal, ?_⟩
        exact hPrefixIff.2 C.1
      · intro L
        have hCarryOne :=
          (interiorMinimal_iff_carry_eq_one U A hRoof hEndRoof).1 L.1.2.2.1
        refine ⟨?_, hCarryOne, ?_⟩
        · exact hPrefixIff.1 L.1.2.2.2
        · exact hTailIff.2 L.2

/--
外部 context が interior carry `1` を保証する場合、current Record 型の contextual compatibility
だけで全 local criticalityを特徴付けられる。
-/
theorem contextualCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m : ℕ}
    {h : RoofProfile m}
    (A : AdmissibleRoofProfile β h) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsRoofCutAt β h a →
      RoofBlockChainFrom β h a rs →
      InteriorCarryOneFrom β a rs →
      (ContextualCarryCompatibleFrom β h a rs ↔
        LocalRoofCriticalBlocksFrom β h a rs)
  | _a, [], _hRoof, hFalse, _hInterior => False.elim hFalse
  | a, [r], hRoof, hOne, _hInterior => by
      simpa [ContextualCarryCompatibleFrom, FullCarryCompatibleFrom] using
        (fullCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
          U A a [r] hRoof hOne)
  | a, r :: s :: rs, hRoof, hMany, hInterior => by
      simp only [
        ContextualCarryCompatibleFrom,
        LocalRoofCriticalBlocksFrom,
        InteriorCarryOneFrom
      ] at hInterior ⊢
      have hEndRoof : IsRoofCutAt β h (a + r) := hMany.2.1
      have hEnd : a + r ≤ m := Nat.le_of_lt hEndRoof.lt_width
      have hPrefixIff :=
        localProperPrefixBound_iff_noPrematureCarryOneRoofReturn
          U A hRoof hEnd
      have hMinimal :=
        (interiorMinimal_iff_carry_eq_one U A hRoof hEndRoof).2 hInterior.1
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

end Experimental
end Collatz3
