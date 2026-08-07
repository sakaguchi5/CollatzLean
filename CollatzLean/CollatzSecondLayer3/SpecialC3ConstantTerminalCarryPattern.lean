import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalNested
import CollatzLean.CollatzSupport.CofinalSelection

/-!
# Constant terminalのfinite carry pattern固定

Constant terminal枝ではterminal time `T`が固定される。
各selected windowの時刻`0,...,T-1`はcaptureまたはsynchronizedなので、
有限型のcarry patternを一つ持つ。
有限型値列にはcofinal定数部分列が存在するため、さらに部分列を取り、
全時刻のcapture/sync patternを完全に固定する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer

namespace FutureMinimumSpecialC3TowerData
namespace ConstantTerminalNestedAlignmentData

/-- Constant terminal以前の一時刻のcarry種別。 -/
inductive ConstantTerminalCarryKind where
  | captured
  | synchronized
  deriving DecidableEq, Fintype

/-- 上に有界な自然数列では一つの値がcofinalに現れる。 -/
theorem cofinally_constant_of_bounded_nat_sequence :
    ∀ B : ℕ,
      ∀ a : ℕ → ℕ,
        (∀ n : ℕ, a n ≤ B) →
        ∃ v : ℕ, Cofinally (fun n => a n = v) := by
  intro B
  induction B with
  | zero =>
      intro a hBound
      refine ⟨0, ?_⟩
      intro N
      refine ⟨N, le_rfl, ?_⟩
      have h := hBound N
      omega
  | succ B ih =>
      intro a hBound
      by_cases hTop : Cofinally (fun n => a n = B + 1)
      · exact ⟨B + 1, hTop⟩
      · obtain ⟨Ntop, hNtop⟩ :=
          Cofinally.eventually_not_of_not
            (fun n => a n = B + 1) hTop
        have hLower : ∀ n : ℕ, Ntop ≤ n → a n ≤ B := by
          intro n hn
          have hle := hBound n
          have hne := hNtop n hn
          omega
        let shifted : ℕ → ℕ := fun n => a (Ntop + n)
        have hShiftBound : ∀ n : ℕ, shifted n ≤ B := by
          intro n
          exact hLower (Ntop + n) (by omega)
        obtain ⟨v, hv⟩ := ih shifted hShiftBound
        refine ⟨v, ?_⟩
        intro N
        obtain ⟨n, hn, heq⟩ := hv N
        refine ⟨Ntop + n, ?_, ?_⟩
        · omega
        · simpa [shifted] using heq

/-- 任意の有限型値列にはcofinal定数部分列が存在する。 -/
theorem cofinally_constant_of_fintype
    {α : Type*}
    [Fintype α]
    (a : ℕ → α) :
    ∃ x : α, Cofinally (fun n => a n = x) := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let code : ℕ → ℕ := fun n => (e (a n)).val
  have hBound : ∀ n : ℕ, code n ≤ Fintype.card α := by
    intro n
    exact Nat.le_of_lt (e (a n)).isLt
  obtain ⟨v, hv⟩ :=
    cofinally_constant_of_bounded_nat_sequence
      (Fintype.card α) code hBound
  obtain ⟨n₀, _hn₀, hv₀⟩ := hv 0
  have hvlt : v < Fintype.card α := by
    have hlt := (e (a n₀)).isLt
    have hvEq : (e (a n₀)).val = v := by
      simpa [code] using hv₀
    rw [hvEq] at hlt
    exact hlt
  let x : α := e.symm ⟨v, hvlt⟩
  refine ⟨x, ?_⟩
  intro N
  obtain ⟨n, hn, hcode⟩ := hv N
  refine ⟨n, hn, ?_⟩
  apply e.injective
  change e (a n) = e x
  rw [show e x = (⟨v, hvlt⟩ : Fin (Fintype.card α)) by
    simp [x]]
  apply Fin.ext
  have hvEq : (e (a n)).val = v := by
    simpa [code] using hcode
  exact hvEq

/-- n番目のwindowの固定terminal以前の時刻`t`におけるcarry種別。 -/
noncomputable def carryKind
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ)
    (t : Fin D.terminal.value) : ConstantTerminalCarryKind := by
  classical
  by_cases hCaptured :
      Nonempty
        (O.CapturedWindowAt
          (R.anchor + t.1)
          (D.selectedLength n))
  · exact .captured
  · exact .synchronized

/-- `carryKind`が表す実際のcapture/synchronized certificate。 -/
theorem carryKind_certificate
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ)
    (t : Fin D.terminal.value) :
    match D.carryKind n t with
    | .captured =>
        Nonempty
          (O.CapturedWindowAt
            (R.anchor + t.1)
            (D.selectedLength n))
    | .synchronized =>
        Nonempty
          (O.SynchronizedWindowAt
            (R.anchor + t.1)
            (D.selectedLength n)) := by
  classical
  by_cases hCaptured :
      Nonempty
        (O.CapturedWindowAt
          (R.anchor + t.1)
          (D.selectedLength n))
  · simpa [carryKind, hCaptured] using hCaptured
  · have ht :
        t.1 < R.terminalTime (D.selectedIndex n) := by
      change t.1 < R.terminalTime (D.terminal.select n)
      rw [D.terminal.value_eq n]
      exact t.2
    have hBefore :=
      (R.normalization (D.selectedIndex n)).before t.1 (by
        simpa [FutureMinimumSpecialC3TowerData.terminalTime] using ht)
    rcases hBefore with ⟨C | S⟩
    · exact False.elim (hCaptured ⟨by
        simpa [selectedIndex, selectedLength,
          FutureMinimumSpecialC3TowerData.length,
          Nat.add_assoc] using C⟩)
    · have hSync :
          Nonempty
            (O.SynchronizedWindowAt
              (R.anchor + t.1)
              (D.selectedLength n)) := by
        exact ⟨by
          simpa [selectedIndex, selectedLength,
            FutureMinimumSpecialC3TowerData.length,
            Nat.add_assoc] using S⟩
      simpa [carryKind, hCaptured] using hSync

/-- n番目のwindowのterminal以前carry pattern全体。 -/
noncomputable def carryPattern
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Fin D.terminal.value → ConstantTerminalCarryKind :=
  fun t => D.carryKind n t

/-- carry patternを固定した無限部分列。 -/
structure ConstantTerminalFixedCarryPatternData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  pattern : Fin D.terminal.value → ConstantTerminalCarryKind
  pattern_eq : ∀ n : ℕ, D.carryPattern (select n) = pattern

/-- 有限carry patternのどれかはcofinalに現れる。 -/
theorem fixedCarryPatternSubsequence_nonempty
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) :
    Nonempty (ConstantTerminalFixedCarryPatternData D) := by
  classical
  obtain ⟨P, hP⟩ :=
    cofinally_constant_of_fintype D.carryPattern
  let select : ℕ → ℕ :=
    Cofinally.select (fun n => D.carryPattern n = P) hP
  exact ⟨{
    select := select
    select_strict :=
      Cofinally.select_strict (fun n => D.carryPattern n = P) hP
    pattern := P
    pattern_eq := fun n =>
      Cofinally.select_spec (fun n => D.carryPattern n = P) hP n
  }⟩

namespace ConstantTerminalFixedCarryPatternData

/-- pattern固定後の部分列も再びConstant nested dataとして扱える。 -/
def nested
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    (F : ConstantTerminalFixedCarryPatternData D) :
    ConstantTerminalNestedAlignmentData R :=
  D.refine F.select F.select_strict

/-- 固定patternの各時刻で、各selected windowは同じ種別のcertificateを持つ。 -/
theorem pattern_certificate
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    (F : ConstantTerminalFixedCarryPatternData D)
    (n : ℕ)
    (t : Fin D.terminal.value) :
    match F.pattern t with
    | .captured =>
        Nonempty
          (O.CapturedWindowAt
            (R.anchor + t.1)
            (D.selectedLength (F.select n)))
    | .synchronized =>
        Nonempty
          (O.SynchronizedWindowAt
            (R.anchor + t.1)
            (D.selectedLength (F.select n))) := by
  have hEq := congrFun (F.pattern_eq n) t
  have hCert := D.carryKind_certificate (F.select n) t
  change
    match F.pattern t with
    | .captured =>
        Nonempty
          (O.CapturedWindowAt
            (R.anchor + t.1)
            (D.selectedLength (F.select n)))
    | .synchronized =>
        Nonempty
          (O.SynchronizedWindowAt
            (R.anchor + t.1)
            (D.selectedLength (F.select n)))
  rw [← hEq]
  simpa [carryPattern] using hCert

end ConstantTerminalFixedCarryPatternData
end ConstantTerminalNestedAlignmentData
end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
