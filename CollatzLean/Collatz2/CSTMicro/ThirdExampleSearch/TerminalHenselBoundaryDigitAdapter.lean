import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalBoundaryLiftSurvival
import Mathlib.Tactic.FinCases

/-!
# 第3例探索 次段 1: 実 Hensel 3-lift と criticalization boundary digit の exact adapter

前段では、

* backward Hensel の 3 個の候補を `Fin 3`、
* criticalization boundary が要求する次の 3 進 digit を `ZMod 3`

として別々に扱っていた。

このファイルでは `Fin 3` の候補番号 `0,1,2` を、そのまま対応する
`ZMod 3` digit `0,1,2` へ送る exact equivalence を作る。
その結果、boundary filter を通る Hensel 3-lift 候補は exact に一つになる。

ここでいう survivor は、前段 `terminalBoundaryLiftSurvives` と同じく
criticalization boundary condition を通過する候補を意味する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/-- Hensel 3-lift の候補番号 `0,1,2` を対応する 3 進 digit へ送る。 -/
def henselThreeLiftDigit
    (a : Fin 3) : ZMod 3 :=
  (a.val : ZMod 3)

/-- `ZMod 3` digit を canonical な `Fin 3` 候補番号へ戻す。 -/
def henselThreeLiftIndexOfDigit
    (d : ZMod 3) : Fin 3 :=
  ⟨d.val, ZMod.val_lt d⟩

/-- `ZMod 3 -> Fin 3 -> ZMod 3` は恒等。 -/
@[simp] theorem henselThreeLiftDigit_indexOfDigit
    (d : ZMod 3) :
    henselThreeLiftDigit (henselThreeLiftIndexOfDigit d) = d := by
  unfold henselThreeLiftDigit henselThreeLiftIndexOfDigit
  exact ZMod.natCast_zmod_val d

/-- `Fin 3 -> ZMod 3 -> Fin 3` も恒等。 -/
@[simp] theorem henselThreeLiftIndexOfDigit_digit
    (a : Fin 3) :
    henselThreeLiftIndexOfDigit (henselThreeLiftDigit a) = a := by
  apply Fin.ext
  simp [henselThreeLiftIndexOfDigit, henselThreeLiftDigit,
    ZMod.val_cast_of_lt a.isLt]

/-- Hensel 3-lift の候補番号と 3 進 digit の exact equivalence。 -/
def henselThreeLiftDigitEquiv :
    Fin 3 ≃ ZMod 3 where
  toFun := henselThreeLiftDigit
  invFun := henselThreeLiftIndexOfDigit
  left_inv := henselThreeLiftIndexOfDigit_digit
  right_inv := henselThreeLiftDigit_indexOfDigit

/-- 3-lift 候補が boundary filter を通るとは、その候補の digit が boundary digit と一致すること。 -/
def terminalHenselBoundarySurvives
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (a : Fin 3) : Prop :=
  terminalBoundaryLiftSurvives P hStart (henselThreeLiftDigit a)

/-- Hensel 3-lift の boundary survivor 条件は判定可能。 -/
noncomputable instance terminalHenselBoundarySurvives_decidable
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    DecidablePred (terminalHenselBoundarySurvives P hStart) := by
  classical
  intro a
  unfold terminalHenselBoundarySurvives
  infer_instance

/--
実 Hensel 3-lift 候補の survival 条件を、既存 boundary digit 条件へ exact に輸送する。
-/
theorem terminalHenselBoundarySurvives_iff_digit
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (a : Fin 3) :
    terminalHenselBoundarySurvives P hStart a ↔
      henselThreeLiftDigit a =
        MultiCorner.criticalizationBoundaryDigit P hStart := by
  rfl

/--
left cut `a` の normalized terminal tail を使えば、survive する実 3-lift 候補の digit を
直接読める。
-/
theorem terminalHenselBoundarySurvives_iff_normalizedTerminalTail
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {cut : ℕ}
    (hcut : cut < P.criticalizationStart)
    (a : Fin 3) :
    terminalHenselBoundarySurvives P hStart a ↔
      henselThreeLiftDigit a =
        ((- (2 : ℤ) ^ beattyIndex cut *
            P.criticalizationNormalizedTerminalTail
              cut (Nat.le_of_lt hcut) : ℤ) : ZMod 3) := by
  unfold terminalHenselBoundarySurvives
  exact
    terminalBoundaryLiftSurvives_iff_normalizedTerminalTail
      P hStart hcut (henselThreeLiftDigit a)

/-- boundary digit が指定する canonical Hensel 3-lift 候補。 -/
def terminalHenselBoundaryCandidate
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) : Fin 3 :=
  henselThreeLiftIndexOfDigit
    (MultiCorner.criticalizationBoundaryDigit P hStart)


/-- canonical candidate は必ず boundary filter を通る。 -/
theorem terminalHenselBoundaryCandidate_survives
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    terminalHenselBoundarySurvives P hStart
      (terminalHenselBoundaryCandidate P hStart) := by
  unfold terminalHenselBoundarySurvives terminalHenselBoundaryCandidate
  rw [henselThreeLiftDigit_indexOfDigit]
  rfl

/--
boundary filter を通る Hensel 3-lift 候補は canonical candidate に必ず一致する。
従って 3 分岐は exact に 1 分岐へ潰れる。
-/
theorem terminalHenselBoundarySurvivor_eq_candidate
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : Fin 3}
    (ha : terminalHenselBoundarySurvives P hStart a) :
    a = terminalHenselBoundaryCandidate P hStart := by
  unfold terminalHenselBoundarySurvives at ha
  apply henselThreeLiftDigitEquiv.injective
  change
    henselThreeLiftDigit a =
      henselThreeLiftDigit
        (henselThreeLiftIndexOfDigit
          (MultiCorner.criticalizationBoundaryDigit P hStart))
  rw [henselThreeLiftDigit_indexOfDigit]
  exact ha
/--
実 Hensel 3-lift 候補のうち boundary filter を通るものは exact に一つ存在する。
-/
theorem terminalHenselBoundarySurvivor_existsUnique
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ∃! a : Fin 3,
      terminalHenselBoundarySurvives P hStart a := by
  refine ⟨terminalHenselBoundaryCandidate P hStart,
    terminalHenselBoundaryCandidate_survives P hStart, ?_⟩
  intro a ha
  exact terminalHenselBoundarySurvivor_eq_candidate P hStart ha

/--
有限集合として数えても survivor は exact に 1 個。
探索器では 3 個すべてを枝として保持する必要がない。
-/
theorem terminalHenselBoundarySurvivor_card_eq_one
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (Finset.univ.filter
      (terminalHenselBoundarySurvives P hStart)).card = 1 := by
  classical
  let a0 := terminalHenselBoundaryCandidate P hStart
  have ha0 : terminalHenselBoundarySurvives P hStart a0 := by
    dsimp [a0]
    exact terminalHenselBoundaryCandidate_survives P hStart
  have hFilter :
      Finset.univ.filter (terminalHenselBoundarySurvives P hStart) =
        {a0} := by
    ext a
    constructor
    · intro ha
      have hSurv : terminalHenselBoundarySurvives P hStart a :=
        (Finset.mem_filter.mp ha).2
      have hEq : a = a0 := by
        dsimp [a0]
        exact terminalHenselBoundarySurvivor_eq_candidate P hStart hSurv
      simp [hEq]
    · intro ha
      have hEq : a = a0 := by simpa using ha
      subst a
      simp [ha0]
  rw [hFilter]
  simp

end ThirdExampleSearch
end CSTMicro
end Collatz2
