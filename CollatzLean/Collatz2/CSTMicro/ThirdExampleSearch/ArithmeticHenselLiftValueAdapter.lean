import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalHenselBoundaryDigitAdapter

/-!
# 第3例探索: arithmetic Hensel 3-lift の実値 adapter

前段では Hensel の三候補を `Fin 3` の label として持ち、
criticalization boundary が許す digit label が一意であることを証明した。

ここでは基礎 residue `q (mod 3^r)` の実際の三つの lift

  q,
  q + 3^r,
  q + 2 * 3^r

を `Fin 3` label から直接構成する。
これにより boundary digit の一意性を「実際の整数 lift 値の一意性」へ輸送する。

注意: boundary condition は三候補のうち「候補になり得る実値」を一意にする。
その実値がさらに backward Hensel recurrence を満たすかは別の算術条件であり、
recurrence を課した survivor は高々一つになる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
基礎 residue `q (mod 3^r)` の `a=0,1,2` 番目の actual Hensel lift 値。
-/
def arithmeticHenselThreeLiftValue
    (q r : ℕ)
    (a : Fin 3) : ℕ :=
  q + a.val * 3 ^ r

/-- actual lift は `q + digit * 3^r` そのもの。 -/
@[simp] theorem arithmeticHenselThreeLiftValue_eq
    (q r : ℕ)
    (a : Fin 3) :
    arithmeticHenselThreeLiftValue q r a =
      q + a.val * 3 ^ r := rfl

/-- actual lift から基礎 residue を引くと、新しく付けた digit 部分だけが残る。 -/
theorem arithmeticHenselThreeLiftValue_sub_base
    (q r : ℕ)
    (a : Fin 3) :
    arithmeticHenselThreeLiftValue q r a - q =
      a.val * 3 ^ r := by
  simp [arithmeticHenselThreeLiftValue]

/--
三つの actual lift はすべて元の residue `q` と `mod 3^r` で一致する。
-/
theorem arithmeticHenselThreeLiftValue_mod_basePow
    (q r : ℕ)
    (a : Fin 3) :
    arithmeticHenselThreeLiftValue q r a % (3 ^ r) =
      q % (3 ^ r) := by
  simp [arithmeticHenselThreeLiftValue, Nat.add_mod]

/--
`Fin 3` label の値を `ZMod 3` へ送ると、
Hensel 3-lift の digit と exact に一致する。
-/
theorem arithmeticHenselThreeLiftValue_labelDigit
    (a : Fin 3) :
    ((a.val : ℕ) : ZMod 3) = henselThreeLiftDigit a := by
  rfl

/--
actual integer lift が criticalization boundary filter を通ること。
値が三候補のどれかで、その label が既存 boundary condition を通ることを要求する。
-/
def arithmeticHenselBoundaryLiftSurvives
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r v : ℕ) : Prop :=
  ∃ a : Fin 3,
    v = arithmeticHenselThreeLiftValue q r a ∧
      terminalHenselBoundarySurvives P hStart a

/-- boundary digit が指定する canonical actual Hensel lift 値。 -/
def arithmeticHenselBoundaryCandidateValue
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r : ℕ) : ℕ :=
  arithmeticHenselThreeLiftValue q r
    (terminalHenselBoundaryCandidate P hStart)

/-- canonical actual value は必ず boundary filter を通る。 -/
theorem arithmeticHenselBoundaryCandidateValue_survives
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r : ℕ) :
    arithmeticHenselBoundaryLiftSurvives
      P hStart q r
      (arithmeticHenselBoundaryCandidateValue P hStart q r) := by
  refine ⟨terminalHenselBoundaryCandidate P hStart, rfl, ?_⟩
  exact terminalHenselBoundaryCandidate_survives P hStart

/--
boundary を通る actual Hensel lift 値は canonical value に必ず一致する。
従って label の一意性が、そのまま整数 lift 値の一意性になる。
-/
theorem arithmeticHenselBoundaryLiftSurvivor_eq_candidateValue
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r : ℕ)
    {v : ℕ}
    (hv : arithmeticHenselBoundaryLiftSurvives P hStart q r v) :
    v = arithmeticHenselBoundaryCandidateValue P hStart q r := by
  rcases hv with ⟨a, rfl, ha⟩
  have hEq := terminalHenselBoundarySurvivor_eq_candidate P hStart ha
  rw [hEq]
  rfl

/--
実際の三つの整数 lift のうち boundary filter を通る値は exact に一つ存在する。
-/
theorem arithmeticHenselBoundaryLiftSurvivor_existsUnique
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r : ℕ) :
    ∃! v : ℕ,
      arithmeticHenselBoundaryLiftSurvives P hStart q r v := by
  refine ⟨arithmeticHenselBoundaryCandidateValue P hStart q r,
    arithmeticHenselBoundaryCandidateValue_survives P hStart q r, ?_⟩
  intro v hv
  exact
    arithmeticHenselBoundaryLiftSurvivor_eq_candidateValue
      P hStart q r hv

/--
normalized terminal tail を使うと、boundary を通る actual lift の新しい digit label を
直接読める。
-/
theorem arithmeticHenselBoundaryLiftSurvives_iff_normalizedTerminalTail
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r v : ℕ)
    {cut : ℕ}
    (hcut : cut < P.criticalizationStart) :
    arithmeticHenselBoundaryLiftSurvives P hStart q r v ↔
      ∃ a : Fin 3,
        v = arithmeticHenselThreeLiftValue q r a ∧
        henselThreeLiftDigit a =
          ((- (2 : ℤ) ^ beattyIndex cut *
              P.criticalizationNormalizedTerminalTail
                cut (Nat.le_of_lt hcut) : ℤ) : ZMod 3) := by
  constructor
  · intro hv
    rcases hv with ⟨a, hva, ha⟩
    refine ⟨a, hva, ?_⟩
    exact
      (terminalHenselBoundarySurvives_iff_normalizedTerminalTail
        P hStart hcut a).mp ha
  · rintro ⟨a, hva, ha⟩
    refine ⟨a, hva, ?_⟩
    exact
      (terminalHenselBoundarySurvives_iff_normalizedTerminalTail
        P hStart hcut a).mpr ha

/--
backward Hensel recurrence 自体も課した actual predecessor 候補。
`d` を defect/Record skeleton 側から固定した後に使う。
-/
def arithmeticHenselBoundaryPredecessor
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r d qPrev v : ℕ) : Prop :=
  arithmeticHenselBoundaryLiftSurvives P hStart q r v ∧
    3 * qPrev + 1 = 2 * v + 2 ^ d

/--
boundary condition と backward recurrence を同時に満たす actual lift 値は高々一つ。
recurrence が canonical boundary value を許さない場合は survivor が 0 個になる。
-/
theorem arithmeticHenselBoundaryPredecessor_value_unique
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (q r d : ℕ)
    {qPrev₁ qPrev₂ v₁ v₂ : ℕ}
    (h₁ : arithmeticHenselBoundaryPredecessor
      P hStart q r d qPrev₁ v₁)
    (h₂ : arithmeticHenselBoundaryPredecessor
      P hStart q r d qPrev₂ v₂) :
    v₁ = v₂ := by
  exact
    (arithmeticHenselBoundaryLiftSurvivor_eq_candidateValue
      P hStart q r h₁.1).trans
    (arithmeticHenselBoundaryLiftSurvivor_eq_candidateValue
      P hStart q r h₂.1).symm

end ThirdExampleSearch
end CSTMicro
end Collatz2
