import CollatzLean.Collatz.Canonical.FirstCrossingReduction
import CollatzLean.Collatz.External.TwoThreeGap

/-!
# prepend-one CORE の三分岐

`PrependOneCorePrinciple` を replay quotient `j = 0,1,2` の三枝へ分解する。

* `j = 0` は canonical residue を保持する本質的な残余枝。
* `j = 1` は Baker 型 gap 下界により十分長い語で自動的に CORE。
* `j = 2` も同じ cutoff 以後で自動的に CORE。

Baker 入力はこのファイルでのみ明示的に使い、
`FirstCrossingReduction` の pure finite-word 層には持ち込まない。
-/

namespace Collatz
namespace Word

/-- 固定 quotient における prepend-one CORE 原理。 -/
def PrependOneCoreBranchPrinciple (quotient : ℕ) : Prop :=
  ∀ (v : Collatz.Word) (boundary : ℕ),
    v ≠ [] →
      Word.Valid (1 :: v) →
      Word.Contracting (1 :: v) →
      Word.AllSuffixesContracting v →
      PrependOneReplayData v boundary quotient →
      PrependOneCoreCondition v quotient

/-- quotient `0` の CORE 枝。 -/
abbrev PrependOneCoreZeroPrinciple : Prop :=
  PrependOneCoreBranchPrinciple 0

/-- quotient `1` の CORE 枝。 -/
abbrev PrependOneCoreOnePrinciple : Prop :=
  PrependOneCoreBranchPrinciple 1

/-- quotient `2` の CORE 枝。 -/
abbrev PrependOneCoreTwoPrinciple : Prop :=
  PrependOneCoreBranchPrinciple 2

/--
固定 cutoff 未満だけを要求する CORE 枝。
Baker で cutoff 以後を閉じた後に残る有限側を表す。
-/
def PrependOneCoreBranchBelow (quotient cutoff : ℕ) : Prop :=
  ∀ (v : Collatz.Word) (boundary : ℕ),
    v ≠ [] →
      Word.Valid (1 :: v) →
      Word.Contracting (1 :: v) →
      Word.AllSuffixesContracting v →
      PrependOneReplayData v boundary quotient →
      Word.oddSteps v + 1 < cutoff →
      PrependOneCoreCondition v quotient

/-- quotient `1` の有限残余枝。 -/
abbrev PrependOneCoreOneBelow (cutoff : ℕ) : Prop :=
  PrependOneCoreBranchBelow 1 cutoff

/-- quotient `2` の有限残余枝。 -/
abbrev PrependOneCoreTwoBelow (cutoff : ℕ) : Prop :=
  PrependOneCoreBranchBelow 2 cutoff

/-- 三枝すべての CORE があれば元の CORE 原理を得る。 -/
theorem prependOneCorePrinciple_of_three_branches
    (hZero : PrependOneCoreZeroPrinciple)
    (hOne : PrependOneCoreOnePrinciple)
    (hTwo : PrependOneCoreTwoPrinciple) :
    PrependOneCorePrinciple := by
  intro v boundary quotient hvne hvalid hC hAll D
  rcases D.quotient_cases with hq | hq | hq
  · subst quotient
    exact hZero v boundary hvne hvalid hC hAll D
  · subst quotient
    exact hOne v boundary hvne hvalid hC hAll D
  · subst quotient
    exact hTwo v boundary hvne hvalid hC hAll D

/-- quotient `0` では canonical start 自身が `2 mod 3`。 -/
theorem PrependOneReplayData.zero_canonicalStart_mod_three
    {v : Collatz.Word} {boundary : ℕ}
    (D : PrependOneReplayData v boundary 0) :
    Word.canonicalStart v % 3 = 2 := by
  have h := D.canonical_boundary_mod_three
  simpa using h

/--
全 nonempty suffix が contracting なら affine constant は sharp に小さい。
各 affine term に対応する suffix の contracting 性を帰納的に足し合わせる。
-/
theorem AllSuffixesContracting.three_mul_affineConst_lt_oddSteps
    {v : Collatz.Word}
    (hvne : v ≠ [])
    (hAll : Word.AllSuffixesContracting v) :
    3 * Word.affineConst v <
      Word.oddSteps v * 2 ^ Word.twoSteps v := by
  induction v with
  | nil =>
      contradiction
  | cons e w ih =>
      change
        Word.Contracting (e :: w) ∧
          Word.AllSuffixesContracting w at hAll
      have hWhole : Word.Contracting (e :: w) := hAll.1
      by_cases hw : w = []
      · subst w
        simpa [Word.Contracting, Word.affineConst, Word.oddSteps,
          Word.twoSteps] using hWhole
      · have hTail :
            3 * Word.affineConst w <
              Word.oddSteps w * 2 ^ Word.twoSteps w :=
          ih hw hAll.2
        have hHead :
            3 * 3 ^ Word.oddSteps w <
              2 ^ (e + Word.twoSteps w) := by
          simpa [Word.Contracting, pow_succ, Nat.mul_comm] using hWhole
        have hPowPos : 0 < 2 ^ e :=
          Nat.pow_pos (by omega)
        have hTailScaled :
            3 * (2 ^ e * Word.affineConst w) <
              Word.oddSteps w * 2 ^ (e + Word.twoSteps w) := by
          have hmul :=
            (Nat.mul_lt_mul_left hPowPos).2 hTail
          calc
            3 * (2 ^ e * Word.affineConst w)
                = 2 ^ e * (3 * Word.affineConst w) := by ring
            _ < 2 ^ e *
                (Word.oddSteps w * 2 ^ Word.twoSteps w) := hmul
            _ = Word.oddSteps w *
                2 ^ (e + Word.twoSteps w) := by
                  rw [pow_add]
                  ring
        calc
          3 * Word.affineConst (e :: w)
              = 3 * 3 ^ Word.oddSteps w +
                  3 * (2 ^ e * Word.affineConst w) := by
                    simp only [Word.affineConst_cons]
                    ring
          _ < 2 ^ (e + Word.twoSteps w) +
                Word.oddSteps w * 2 ^ (e + Word.twoSteps w) :=
            Nat.add_lt_add hHead hTailScaled
          _ = Word.oddSteps (e :: w) *
                2 ^ Word.twoSteps (e :: w) := by
            simp only [Word.oddSteps_cons, Word.twoSteps_cons]
            ring

/--
all-suffix sharp boundから CORE を得るための局所十分条件。
`p = oddSteps(v)+1`, `g = contractingGap(1::v)` として
`p <= 2*g*j` なら CORE が成立する。
-/
theorem prependOneCore_of_gap_length
    {v : Collatz.Word} {quotient : ℕ}
    (hvne : v ≠ [])
    (hC : Word.Contracting (1 :: v))
    (hAll : Word.AllSuffixesContracting v)
    (hlarge :
      Word.oddSteps v + 1 ≤
        2 * Word.contractingGap (1 :: v) * quotient) :
    PrependOneCoreCondition v quotient := by
  let A := 2 ^ Word.twoSteps v
  let C := 3 ^ Word.oddSteps v
  let B := Word.affineConst v
  let s := Word.canonicalStart v
  let t := Word.canonicalEnd v
  let g := Word.contractingGap (1 :: v)
  let leftCore := s + 1 + 3 * t
  let rightCore := 3 * s + 2 * g * quotient
  let affineBudget := A + 3 * B
  let replayBudget := g * s + 2 * A * g * quotient
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.pow_pos (by omega)
  have hAffine :
      3 * B < Word.oddSteps v * A := by
    simpa [A, B] using
      (Word.AllSuffixesContracting.three_mul_affineConst_lt_oddSteps hvne hAll)
  have hAffineBudget :
      affineBudget ≤ A * (Word.oddSteps v + 1) := by
    dsimp [affineBudget]
    nlinarith [hAffine]
  have hLengthBudget :
      A * (Word.oddSteps v + 1) ≤
        A * (2 * g * quotient) := by
    exact Nat.mul_le_mul_left A (by simpa [g] using hlarge)
  have hBudget : affineBudget ≤ replayBudget := by
    calc
      affineBudget ≤ A * (Word.oddSteps v + 1) := hAffineBudget
      _ ≤ A * (2 * g * quotient) := hLengthBudget
      _ ≤ replayBudget := by
        dsimp [replayBudget]
        nlinarith
  have hReal := Word.canonicalEnd_realizes v
  unfold Word.Realizes at hReal
  have hReal' : A * t = C * s + B := by
    simpa [A, B, C, s, t] using hReal
  have hpow :
      3 ^ Word.oddSteps (1 :: v) ≤
        2 ^ Word.twoSteps (1 :: v) :=
    Nat.le_of_lt hC
  have hgap :
      3 ^ Word.oddSteps (1 :: v) +
          Word.contractingGap (1 :: v) =
        2 ^ Word.twoSteps (1 :: v) := by
    unfold Word.contractingGap
    exact Nat.add_sub_of_le hpow
  have hGap' : 3 * C + g = 2 * A := by
    dsimp [A, C, g]
    have h := hgap
    simp only [Word.oddSteps_cons, Word.twoSteps_cons] at h
    rw [Nat.add_comm 1 (Word.twoSteps v)] at h
    rw [pow_succ, pow_succ] at h
    simpa [Nat.mul_comm] using h
  have hBalance :
      A * leftCore + replayBudget =
        A * rightCore + affineBudget := by
    dsimp [leftCore, rightCore, affineBudget, replayBudget]
    nlinarith [hReal', hGap']
  have hScaled : A * leftCore ≤ A * rightCore := by
    omega
  have hCore : leftCore ≤ rightCore := by
    by_contra hnot
    have hlt : rightCore < leftCore := Nat.lt_of_not_ge hnot
    have hscaledLt : A * rightCore < A * leftCore :=
      (Nat.mul_lt_mul_left hApos).2 hlt
    omega
  simpa [leftCore, rightCore, PrependOneCoreCondition, s, t, g] using hCore

/-- CORE が失敗するなら `2*g*j < oddSteps(v)+1` が必要。 -/
theorem prependOneCore_failure_forces_small_gap
    {v : Collatz.Word} {quotient : ℕ}
    (hvne : v ≠ [])
    (hC : Word.Contracting (1 :: v))
    (hAll : Word.AllSuffixesContracting v)
    (hFail : ¬ PrependOneCoreCondition v quotient) :
    2 * Word.contractingGap (1 :: v) * quotient <
      Word.oddSteps v + 1 := by
  by_contra hnot
  have hlarge :
      Word.oddSteps v + 1 ≤
        2 * Word.contractingGap (1 :: v) * quotient := by
    omega
  exact hFail (prependOneCore_of_gap_length hvne hC hAll hlarge)

/-- quotient `1` の CORE 失敗には `2*g < p` が必要。 -/
theorem prependOneCore_one_failure_forces_small_gap
    {v : Collatz.Word}
    (hvne : v ≠ [])
    (hC : Word.Contracting (1 :: v))
    (hAll : Word.AllSuffixesContracting v)
    (hFail : ¬ PrependOneCoreCondition v 1) :
    2 * Word.contractingGap (1 :: v) <
      Word.oddSteps v + 1 := by
  simpa using
    (prependOneCore_failure_forces_small_gap hvne hC hAll hFail)

/-- quotient `2` の CORE 失敗には `4*g < p` が必要。 -/
theorem prependOneCore_two_failure_forces_small_gap
    {v : Collatz.Word}
    (hvne : v ≠ [])
    (hC : Word.Contracting (1 :: v))
    (hAll : Word.AllSuffixesContracting v)
    (hFail : ¬ PrependOneCoreCondition v 2) :
    4 * Word.contractingGap (1 :: v) <
      Word.oddSteps v + 1 := by
  have h :=
    prependOneCore_failure_forces_small_gap hvne hC hAll hFail
  nlinarith [h]

/--
Baker 型 gap 下界から、十分長い contracting prepend-one word では
multiplicative gap 自体が odd-step 数以上になる。
-/
theorem prependOne_contractingGap_ge_oddSteps_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ v : Collatz.Word,
        Word.Contracting (1 :: v) →
        N ≤ Word.oddSteps v + 1 →
          Word.oddSteps v + 1 ≤
            Word.contractingGap (1 :: v) := by
  rcases hGap with ⟨K, E, hK, hBaker⟩
  obtain ⟨N, hN⟩ :=
    Arithmetic.polynomialBelowTwoPower (2 * K) (E + 1)
  refine ⟨N, ?_⟩
  intro v hC hlen
  let p := Word.oddSteps v + 1
  let H := Word.twoSteps (1 :: v)
  let g := Word.contractingGap (1 :: v)
  have hpN : N ≤ p := by
    simpa [p] using hlen
  have hpPos : 0 < p := by
    dsimp [p]
    omega
  have hContract : 3 ^ p < 2 ^ H := by
    simpa [p, H, Word.Contracting] using hC
  have hBaker' :
      3 ^ p ≤ K * (p + 1) ^ E * g := by
    have h := hBaker p H hpPos hContract
    have hg : g = 2 ^ H - 3 ^ p := by
      rfl
    rw [← hg] at h
    exact h
  have hPoly :
      (2 * K) * (p + 1) ^ (E + 1) < 2 ^ (p + 1) :=
    hN p hpN
  have hTwoThree :
      2 ^ (p + 1) ≤ 2 * 3 ^ p :=
    Arithmetic.twoPow_succ_le_two_mul_threePow p
  by_contra hnot
  have hglt : g < p := Nat.lt_of_not_ge hnot
  have hfactorPos : 0 < (2 * K) * (p + 1) ^ E :=
    Nat.mul_pos (Nat.mul_pos (by omega) hK) (Nat.pow_pos (by omega))
  have hBakerScaled :
      2 * 3 ^ p ≤ (2 * K) * (p + 1) ^ E * g := by
    have h := Nat.mul_le_mul_left 2 hBaker'
    simpa [mul_assoc] using h
  have hGapUpper :
      (2 * K) * (p + 1) ^ E * g <
        (2 * K) * (p + 1) ^ E * p :=
    (Nat.mul_lt_mul_left hfactorPos).2 hglt
  have hPolynomialUpper :
      (2 * K) * (p + 1) ^ E * p ≤
        (2 * K) * (p + 1) ^ (E + 1) := by
    calc
      (2 * K) * (p + 1) ^ E * p
          ≤ (2 * K) * (p + 1) ^ E * (p + 1) :=
        Nat.mul_le_mul_left ((2 * K) * (p + 1) ^ E) (by omega)
      _ = (2 * K) * (p + 1) ^ (E + 1) := by
        rw [pow_succ]
        ring
  have hcontra : 2 * 3 ^ p < 2 * 3 ^ p := by
    calc
      2 * 3 ^ p ≤ (2 * K) * (p + 1) ^ E * g := hBakerScaled
      _ < (2 * K) * (p + 1) ^ E * p := hGapUpper
      _ ≤ (2 * K) * (p + 1) ^ (E + 1) := hPolynomialUpper
      _ < 2 ^ (p + 1) := hPoly
      _ ≤ 2 * 3 ^ p := hTwoThree
  omega

/--
Baker 型 gap 下界のもと、同じ cutoff 以後では
positive quotient (`j=1,2`) の CORE が自動的に成立する。
-/
theorem prependOneCore_positive_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ (v : Collatz.Word) (boundary quotient : ℕ),
        v ≠ [] →
        Word.Valid (1 :: v) →
        Word.Contracting (1 :: v) →
        Word.AllSuffixesContracting v →
        PrependOneReplayData v boundary quotient →
        N ≤ Word.oddSteps v + 1 →
        0 < quotient →
          PrependOneCoreCondition v quotient := by
  obtain ⟨N, hN⟩ := prependOne_contractingGap_ge_oddSteps_eventually hGap
  refine ⟨N, ?_⟩
  intro v boundary quotient hvne _hvalid hC hAll _D hlen hq
  have hgap :
      Word.oddSteps v + 1 ≤
        Word.contractingGap (1 :: v) :=
    hN v hC hlen
  have hqOne : 1 ≤ quotient := by omega
  have hgapQ :
      Word.contractingGap (1 :: v) ≤
        Word.contractingGap (1 :: v) * quotient := by
    have h :=
      Nat.mul_le_mul_left
        (Word.contractingGap (1 :: v)) hqOne
    simpa using h
  have hlarge :
      Word.oddSteps v + 1 ≤
        2 * Word.contractingGap (1 :: v) * quotient := by
    calc
      Word.oddSteps v + 1
          ≤ Word.contractingGap (1 :: v) := hgap
      _ ≤ Word.contractingGap (1 :: v) * quotient := hgapQ
      _ ≤ 2 * Word.contractingGap (1 :: v) * quotient := by
        nlinarith
  exact prependOneCore_of_gap_length hvne hC hAll hlarge

/-- Baker 付きでは quotient `1` 枝は十分長い部分で閉じる。 -/
theorem prependOneCore_one_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ (v : Collatz.Word) (boundary : ℕ),
        v ≠ [] →
        Word.Valid (1 :: v) →
        Word.Contracting (1 :: v) →
        Word.AllSuffixesContracting v →
        PrependOneReplayData v boundary 1 →
        N ≤ Word.oddSteps v + 1 →
          PrependOneCoreCondition v 1 := by
  obtain ⟨N, hN⟩ := prependOneCore_positive_eventually hGap
  refine ⟨N, ?_⟩
  intro v boundary hvne hvalid hC hAll D hlen
  exact hN v boundary 1 hvne hvalid hC hAll D hlen (by omega)

/-- Baker 付きでは quotient `2` 枝も十分長い部分で閉じる。 -/
theorem prependOneCore_two_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ (v : Collatz.Word) (boundary : ℕ),
        v ≠ [] →
        Word.Valid (1 :: v) →
        Word.Contracting (1 :: v) →
        Word.AllSuffixesContracting v →
        PrependOneReplayData v boundary 2 →
        N ≤ Word.oddSteps v + 1 →
          PrependOneCoreCondition v 2 := by
  obtain ⟨N, hN⟩ := prependOneCore_positive_eventually hGap
  refine ⟨N, ?_⟩
  intro v boundary hvne hvalid hC hAll D hlen
  exact hN v boundary 2 hvne hvalid hC hAll D hlen (by omega)

/--
Baker 付き CORE の最終三分岐 reduction。

`j=0` は全長で残し、`j=1,2` は共通 cutoff 未満の有限側だけ残す。
cutoff 以後の positive quotient は Baker により自動的に CORE となる。
-/
theorem prependOneCorePrinciple_of_baker_three_branches
    (hGap : External.TwoThreeGapPolynomialBound)
    (hZero : PrependOneCoreZeroPrinciple) :
    ∃ cutoff : ℕ,
      PrependOneCoreOneBelow cutoff →
      PrependOneCoreTwoBelow cutoff →
        PrependOneCorePrinciple := by
  obtain ⟨cutoff, hPositive⟩ :=
    prependOneCore_positive_eventually hGap
  refine ⟨cutoff, ?_⟩
  intro hOneSmall hTwoSmall v boundary quotient hvne hvalid hC hAll D
  rcases D.quotient_cases with hq | hq | hq
  · subst quotient
    exact hZero v boundary hvne hvalid hC hAll D
  · subst quotient
    by_cases hsmall : Word.oddSteps v + 1 < cutoff
    · exact hOneSmall v boundary hvne hvalid hC hAll D hsmall
    · exact
        hPositive v boundary 1 hvne hvalid hC hAll D
          (by omega) (by omega)
  · subst quotient
    by_cases hsmall : Word.oddSteps v + 1 < cutoff
    · exact hTwoSmall v boundary hvne hvalid hC hAll D hsmall
    · exact
        hPositive v boundary 2 hvne hvalid hC hAll D
          (by omega) (by omega)

end Word
end Collatz
