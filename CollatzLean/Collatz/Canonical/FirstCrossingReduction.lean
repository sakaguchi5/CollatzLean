import CollatzLean.Collatz.Canonical.CylinderDynamics
import CollatzLean.Collatz.Word.Geometry

/-!
# canonical first crossing の CORE 還元

canonical first crossing の正 return 排除を、prepend-one の局所不等式 `CORE` に還元する。

このファイルでは `CORE` 自体は証明せず `PrependOneCorePrinciple` として一点だけ切り出す。
それ以外の replay 分解・quotient 3値化・exact gap balance・
`CORE -> canonical descent` は pure finite-word 層で証明する。
-/

namespace Collatz
namespace Word

/--
`1 :: v` の canonical run を先頭一歩で切ったときの replay data。
`boundary` は一歩後の値、`quotient` は suffix `v` の canonical replay level。
-/
structure PrependOneReplayData
    (v : Collatz.Word) (boundary quotient : ℕ) : Prop where
  headStep :
    2 * boundary =
      3 * Word.canonicalStart (1 :: v) + 1
  suffixRuns :
    Runs v boundary (Word.canonicalEnd (1 :: v))
  boundary_eq :
    boundary =
      Word.canonicalStart v +
        Word.residueModulus v * quotient
  endpoint_eq :
    Word.canonicalEnd (1 :: v) =
      Word.canonicalEnd v +
        2 * 3 ^ Word.oddSteps v * quotient
  quotient_le_two :
    quotient ≤ 2
  boundary_mod_three :
    boundary % 3 = 2

/-- prepend-one replay quotient は 0,1,2 の三値しかない。 -/
theorem PrependOneReplayData.quotient_cases
    {v : Collatz.Word} {boundary quotient : ℕ}
    (D : PrependOneReplayData v boundary quotient) :
    quotient = 0 ∨ quotient = 1 ∨ quotient = 2 := by
  have hq : quotient ≤ 2 := D.quotient_le_two
  omega

/-- suffix canonical class で書いた mod 3 条件。 -/
theorem PrependOneReplayData.canonical_boundary_mod_three
    {v : Collatz.Word} {boundary quotient : ℕ}
    (D : PrependOneReplayData v boundary quotient) :
    (v.canonicalStart + v.residueModulus * quotient) % 3 = 2 := by
  rw [← D.boundary_eq]
  exact D.boundary_mod_three

/--
valid な `1 :: v` の canonical actual run から prepend-one replay data を得る。
-/
theorem exists_prependOneReplayData
    {v : Collatz.Word}
    (hvalid : Word.Valid (1 :: v))
    (hvne : v ≠ []) :
    ∃ boundary quotient : ℕ,
      PrependOneReplayData v boundary quotient := by
  have hrun :
      Runs
        (1 :: v)
        (Word.canonicalStart (1 :: v))
        (Word.canonicalEnd (1 :: v)) :=
    hvalid.canonicalRuns
  cases hrun with
  | @cons e w x boundary z he hstep hodd htail =>
      have htail' :
          Runs v boundary (Word.canonicalEnd (1 :: v)) := by
        simpa using htail
      let R :
          ReplayCoordinate
            v boundary (Word.canonicalEnd (1 :: v)) :=
        ReplayCoordinate.ofRuns htail' hvne
      have hhead :
          2 * boundary =
            3 * Word.canonicalStart (1 :: v) + 1 := by
        simpa using hstep
      have hmodulus :
          Word.residueModulus (1 :: v) =
            2 * Word.residueModulus v := by
        unfold Word.residueModulus
        simp only [Word.twoSteps_cons]
        rw [
          show
            1 + Word.twoSteps v + 1 =
              (Word.twoSteps v + 1) + 1 by
            omega
        ]
        rw [pow_succ]
        ring
      have hxlt :
          Word.canonicalStart (1 :: v) <
            2 * Word.residueModulus v := by
        have h := Word.canonicalStart_lt_modulus (1 :: v)
        rw [hmodulus] at h
        exact h
      have hmodPos :
          0 < Word.residueModulus v := by
        simp [Word.residueModulus]
      have hboundaryLt :
          boundary < 3 * Word.residueModulus v := by
        omega
      have hquotientLe :
          R.quotient ≤ 2 := by
        by_contra hnot
        have hthree :
            3 ≤ R.quotient := by
          omega
        have hmul :
            Word.residueModulus v * 3 ≤
              Word.residueModulus v * R.quotient :=
          Nat.mul_le_mul_left
            (Word.residueModulus v) hthree
        have hstart := R.start_eq
        omega
      have hmodThree :
          boundary % 3 = 2 := by
        omega
      exact
        ⟨boundary, R.quotient,
          {
            headStep := hhead
            suffixRuns := htail'
            boundary_eq := R.start_eq
            endpoint_eq := R.finish_eq
            quotient_le_two := hquotientLe
            boundary_mod_three := hmodThree
          }⟩


/--
prepend-one で残る唯一の局所不等式。
`s = canonicalStart(v)`, `t = canonicalEnd(v)`,
`g = contractingGap(1 :: v)` とすると subtraction-free 形で
`s + 1 + 3*t <= 3*s + 2*g*j`
を要求する。
-/
def PrependOneCoreCondition
    (v : Collatz.Word) (quotient : ℕ) : Prop :=
  Word.canonicalStart v + 1 + 3 * Word.canonicalEnd v ≤
    3 * Word.canonicalStart v +
      2 * Word.contractingGap (1 :: v) * quotient


/--
未解決の数学を一点に切り出した CORE 原理。
対象は all-suffix-contracting な suffix `v` を持つ valid contracting prepend-one word。
canonical run から得る三値 replay quotient に対し `CORE` が成立することを主張する。
-/
def PrependOneCorePrinciple : Prop :=
  ∀ (v : Collatz.Word) (boundary quotient : ℕ),
    v ≠ [] →
      Word.Valid (1 :: v) →
      Word.Contracting (1 :: v) →
      Word.AllSuffixesContracting v →
      PrependOneReplayData v boundary quotient →
      PrependOneCoreCondition v quotient


/--
contracting prepend-one word の canonical start/end 差を記録する exact balance。
`CORE` の左右をそのまま使う subtraction-free 形にしている。
-/
theorem prependOne_canonical_gap_balance
    {v : Collatz.Word} {boundary quotient : ℕ}
    (hC : Word.Contracting (1 :: v))
    (D : PrependOneReplayData v boundary quotient) :
    3 * Word.canonicalStart (1 :: v) +
        (Word.canonicalStart v + 1 + 3 * Word.canonicalEnd v) =
      3 * Word.canonicalEnd (1 :: v) +
        (3 * Word.canonicalStart v +
          2 * Word.contractingGap (1 :: v) * quotient) := by
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
  have htwo :
      Word.residueModulus v =
        2 ^ Word.twoSteps (1 :: v) := by
    unfold Word.residueModulus
    simp only [Word.twoSteps_cons]
    rw [Nat.add_comm 1 (Word.twoSteps v)]
  have hthree :
      3 ^ Word.oddSteps (1 :: v) =
        3 * 3 ^ Word.oddSteps v := by
    simp only [Word.oddSteps_cons, pow_succ]
    ring
  have hmodulusGap :
      Word.residueModulus v =
        3 * 3 ^ Word.oddSteps v +
          Word.contractingGap (1 :: v) := by
    calc
      Word.residueModulus v =
          2 ^ Word.twoSteps (1 :: v) :=
        htwo
      _ =
          3 ^ Word.oddSteps (1 :: v) +
            Word.contractingGap (1 :: v) :=
        hgap.symm
      _ =
          3 * 3 ^ Word.oddSteps v +
            Word.contractingGap (1 :: v) := by
        rw [hthree]
  have hhead := D.headStep
  rw [D.boundary_eq, hmodulusGap] at hhead
  rw [D.endpoint_eq]
  nlinarith [hhead]


/-- CORE が成立すれば prepend-one canonical run は上昇しない。 -/
theorem canonicalEnd_le_canonicalStart_of_prependOneCore
    {v : Collatz.Word} {boundary quotient : ℕ}
    (hC : Word.Contracting (1 :: v))
    (D : PrependOneReplayData v boundary quotient)
    (hCore : PrependOneCoreCondition v quotient) :
    Word.canonicalEnd (1 :: v) ≤
      Word.canonicalStart (1 :: v) := by
  have hbalance :=
    prependOne_canonical_gap_balance hC D
  let leftCore :=
    Word.canonicalStart v + 1 +
      3 * Word.canonicalEnd v
  let rightCore :=
    3 * Word.canonicalStart v +
      2 * Word.contractingGap (1 :: v) * quotient
  have hcore' :
      leftCore ≤ rightCore := by
    simpa [
      leftCore,
      rightCore,
      PrependOneCoreCondition
    ] using hCore
  have hbalance' :
      3 * Word.canonicalStart (1 :: v) + leftCore =
        3 * Word.canonicalEnd (1 :: v) + rightCore := by
    simpa [leftCore, rightCore] using hbalance
  omega


/--
長さ2以上の valid first crossing では先頭指数は必ず1。
-/
theorem FirstCrossing.head_eq_one_of_cons_tail
    {e : ℕ} {v : Collatz.Word}
    (hvalid : Word.Valid (e :: v))
    (hF : Word.FirstCrossing (e :: v))
    (hvne : v ≠ []) :
    e = 1 := by
  have hvpos :
      0 < v.length :=
    List.length_pos_of_ne_nil hvne
  have hlen :
      1 < (e :: v).length := by
    simp only [List.length_cons]
    omega
  have hExp :=
    hF.properExpanding 1 (by omega) hlen
  have hpow :
      2 ^ e < 3 := by
    simpa [
      Word.Expanding,
      Word.twoSteps,
      Word.oddSteps
    ] using hExp
  have hepos :
      0 < e :=
    hvalid e (by simp)
  by_contra hne
  have hetwo :
      2 ≤ e := by
    omega
  have hmono :
      2 ^ 2 ≤ 2 ^ e :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ)) hetwo
  have hfour :
      4 ≤ 2 ^ e := by
    simpa using hmono
  omega


/--
CORE 原理があれば、長さ2以上の valid first crossing の canonical run は上昇しない。
-/
theorem FirstCrossing.canonicalEnd_le_canonicalStart_of_core
    {w : Collatz.Word}
    (hCore : PrependOneCorePrinciple)
    (hvalid : Word.Valid w)
    (hF : Word.FirstCrossing w)
    (hlen : 1 < w.length) :
    Word.canonicalEnd w ≤ Word.canonicalStart w := by
  cases w with
  | nil =>
      simp at hlen
  | cons e v =>
      have hvne :
          v ≠ [] := by
        intro hv
        subst v
        simp at hlen
      have he :
          e = 1 :=
        FirstCrossing.head_eq_one_of_cons_tail
          hvalid hF hvne
      subst e
      have htailAll :
          Word.AllSuffixesContracting v := by
        have hall := hF.allSuffixesContracting
        change
          Word.Contracting (1 :: v) ∧
            Word.AllSuffixesContracting v at hall
        exact hall.2
      obtain ⟨boundary, quotient, hReplay⟩ :=
        exists_prependOneReplayData hvalid hvne
      have hCondition :
          PrependOneCoreCondition v quotient :=
        hCore
          v
          boundary
          quotient
          hvne
          hvalid
          hF.terminalContracting
          htailAll
          hReplay
      exact
        canonicalEnd_le_canonicalStart_of_prependOneCore
          hF.terminalContracting
          hReplay
          hCondition

end Word
end Collatz
