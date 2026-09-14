import CollatzLean.Collatz3.CSTConditional.GlobalCST
import CollatzLean.Collatz3.Bridge.SurvivorFutureMinimumABC
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: global CST と future-minimum dynamics

`GlobalCST` を仮定すると、future minimum から始まる actual odd-only segment は
coefficient-contracting 側へ入れないことを示す。

証明では contracting segment の中から、odd-prefix depth が初めて
`criticalTwoDepth` に届く odd index `p` を取る。
最後の exponent をその first crossing 位置まで短くした critical word を作ると、
同じ affine numerator を持つ standard first-passage realization が得られる。
Global CST はその realization を始点未満へ落とす。
一方、元 actual `p`-step endpoint はそこからさらに 2 で割った値なので、
future-minimum 性と矛盾する。

この一般結果から next-future-minimum block について

* positive Beatty excess は不可能、
* raw symbol `B` は不可能、
* defect は自動的に非減少、
* flat は exact に `C=(0,0)`、

を derived theorem として得る。
-/

namespace Collatz3
namespace CSTConditional

private theorem segmentWord_take_of_le
    (O : Collatz3.OddOrbit)
    (i : ℕ)
    {p q : ℕ}
    (hqp : q ≤ p) :
    (O.segmentWord i p).take q = O.segmentWord i q := by
  induction q generalizing i p with
  | zero =>
      simp
  | succ q ih =>
      cases p with
      | zero => omega
      | succ p =>
          have hqp' : q ≤ p := by omega
          simp only [OddOrbit.segmentWord_succ, List.take_succ_cons]
          rw [ih (i := i + 1) hqp']

private theorem segmentWord_succ_last
    (O : Collatz3.OddOrbit)
    (i p : ℕ) :
    O.segmentWord i (p + 1) =
      O.segmentWord i p ++ [O.exponent (i + p)] := by
  induction p generalizing i with
  | zero =>
      simp [OddOrbit.segmentWord]
  | succ p ih =>
      rw [OddOrbit.segmentWord_succ]
      rw [ih (i := i + 1)]
      rw [OddOrbit.segmentWord_succ]
      simp [ Nat.add_comm, Nat.add_left_comm]

private theorem segmentTwoSteps_succ_last
    (O : Collatz3.OddOrbit)
    (i p : ℕ) :
    Word.twoSteps (O.segmentWord i (p + 1)) =
      Word.twoSteps (O.segmentWord i p) + O.exponent (i + p) := by
  rw [segmentWord_succ_last O i p]
  simp

private theorem prefixTwoDepth_trimmedLast
    (O : Collatz3.OddOrbit)
    (i p d t : ℕ)
    (hp : 0 < p)
    (ht : t < p) :
    Word.prefixTwoDepth
        (O.segmentWord i (p - 1) ++ [d]) t =
      Word.twoSteps (O.segmentWord i t) := by
  have htq : t ≤ p - 1 := by omega
  have hLen : (O.segmentWord i (p - 1)).length = p - 1 := by
    have h := O.segmentWord_oddSteps i (p - 1)
    simpa [Word.oddSteps] using h
  unfold Word.prefixTwoDepth
  rw [List.take_append_of_le_length]
  · rw [segmentWord_take_of_le O i htq]
  · simpa [hLen] using htq

namespace GlobalCST

/--
Global CST の下では、future minimum から始まる actual odd-only segment は
coefficient-contracting になれない。

`2^H ≤ 3^r` がすべての有限長 `r` で成立する。
-/
theorem twoPow_segment_le_threePow_of_futureMinimum
    (G : GlobalCST)
    (O : Collatz3.OddOrbit)
    {i r : ℕ}
    (hMin : O.FutureMinimumAt i) :
    2 ^ Word.twoSteps (O.segmentWord i r) ≤ 3 ^ r := by
  by_contra hNot
  have hContract :
      3 ^ r < 2 ^ Word.twoSteps (O.segmentWord i r) := by
    omega
  have hrPos : 0 < r := by
    by_contra hr
    have hr0 : r = 0 := by omega
    subst r
    simp at hContract
  let Q : ℕ → Prop := fun p =>
    0 < p ∧
      p ≤ r ∧
      Critical.criticalTwoDepth p ≤
        Word.twoSteps (O.segmentWord i p)
  have hTerminal :
      Critical.criticalTwoDepth r ≤
        Word.twoSteps (O.segmentWord i r) := by
    by_contra hNo
    have hDepthLe :
        Word.twoSteps (O.segmentWord i r) ≤ Critical.beattyIndex r := by
      unfold Critical.criticalTwoDepth at hNo
      omega
    have hPowLe :
        2 ^ Word.twoSteps (O.segmentWord i r) ≤
          2 ^ Critical.beattyIndex r :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepthLe
    have hLower := Critical.beattyIndex_lower r
    have : 2 ^ Word.twoSteps (O.segmentWord i r) ≤ 3 ^ r :=
      le_trans hPowLe hLower
    omega
  have hExists : ∃ p : ℕ, Q p :=
    ⟨r, hrPos, le_rfl, hTerminal⟩
  let p : ℕ := Nat.find hExists
  have hpSpec : Q p := Nat.find_spec hExists
  have hpPos : 0 < p := hpSpec.1
  have hpLeR : p ≤ r := hpSpec.2.1
  have hCritP :
      Critical.criticalTwoDepth p ≤
        Word.twoSteps (O.segmentWord i p) :=
    hpSpec.2.2
  let q : ℕ := p - 1
  have hqSucc : q + 1 = p := by
    dsimp [q]
    omega
  have hqLt : q < p := by omega
  have hqLeR : q ≤ r := by omega
  have hPrevRoof :
      Word.twoSteps (O.segmentWord i q) ≤ Critical.beattyIndex q := by
    by_cases hq0 : q = 0
    · rw [hq0]
      simp
    · have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
      by_contra hNo
      have hKq :
          Critical.criticalTwoDepth q ≤
            Word.twoSteps (O.segmentWord i q) := by
        unfold Critical.criticalTwoDepth
        omega
      have hQq : Q q := ⟨hqPos, hqLeR, hKq⟩
      exact (Nat.find_min hExists hqLt) hQq
  have hBeattyStep :
      Critical.beattyIndex q < Critical.beattyIndex p := by
    have h := Critical.beattyIndex_lt_succ q
    simpa [hqSucc] using h
  have hPrevLtCritical :
      Word.twoSteps (O.segmentWord i q) <
        Critical.criticalTwoDepth p := by
    unfold Critical.criticalTwoDepth
    omega
  let K : ℕ := Critical.criticalTwoDepth p
  let D0 : ℕ := Word.twoSteps (O.segmentWord i q)
  let d : ℕ := K - D0
  have hdPos : 0 < d := by
    dsimp [d, K, D0]
    omega
  have hKLeDepthP : K ≤ Word.twoSteps (O.segmentWord i p) := by
    simpa [K] using hCritP
  let u : Word := O.segmentWord i q ++ [d]
  have hValidU : Word.Valid u := by
    apply (O.segmentWord_valid i q).append
    intro e he
    simp only [List.mem_singleton] at he
    subst e
    exact hdPos
  have hOddU : Word.oddSteps u = p := by
    dsimp [u]
    simp [hqSucc]
  have hTwoU : Word.twoSteps u = K := by
    dsimp [u, d, D0]
    simp only [Word.twoSteps_append, Word.twoSteps_cons, Word.twoSteps_nil,
      Nat.add_zero]
    omega
  have hFirstU : Word.CriticalFirstPassage u := by
    constructor
    · rw [hOddU, hTwoU]
    · intro t ht
      rw [hOddU] at ht
      have hPrefix :
          Word.prefixTwoDepth u t =
            Word.twoSteps (O.segmentWord i t) := by
        simpa [u] using
          prefixTwoDepth_trimmedLast O i p d t hpPos ht
      rw [hPrefix]
      by_cases ht0 : t = 0
      · subst t
        simp
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht0
        have htLeR : t ≤ r := by omega
        by_contra hNo
        have hKt :
            Critical.criticalTwoDepth t ≤
              Word.twoSteps (O.segmentWord i t) := by
          unfold Critical.criticalTwoDepth
          omega
        have hQt : Q t := ⟨htPos, htLeR, hKt⟩
        exact (Nat.find_min hExists ht) hQt
  have hFullWord :
      O.segmentWord i p =
        O.segmentWord i q ++ [O.exponent (i + q)] := by
    rw [← hqSucc]
    exact segmentWord_succ_last O i q
  have hAffineU :
      Word.affineConst u =
        Word.affineConst (O.segmentWord i p) := by
    rw [hFullWord]
    dsimp [u]
    simp [Word.affineConst_append]
  let D : ℕ := Word.twoSteps (O.segmentWord i p)
  let rem : ℕ := D - K
  let z : ℕ := 2 ^ rem * O.value (i + p)
  have hKLeD : K ≤ D := by
    simpa [D] using hKLeDepthP
  have hKRem : K + rem = D := by
    dsimp [rem]
    omega
  have hRunP := O.runsSegment i p
  have hMain :=
    (Word.endpointEquation_iff
      (O.segmentWord i p) (O.value i) (O.value (i + p))).1
      hRunP.endpointEquation
  have hMain' :
      2 ^ D * O.value (i + p) =
        3 ^ p * O.value i +
          Word.affineConst (O.segmentWord i p) := by
    simpa [D] using hMain
  have hEqU : u.EndpointEquation (O.value i) z := by
    apply (Word.endpointEquation_iff u (O.value i) z).2
    rw [hOddU, hTwoU, hAffineU]
    calc
      2 ^ K * z =
          2 ^ K * (2 ^ rem * O.value (i + p)) := by rfl
      _ = 2 ^ (K + rem) * O.value (i + p) := by
            rw [pow_add]
            ring
      _ = 2 ^ D * O.value (i + p) := by rw [hKRem]
      _ = 3 ^ p * O.value i +
            Word.affineConst (O.segmentWord i p) := hMain'
  have hDesc : z < O.value i :=
    G.criticalEndpointEquation_descends hValidU hFirstU hEqU
  have hMinEndpoint : O.value i ≤ O.value (i + p) :=
    hMin (i + p) (by omega)
  have hPowOne : 1 ≤ 2 ^ rem := by
    have hPowPos : 0 < 2 ^ rem := Nat.pow_pos (by decide)
    omega
  have hEndpointLeZ : O.value (i + p) ≤ z := by
    dsimp [z]
    calc
      O.value (i + p) = 1 * O.value (i + p) := by simp
      _ ≤ 2 ^ rem * O.value (i + p) :=
        Nat.mul_le_mul_right _ hPowOne
  omega

/-- strict contracting form は future minimum からは不可能。 -/
theorem not_threePow_lt_twoPow_segment_of_futureMinimum
    (G : GlobalCST)
    (O : Collatz3.OddOrbit)
    {i r : ℕ}
    (hMin : O.FutureMinimumAt i) :
    ¬ 3 ^ r < 2 ^ Word.twoSteps (O.segmentWord i r) := by
  intro h
  have hLe := G.twoPow_segment_le_threePow_of_futureMinimum (r:=r) O hMin
  omega

end GlobalCST
end CSTConditional

namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST の下では、future minimum から始まる任意の finite segment の
Beatty excess は必ず `0`。
-/
theorem segmentBeattyExcess_eq_zero_of_futureMinimum
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i r : ℕ}
    (hStart : O.FutureMinimumAt i) :
    O.segmentBeattyExcess i r = 0 := by
  by_contra hZero
  have hPos : 0 < O.segmentBeattyExcess i r := by
    omega
  have hContract :=
    O.threePow_lt_twoPow_segment_of_segmentBeattyExcess_pos hPos
  exact
    (G.not_threePow_lt_twoPow_segment_of_futureMinimum
      O hStart) hContract


/--
Global CST の下では、future minimum を始点とする任意の transition に
raw symbol `B` は現れない。
-/
theorem transitionSymbol_ne_B_of_futureMinimum_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i) :
    O.transitionSymbol i j ≠ .B := by
  intro hB
  have hRaw := (O.transitionSymbol_eq_B_iff i j).1 hB
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := j - i) G hStart
  exact hRaw.2 hZero

/--
Global CST の下では、future minimum を始点とする任意の transition symbol は
`A` または `C` である。
-/
theorem transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i) :
    O.transitionSymbol i j = .A ∨ O.transitionSymbol i j = .C := by
  have hNoB := O.transitionSymbol_ne_B_of_futureMinimum_of_globalCST (j :=j) G hStart
  cases hSym : O.transitionSymbol i j with
  | A =>
      exact Or.inl rfl
  | B =>
      exact False.elim (hNoB hSym)
  | C =>
      exact Or.inr rfl

/-- Global CST の下では next-future-minimum defect は自動的に非減少。 -/
theorem nextFutureMinimum_defect_nondec_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent i ≤
      infiniteSurvivorDefect O.exponent j := by
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := j - i) G hStart
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  rw [hZero] at hBalance
  omega

/--
Global CST の下では flat next-future-minimum transition と `C=(0,0)` が exact に同値。
-/
theorem nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i ↔
      O.transitionSymbol i j = .C := by
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := j - i) G hStart
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  rw [hZero] at hBalance
  constructor
  · intro hFlat
    apply (O.transitionSymbol_eq_C_iff i j).2
    omega
  · intro hC
    have hCarry := (O.transitionSymbol_eq_C_iff i j).1 hC
    omega

namespace FutureMinima

/--
標準 survivor future-minimum 列では Global CST により全 transition の defect が非減少。
-/
theorem defect_nondec_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (t : ℕ) :
    infiniteSurvivorDefect O.exponent (F.index t) ≤
      infiniteSurvivorDefect O.exponent (F.index (t + 1)) := by
  have hNext :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard t
  exact
    O.nextFutureMinimum_defect_nondec_of_globalCST
      G S (F.minimum t) hNext

/-- 標準 survivor future-minimum word では Global CST の下で `B` は一文字も現れない。 -/
theorem transitionSymbol_ne_B_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (hStandard : F.IsStandard)
    (t : ℕ) :
    O.transitionSymbol (F.index t) (F.index (t + 1)) ≠ .B := by
  have hNext :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard t
  exact
    O.transitionSymbol_ne_B_of_futureMinimum_of_globalCST
      G (F.minimum t)

end FutureMinima
end OddOrbit
end Collatz3
