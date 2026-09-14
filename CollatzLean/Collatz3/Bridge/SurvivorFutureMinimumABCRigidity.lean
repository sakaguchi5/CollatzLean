import CollatzLean.Collatz3.Bridge.SurvivorFutureMinimumABC
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumBarrier
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: ABC symbolic dynamics の finite-state rigidity

三文字

* `A` : rise,
* `B` : carry `1` positive-excess transition,
* `C` : carry `0` transition

を、三状態

* `S0` : 直近の `C` 以後 rise 0 回,
* `S1` : rise 1 回,
* `S2` : rise 2 回

で読む最小オートマトンへ接続する。

状態は combinatorial primitive ではなく、既存 power barrier の読み替えである。

* `S1` は `2*3^n ≤ 3*2^B_n`（ratio `≤ 3/2`）、
* `S2` は `8*3^n ≤ 9*2^B_n`（ratio `≤ 9/8`）。

`B` は carry `1` なので barrier を保存し、`C` は state を `S0` に reset する。
`S2` から `A` を読むと rise-start opposite barrier と矛盾する。

この有限状態則から

* `A B* A B* A` の禁止,
* `#A ≤ 2 #C + 2`,
* 非減少区間で `δ_end - δ_start ≤ 2 #C + 2`,
* `A B* A` 終点で一般化 `9/8` barrier

を derived theorem として導く。
-/

namespace Collatz3
namespace Bridge

/-- ABC word を読む三状態。 -/
inductive FutureMinimumABCState where
  | S0
  | S1
  | S2
  deriving DecidableEq, BEq, Repr

namespace FutureMinimumABCState

/-- state が保持する「直近 C 以後の A 個数」。 -/
def riseCredit : FutureMinimumABCState → ℕ
  | .S0 => 0
  | .S1 => 1
  | .S2 => 2

/--
三状態 automaton の一文字遷移。

`B` は state を保持、`C` は `S0` へ reset、`A` は `S0→S1→S2` と進み、
`S2 --A-->` だけが禁止。
-/
def step : FutureMinimumABCState → FutureMinimumABC → Option FutureMinimumABCState
  | .S0, .A => some .S1
  | .S0, .B => some .S0
  | .S0, .C => some .S0
  | .S1, .A => some .S2
  | .S1, .B => some .S1
  | .S1, .C => some .S0
  | .S2, .A => none
  | .S2, .B => some .S2
  | .S2, .C => some .S0

end FutureMinimumABCState

/-- state `s` から有限 ABC word を最後まで読めること。 -/
def ABCAcceptsFrom : FutureMinimumABCState → List FutureMinimumABC → Prop
  | _s, [] => True
  | s, a :: w =>
      match s.step a with
      | none => False
      | some s' => ABCAcceptsFrom s' w

/-- 初期 state `S0` から読める ABC word。 -/
def ABCAdmissible (w : List FutureMinimumABC) : Prop :=
  ABCAcceptsFrom .S0 w

/--
automaton の一文字 step は rise-credit / recharge-count の局所不等式を満たす。
-/
theorem ABCState_step_credit_bound
    {s s' : FutureMinimumABCState}
    {a : FutureMinimumABC}
    (hStep : s.step a = some s') :
    (if a = .A then 1 else 0) + s.riseCredit ≤
      2 * (if a = .C then 1 else 0) + s'.riseCredit := by
  cases s <;> cases a <;> cases s' <;>
    simp [FutureMinimumABCState.step, FutureMinimumABCState.riseCredit] at hStep ⊢

/--
任意の accepted word で、残っている state credit まで含めて

`#A + credit(start) ≤ 2 #C + 2`

が成り立つ。
-/
theorem ABC_count_A_add_credit_le_two_count_C_add_two
    (s : FutureMinimumABCState)
    (w : List FutureMinimumABC)
    (hAcc : ABCAcceptsFrom s w) :
    w.count .A + s.riseCredit ≤
      2 * w.count .C + 2 := by
  induction w generalizing s with
  | nil =>
      cases s <;>
        simp [FutureMinimumABCState.riseCredit]
  | cons a w ih =>
      cases hStep : s.step a with
      | none =>
          simp [ABCAcceptsFrom, hStep] at hAcc
      | some s' =>
          have hTail : ABCAcceptsFrom s' w := by
            simpa [ABCAcceptsFrom, hStep] using hAcc
          have hIH := ih s' hTail
          cases a <;>
            cases s <;>
            simp [FutureMinimumABCState.step] at hStep <;>
            subst s' <;>
            simp [FutureMinimumABCState.riseCredit] at hIH ⊢ <;>
            omega

/-- 初期 state `S0` から読める word では `#A ≤ 2#C+2`。 -/
theorem ABCAdmissible.count_A_le_two_count_C_add_two
    {w : List FutureMinimumABC}
    (h : ABCAdmissible w) :
    w.count .A ≤ 2 * w.count .C + 2 := by
  have hBound :=
    ABC_count_A_add_credit_le_two_count_C_add_two .S0 w h
  simpa [FutureMinimumABCState.riseCredit] using hBound

/-- `log₂(4/3) = 2 - log₂3`。rise margin floor の表示変換。 -/
theorem logb_two_four_div_three_eq_two_sub_logb_three :
    Real.logb 2 ((4 : ℝ) / 3) =
      2 - Real.logb 2 3 := by
  rw [Real.logb_div (b := (2 : ℝ)) (by norm_num) (by norm_num)]
  have hFour : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [hFour, Real.logb_pow]
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

end Bridge

namespace OddOrbit

open Bridge

/--
任意の power-ratio barrier `p*3^a ≤ q*2^B_a` は carry `1` addition で保存される。
-/
theorem scaledPowerBarrier_add_of_beattyCarry_eq_one
    {p q a r : ℕ}
    (hBarrier :
      p * 3 ^ a ≤ q * 2 ^ Critical.beattyIndex a)
    (hCarry : Critical.beattyCarry a r = 1) :
    p * 3 ^ (a + r) ≤
      q * 2 ^ Critical.beattyIndex (a + r) := by
  have hUpperR := Critical.beattyIndex_upper r
  have hMul := Nat.mul_le_mul hBarrier hUpperR
  have hAdd := Critical.beattyIndex_add_eq a r
  rw [hCarry] at hAdd
  calc
    p * 3 ^ (a + r) =
        (p * 3 ^ a) * 3 ^ r := by
      rw [pow_add]
      ring
    _ ≤
        (q * 2 ^ Critical.beattyIndex a) *
          2 ^ (Critical.beattyIndex r + 1) := hMul
    _ = q * 2 ^ Critical.beattyIndex (a + r) := by
      rw [hAdd]
      rw [show
        Critical.beattyIndex a + Critical.beattyIndex r + 1 =
          Critical.beattyIndex a + (Critical.beattyIndex r + 1) by omega]
      rw [pow_add]
      ring

/-- `B` transition は任意の scaled power barrier を保存する。 -/
theorem transitionSymbol_B_preserves_scaledPowerBarrier
    (O : Collatz3.OddOrbit)
    {p q i j : ℕ}
    (hij : i < j)
    (hB : O.transitionSymbol i j = .B)
    (hBarrier :
      p * 3 ^ i ≤ q * 2 ^ Critical.beattyIndex i) :
    p * 3 ^ j ≤ q * 2 ^ Critical.beattyIndex j := by
  let r : ℕ := j - i
  have hIndex : i + r = j := by
    dsimp [r]
    exact Nat.add_sub_of_le (Nat.le_of_lt hij)
  have hCarry : Critical.beattyCarry i r = 1 := by
    have h := (O.transitionSymbol_eq_B_iff i j).1 hB
    simpa [r] using h.1
  have hProp :=
    scaledPowerBarrier_add_of_beattyCarry_eq_one
      (p := p) (q := q) (a := i) (r := r) hBarrier hCarry
  simpa [hIndex] using hProp

/--
`A` transition を一度通ると、その endpoint は ratio `≤3/2` barrier

`2*3^j ≤ 3*2^B_j`

へ入る。
-/
theorem nextFutureMinimum_symbol_A_endpoint_threeHalvesBarrier
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A) :
    2 * 3 ^ j ≤ 3 * 2 ^ Critical.beattyIndex j := by
  let r : ℕ := j - i
  have hIndex : i + r = j := by
    dsimp [r]
    exact Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  have hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 :=
    (O.nextFutureMinimum_symbol_A_iff_defect_succ S hNext).1 hA
  have hBlock :
      2 * 3 ^ r ≤ 3 * 2 ^ Critical.beattyIndex r := by
    simpa [r] using
      O.nextFutureMinimum_defect_succ_length_power_bound
        S hStart hNext hRise
  have hCarry : Critical.beattyCarry i r = 1 := by
    have h := (O.transitionSymbol_eq_A_iff i j).1 hA
    simpa [r] using h.1
  have hAdd := Critical.beattyIndex_add_eq i r
  rw [hIndex, hCarry] at hAdd
  have hUpperI := Critical.beattyIndex_upper i
  have hMul := Nat.mul_le_mul hUpperI hBlock
  calc
    2 * 3 ^ j =
        3 ^ i * (2 * 3 ^ r) := by
      rw [← hIndex, pow_add]
      ring
    _ ≤
        2 ^ (Critical.beattyIndex i + 1) *
          (3 * 2 ^ Critical.beattyIndex r) := hMul
    _ = 3 * 2 ^ Critical.beattyIndex j := by
      rw [hAdd]
      rw [show
        Critical.beattyIndex i + Critical.beattyIndex r + 1 =
          (Critical.beattyIndex i + 1) + Critical.beattyIndex r by omega]
      rw [pow_add]
      ring

/--
ratio `≤3/2` state からさらに `A` を一度通ると、endpoint は ratio `≤9/8` barrier に入る。
-/
theorem nextFutureMinimum_symbol_A_endpoint_nineEighthsBarrier_of_threeHalves
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A)
    (hBarrier :
      2 * 3 ^ i ≤ 3 * 2 ^ Critical.beattyIndex i) :
    8 * 3 ^ j ≤ 9 * 2 ^ Critical.beattyIndex j := by
  let r : ℕ := j - i
  have hIndex : i + r = j := by
    dsimp [r]
    exact Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  have hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 :=
    (O.nextFutureMinimum_symbol_A_iff_defect_succ S hNext).1 hA
  have hBlock :
      2 * 3 ^ r ≤ 3 * 2 ^ Critical.beattyIndex r := by
    simpa [r] using
      O.nextFutureMinimum_defect_succ_length_power_bound
        S hStart hNext hRise
  have hCarry : Critical.beattyCarry i r = 1 := by
    have h := (O.transitionSymbol_eq_A_iff i j).1 hA
    simpa [r] using h.1
  have hAdd := Critical.beattyIndex_add_eq i r
  rw [hIndex, hCarry] at hAdd
  have hMul := Nat.mul_le_mul hBarrier hBlock
  have hTwice := Nat.mul_le_mul_left 2 hMul
  calc
    8 * 3 ^ j =
        2 * ((2 * 3 ^ i) * (2 * 3 ^ r)) := by
      rw [← hIndex, pow_add]
      ring
    _ ≤
        2 *
          ((3 * 2 ^ Critical.beattyIndex i) *
            (3 * 2 ^ Critical.beattyIndex r)) := hTwice
    _ = 9 * 2 ^ Critical.beattyIndex j := by
      rw [hAdd]
      rw [show
        Critical.beattyIndex i + Critical.beattyIndex r + 1 =
          (Critical.beattyIndex i + Critical.beattyIndex r) + 1 by omega]
      rw [pow_succ, pow_add]
      ring

/-- ratio `≤9/8` state から `A` は出られない。 -/
theorem nextFutureMinimum_symbol_A_impossible_of_nineEighthsBarrier
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hBarrier :
      8 * 3 ^ i ≤ 9 * 2 ^ Critical.beattyIndex i) :
    O.transitionSymbol i j ≠ .A := by
  intro hA
  have hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 :=
    (O.nextFutureMinimum_symbol_A_iff_defect_succ S hNext).1 hA
  have hOpposite :=
    O.nextFutureMinimum_defect_succ_start_oppositePowerBarrier
      S hStart hNext hRise
  have hLeft := Nat.mul_le_mul_left 4 hBarrier
  have hRight :=
    (Nat.mul_lt_mul_left (by omega : 0 < (9 : ℕ))).2 hOpposite
  omega

/--
`A` block lengthの critical margin は universal floor `log₂(4/3)` 以上。

`r=1` では equality。`r>1` では rise block の Beatty jump `+2` と
lower-mechanical cell の strict upper sideから従う。
-/
theorem nextFutureMinimum_symbol_A_logb_four_thirds_le_criticalMargin
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A) :
    Real.logb 2 ((4 : ℝ) / 3) ≤
      criticalMargin (j - i) := by
  let r : ℕ := j - i
  have hrPos : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt hNext.1
  have hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 :=
    (O.nextFutureMinimum_symbol_A_iff_defect_succ S hNext).1 hA
  have hCases :=
    O.nextFutureMinimum_defect_succ_length_eq_one_or_beattyJumpTwo
      S hStart hNext hRise
  have hCases' :
      r = 1 ∨
        Critical.beattyIndex r =
          Critical.beattyIndex (r - 1) + 2 := by
    simpa [r] using hCases
  change Real.logb 2 ((4 : ℝ) / 3) ≤ criticalMargin r
  rw [logb_two_four_div_three_eq_two_sub_logb_three]
  rcases hCases' with hrOne | hJump
  · rw [hrOne, criticalMargin_eq_beattyIndex_add_one_sub]
    rw [Critical.beattyIndex_one]
    norm_num
  · have hCell := beattyIndex_isLowerMechanical_logb_two_three (r - 1)
    change
      (Critical.beattyIndex (r - 1) : ℝ) ≤
          ((r - 1 : ℕ) : ℝ) * Real.logb 2 3 ∧
        ((r - 1 : ℕ) : ℝ) * Real.logb 2 3 <
          (Critical.beattyIndex (r - 1) : ℝ) + 1 at hCell
    have hJumpR :
        (Critical.beattyIndex r : ℝ) =
          (Critical.beattyIndex (r - 1) : ℝ) + 2 := by
      exact_mod_cast hJump
    have hrDecomp : r = (r - 1) + 1 := by omega
    have hrDecompR :
        (r : ℝ) = ((r - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hrDecomp
    rw [criticalMargin_eq_beattyIndex_add_one_sub, hJumpR, hrDecompR]
    linarith [hCell.2]

namespace FutureMinima

/--
`B` だけの selector interval では任意の scaled power barrier が保存される。
-/
theorem scaledPowerBarrier_of_B_interval
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    {p q n m : ℕ}
    (hnm : n ≤ m)
    (hBarrier :
      p * 3 ^ F.index n ≤
        q * 2 ^ Critical.beattyIndex (F.index n))
    (hB :
      ∀ t : ℕ,
        n ≤ t →
        t < m →
        O.transitionSymbol (F.index t) (F.index (t + 1)) = .B) :
    p * 3 ^ F.index m ≤
      q * 2 ^ Critical.beattyIndex (F.index m) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      exact hBarrier
  | succ m hnm ih =>
      have hPrev :
          ∀ t : ℕ,
            n ≤ t →
            t < m →
            O.transitionSymbol (F.index t) (F.index (t + 1)) = .B := by
        intro t hnt htm
        exact hB t hnt (Nat.lt_trans htm (Nat.lt_succ_self m))
      have hAtM := hB m hnm (Nat.lt_succ_self m)
      exact
        O.transitionSymbol_B_preserves_scaledPowerBarrier
          (F.index_strict (Nat.lt_succ_self m)) hAtM (ih hPrev)

/--
一般化 double-rise barrier。

`A B* A` の二個目 `A` の endpoint は、二つの `A` が隣接していなくても

`8 * 3^endpoint ≤ 9 * 2^B_endpoint`

を満たす。
-/
theorem nineEighthsBarrier_after_A_Bstar_A
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n m : ℕ}
    (hnm : n < m)
    (hAN :
      O.transitionSymbol (F.index n) (F.index (n + 1)) = .A)
    (hAM :
      O.transitionSymbol (F.index m) (F.index (m + 1)) = .A)
    (hBetween :
      ∀ t : ℕ,
        n < t →
        t < m →
        O.transitionSymbol (F.index t) (F.index (t + 1)) = .B) :
    8 * 3 ^ F.index (m + 1) ≤
      9 * 2 ^ Critical.beattyIndex (F.index (m + 1)) := by
  have hNext :
      ∀ t : ℕ,
        O.NextFutureMinimum (F.index t) (F.index (t + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard
  have hFirst :
      2 * 3 ^ F.index (n + 1) ≤
        3 * 2 ^ Critical.beattyIndex (F.index (n + 1)) :=
    O.nextFutureMinimum_symbol_A_endpoint_threeHalvesBarrier
      S (F.minimum n) (hNext n) hAN
  have hMiddle :
      2 * 3 ^ F.index m ≤
        3 * 2 ^ Critical.beattyIndex (F.index m) := by
    apply F.scaledPowerBarrier_of_B_interval
        (p := 2) (q := 3) (n := n + 1) (m := m)
        (by omega) hFirst
    intro t ht0 htm
    exact hBetween t (by omega) htm
  exact
    O.nextFutureMinimum_symbol_A_endpoint_nineEighthsBarrier_of_threeHalves
      S (F.minimum m) (hNext m) hAM hMiddle

/--
ABC language の基本禁止語：`A B* A B* A` は出現しない。

従って carry `0`=`C` を一度も挟まずに rise `A` を三回起こすことはできない。
-/
theorem not_A_Bstar_A_Bstar_A
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n m l : ℕ}
    (hnm : n < m)
    (hml : m < l)
    (hAN :
      O.transitionSymbol (F.index n) (F.index (n + 1)) = .A)
    (hAM :
      O.transitionSymbol (F.index m) (F.index (m + 1)) = .A)
    (hAL :
      O.transitionSymbol (F.index l) (F.index (l + 1)) = .A)
    (hBetweenNM :
      ∀ t : ℕ,
        n < t →
        t < m →
        O.transitionSymbol (F.index t) (F.index (t + 1)) = .B)
    (hBetweenML :
      ∀ t : ℕ,
        m < t →
        t < l →
        O.transitionSymbol (F.index t) (F.index (t + 1)) = .B) :
    False := by
  have hNext :
      ∀ t : ℕ,
        O.NextFutureMinimum (F.index t) (F.index (t + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard
  have hNine :=
    F.nineEighthsBarrier_after_A_Bstar_A
      S hStandard hnm hAN hAM hBetweenNM
  have hAtL :
      8 * 3 ^ F.index l ≤
        9 * 2 ^ Critical.beattyIndex (F.index l) := by
    apply F.scaledPowerBarrier_of_B_interval
        (p := 8) (q := 9) (n := m + 1) (m := l)
        (by omega) hNine
    intro t ht0 htl
    exact hBetweenML t (by omega) htl
  exact
    (O.nextFutureMinimum_symbol_A_impossible_of_nineEighthsBarrier
      S (F.minimum l) (hNext l) hAtL) hAL

end FutureMinima

private def abcStateBarrier
    (s : FutureMinimumABCState)
    (a : ℕ) : Prop :=
  match s with
  | .S0 => True
  | .S1 => 2 * 3 ^ a ≤ 3 * 2 ^ Critical.beattyIndex a
  | .S2 => 8 * 3 ^ a ≤ 9 * 2 ^ Critical.beattyIndex a

namespace FutureMinima

/--
標準 survivor future-minimum 列の任意有限 symbol word は三状態 automaton で読める。

proof invariant は `S1=3/2 barrier`, `S2=9/8 barrier`。
-/
private theorem symbolWord_acceptsFrom_of_stateBarrier
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (s : FutureMinimumABCState)
    (n q : ℕ)
    (hBarrier : abcStateBarrier s (F.index n)) :
    ABCAcceptsFrom s (F.symbolWord n q) := by
  have hNext :
      ∀ t : ℕ,
        O.NextFutureMinimum (F.index t) (F.index (t + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard
  induction q generalizing n s with
  | zero =>
      simp [FutureMinima.symbolWord, ABCAcceptsFrom]
  | succ q ih =>
      cases s with
      | S0 =>
          cases hSym : O.transitionSymbol (F.index n) (F.index (n + 1)) with
          | A =>
              have hNextBarrier :=
                O.nextFutureMinimum_symbol_A_endpoint_threeHalvesBarrier
                  S (F.minimum n) (hNext n) hSym
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S1) hNextBarrier
          | B =>
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S0) trivial
          | C =>
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S0) trivial
      | S1 =>
          change 2 * 3 ^ F.index n ≤
            3 * 2 ^ Critical.beattyIndex (F.index n) at hBarrier
          cases hSym : O.transitionSymbol (F.index n) (F.index (n + 1)) with
          | A =>
              have hNextBarrier :=
                O.nextFutureMinimum_symbol_A_endpoint_nineEighthsBarrier_of_threeHalves
                  S (F.minimum n) (hNext n) hSym hBarrier
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S2) hNextBarrier
          | B =>
              have hNextBarrier :=
                O.transitionSymbol_B_preserves_scaledPowerBarrier
                  (p := 2) (q := 3)
                  (F.index_strict (Nat.lt_succ_self n)) hSym hBarrier
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S1) hNextBarrier
          | C =>
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S0) trivial
      | S2 =>
          change 8 * 3 ^ F.index n ≤
            9 * 2 ^ Critical.beattyIndex (F.index n) at hBarrier
          cases hSym : O.transitionSymbol (F.index n) (F.index (n + 1)) with
          | A =>
              exact False.elim
                ((O.nextFutureMinimum_symbol_A_impossible_of_nineEighthsBarrier
                  S (F.minimum n) (hNext n) hBarrier) hSym)
          | B =>
              have hNextBarrier :=
                O.transitionSymbol_B_preserves_scaledPowerBarrier
                  (p := 8) (q := 9)
                  (F.index_strict (Nat.lt_succ_self n)) hSym hBarrier
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S2) hNextBarrier
          | C =>
              simp only [symbolWord, hSym, ABCAcceptsFrom, FutureMinimumABCState.step]
              exact ih (n := n + 1) (s := .S0) trivial

/-- 標準 survivor future-minimum の任意有限 ABC word は automaton-admissible。 -/
theorem symbolWord_ABCAdmissible
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ABCAdmissible (F.symbolWord n q) := by
  exact
    F.symbolWord_acceptsFrom_of_stateBarrier
      S hStandard .S0 n q trivial

/--
任意有限 future-minimum word で rise 数と recharge 数は

`#A ≤ 2 #C + 2`

を満たす。
-/
theorem symbolWord_count_A_le_two_count_C_add_two
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    (F.symbolWord n q).count .A ≤
      2 * (F.symbolWord n q).count .C + 2 := by
  exact
    (F.symbolWord_ABCAdmissible S hStandard n q).count_A_le_two_count_C_add_two

/--
非減少 defect 区間では `δ_end-δ_start=#A` と前定理を合成し、

defect growth `≤ 2 #C + 2`

を得る。
-/
theorem defect_end_le_start_add_two_count_C_add_two_of_nondec
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q : ℕ}
    (hNondec :
      ∀ t : ℕ,
        n ≤ t →
        t < n + q →
        infiniteSurvivorDefect O.exponent (F.index t) ≤
          infiniteSurvivorDefect O.exponent (F.index (t + 1))) :
    infiniteSurvivorDefect O.exponent (F.index (n + q)) ≤
      infiniteSurvivorDefect O.exponent (F.index n) +
        2 * (F.symbolWord n q).count .C + 2 := by
  have hExact :=
    F.defect_end_eq_start_add_count_A_of_nondec
      S hStandard hNondec
  have hCount :=
    F.symbolWord_count_A_le_two_count_C_add_two S hStandard n q
  omega

/-- subtraction 版：`δ_end - δ_start ≤ 2#C+2`。 -/
theorem defect_sub_le_two_count_C_add_two_of_nondec
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q : ℕ}
    (hNondec :
      ∀ t : ℕ,
        n ≤ t →
        t < n + q →
        infiniteSurvivorDefect O.exponent (F.index t) ≤
          infiniteSurvivorDefect O.exponent (F.index (t + 1))) :
    infiniteSurvivorDefect O.exponent (F.index (n + q)) -
        infiniteSurvivorDefect O.exponent (F.index n) ≤
      2 * (F.symbolWord n q).count .C + 2 := by
  have h :=
    F.defect_end_le_start_add_two_count_C_add_two_of_nondec
      S hStandard hNondec
  omega

end FutureMinima
end OddOrbit
end Collatz3
