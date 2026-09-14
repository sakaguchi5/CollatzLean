import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumRigidity
import CollatzLean.Collatz3.Semantics.StandardFutureMinimum
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: future-minimum transition の ABC 記号化

非減少 defect transition に現れる三型

* `A = (carry, excess) = (1,0)` : rise,
* `B = (carry, excess) = (1,1)` : contracting flat,
* `C = (carry, excess) = (0,0)` : recharge flat

を三文字で読むための最小語彙を導入する。

primitive data は三文字 `FutureMinimumABC` と、既存の `carry / excess` から文字を読む
`transitionSymbol`、および標準 future-minimum 列から作る有限 `symbolWord / lengthWord` だけ。

defect 変化、三型完全分類、critical-margin の有限 telescope はすべて derived theorem とする。

`transitionSymbol` 自体は defect 非減少を仮定しない total coding であり、

* carry `0` は常に `C`,
* carry `1`, excess `0` は `A`,
* carry `1`, positive excess は `B`

と読む。非減少区間では既存の三型分類により `B` の excess は exact `1`、
`C` の excess は exact `0` になる。
-/

namespace Collatz3
namespace Bridge

/-- 標準 future-minimum transition を読む三文字。 -/
inductive FutureMinimumABC where
  | A
  | B
  | C
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

end Bridge

namespace OddOrbit

open Bridge

/--
既存の Beatty carry / segment excess から一文字を読む total coding。

非減少性は definition に入れず、三型としての意味は derived theorem 側で与える。
-/
def transitionSymbol
    (O : Collatz3.OddOrbit)
    (i j : ℕ) : FutureMinimumABC :=
  if Critical.beattyCarry i (j - i) = 0 then
    .C
  else if O.segmentBeattyExcess i (j - i) = 0 then
    .A
  else
    .B

/-- `C` は carry `0` と exact に同値。 -/
theorem transitionSymbol_eq_C_iff
    (O : Collatz3.OddOrbit)
    (i j : ℕ) :
    O.transitionSymbol i j = .C ↔
      Critical.beattyCarry i (j - i) = 0 := by
  rcases Critical.beattyCarry_eq_zero_or_one i (j - i) with h0 | h1
  · simp [transitionSymbol, h0]
  · by_cases hEx : O.segmentBeattyExcess i (j - i) = 0
    · simp [transitionSymbol, h1, hEx]
    · simp [transitionSymbol, h1, hEx]

/-- `A` は `(carry, excess)=(1,0)` と exact に同値。 -/
theorem transitionSymbol_eq_A_iff
    (O : Collatz3.OddOrbit)
    (i j : ℕ) :
    O.transitionSymbol i j = .A ↔
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 0 := by
  rcases Critical.beattyCarry_eq_zero_or_one i (j - i) with h0 | h1
  · simp [transitionSymbol, h0]
  · simp [transitionSymbol, h1]

/-- `B` は carry `1` かつ positive excess と exact に同値。 -/
theorem transitionSymbol_eq_B_iff
    (O : Collatz3.OddOrbit)
    (i j : ℕ) :
    O.transitionSymbol i j = .B ↔
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) ≠ 0 := by
  rcases Critical.beattyCarry_eq_zero_or_one i (j - i) with h0 | h1
  · simp [transitionSymbol, h0]
  · simp [transitionSymbol, h1]

/-- survivor 上の next-future-minimum transition では `A` と defect `+1` が exact に同値。 -/
theorem nextFutureMinimum_symbol_A_iff_defect_succ
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    O.transitionSymbol i j = .A ↔
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 := by
  rw [O.transitionSymbol_eq_A_iff i j]
  exact (O.nextFutureMinimum_defect_eq_succ_iff S hNext).symm

/--
非減少 next-future-minimum transition は exact に `A/B/C` 三型のどれか。

ここで `A` だけが defect `+1`、`B,C` は defect flat。
-/
theorem nextFutureMinimum_nondec_ABC_cases
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hNondec :
      infiniteSurvivorDefect O.exponent i ≤
        infiniteSurvivorDefect O.exponent j) :
    (O.transitionSymbol i j = .A ∧
        infiniteSurvivorDefect O.exponent j =
          infiniteSurvivorDefect O.exponent i + 1) ∨
      (O.transitionSymbol i j = .B ∧
        infiniteSurvivorDefect O.exponent j =
          infiniteSurvivorDefect O.exponent i) ∨
      (O.transitionSymbol i j = .C ∧
        infiniteSurvivorDefect O.exponent j =
          infiniteSurvivorDefect O.exponent i) := by
  rcases O.nextFutureMinimum_nondec_three_cases S hNext hNondec with
    hC | hA | hB
  · right
    right
    refine ⟨(O.transitionSymbol_eq_C_iff i j).2 hC.1, hC.2.2⟩
  · left
    refine ⟨(O.transitionSymbol_eq_A_iff i j).2 ⟨hA.1, hA.2.1⟩, hA.2.2⟩
  · right
    left
    have hExcessNe : O.segmentBeattyExcess i (j - i) ≠ 0 := by
      omega
    refine ⟨(O.transitionSymbol_eq_B_iff i j).2 ⟨hB.1, hExcessNe⟩, hB.2.2⟩

/-- 非減少 transition の `B` は exact `(carry,excess)=(1,1)`。 -/
theorem nextFutureMinimum_symbol_B_iff_one_one_of_nondec
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hNondec :
      infiniteSurvivorDefect O.exponent i ≤
        infiniteSurvivorDefect O.exponent j) :
    O.transitionSymbol i j = .B ↔
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1 := by
  constructor
  · intro hB
    have hRaw := (O.transitionSymbol_eq_B_iff i j).1 hB
    have hBalance := O.nextFutureMinimum_defect_balance S hNext
    have hExcessPos : 0 < O.segmentBeattyExcess i (j - i) := by
      omega
    constructor
    · exact hRaw.1
    · omega
  · rintro ⟨hCarry, hExcess⟩
    apply (O.transitionSymbol_eq_B_iff i j).2
    exact ⟨hCarry, by omega⟩

/-- 非減少 transition の `C` は exact `(carry,excess)=(0,0)`。 -/
theorem nextFutureMinimum_symbol_C_iff_zero_zero_of_nondec
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hNondec :
      infiniteSurvivorDefect O.exponent i ≤
        infiniteSurvivorDefect O.exponent j) :
    O.transitionSymbol i j = .C ↔
      Critical.beattyCarry i (j - i) = 0 ∧
        O.segmentBeattyExcess i (j - i) = 0 := by
  constructor
  · intro hC
    have hCarry := (O.transitionSymbol_eq_C_iff i j).1 hC
    have hBalance := O.nextFutureMinimum_defect_balance S hNext
    exact ⟨hCarry, by omega⟩
  · rintro ⟨hCarry, _hExcess⟩
    exact (O.transitionSymbol_eq_C_iff i j).2 hCarry

namespace FutureMinima

/-- selector position `n` から `q` transitions を三文字で読む有限 word。 -/
def symbolWord
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (n : ℕ) : ℕ → List FutureMinimumABC
  | 0 => []
  | q + 1 =>
      O.transitionSymbol (F.index n) (F.index (n + 1)) ::
        symbolWord F (n + 1) q

/-- 同じ有限 transition 区間の actual block lengths。 -/
def lengthWord
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | q + 1 =>
      (F.index (n + 1) - F.index n) ::
        lengthWord F (n + 1) q

@[simp] theorem symbolWord_length
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (n q : ℕ) :
    (F.symbolWord n q).length = q := by
  induction q generalizing n with
  | zero => simp [symbolWord]
  | succ q ih => simp [symbolWord, ih]

@[simp] theorem lengthWord_length
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (n q : ℕ) :
    (F.lengthWord n q).length = q := by
  induction q generalizing n with
  | zero => simp [lengthWord]
  | succ q ih => simp [lengthWord, ih]

/--
非減少 defect の有限 ABC word では、defect 増加量は `A` の個数そのもの。

`δ_end = δ_start + #A`。
-/
theorem defect_end_eq_start_add_count_A_of_nondec
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
    infiniteSurvivorDefect O.exponent (F.index (n + q)) =
      infiniteSurvivorDefect O.exponent (F.index n) +
        (F.symbolWord n q).count .A := by
  have hNext :
      ∀ t : ℕ,
        O.NextFutureMinimum (F.index t) (F.index (t + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard
  induction q generalizing n with
  | zero =>
      simp [symbolWord]
  | succ q ih =>
      have hNd0 :
          infiniteSurvivorDefect O.exponent (F.index n) ≤
            infiniteSurvivorDefect O.exponent (F.index (n + 1)) :=
        hNondec n (by omega) (by omega)
      have hTail :
          ∀ t : ℕ,
            n + 1 ≤ t →
            t < n + 1 + q →
            infiniteSurvivorDefect O.exponent (F.index t) ≤
              infiniteSurvivorDefect O.exponent (F.index (t + 1)) := by
        intro t ht0 htq
        exact hNondec t (by omega) (by omega)
      have hIH := ih (n := n + 1) hTail
      have hIH' :
          infiniteSurvivorDefect O.exponent (F.index (n + (q + 1))) =
            infiniteSurvivorDefect O.exponent (F.index (n + 1)) +
              (F.symbolWord (n + 1) q).count .A := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIH
      rcases O.nextFutureMinimum_nondec_ABC_cases S (hNext n) hNd0 with
        hA | hB | hC
      · simp only [symbolWord, hA.1, List.count_cons_self]
        omega
      · simp only [symbolWord, hB.1]
        rw [List.count_cons_of_ne (by decide : FutureMinimumABC.B ≠ .A)]
        omega
      · simp only [symbolWord, hC.1]
        rw [List.count_cons_of_ne (by decide : FutureMinimumABC.C ≠ .A)]
        omega

/--
任意の有限 ABC word に対する critical-margin の exact telescope。

`C` は carry `0` なので一回ごとに margin cocycle の `-1` wrap を起こす。
従って

`#C = Σ μ(blockLength) + μ(startIndex) - μ(endIndex)`。

この identity 自体には survivor / defect 非減少性は不要。
-/
theorem count_C_eq_margin_sum_add_start_sub_end
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (n q : ℕ) :
    ((F.symbolWord n q).count .C : ℝ) =
      ((F.lengthWord n q).map criticalMargin).sum +
        criticalMargin (F.index n) -
        criticalMargin (F.index (n + q)) := by
  induction q generalizing n with
  | zero =>
      simp [symbolWord, lengthWord]
  | succ q ih =>
      let i : ℕ := F.index n
      let j : ℕ := F.index (n + 1)
      let r : ℕ := j - i
      have hij : i < j := by
        dsimp [i, j]
        exact F.index_strict (Nat.lt_succ_self n)
      have hIndex : i + r = j := by
        dsimp [r]
        exact Nat.add_sub_of_le (Nat.le_of_lt hij)
      have hAdd := criticalMargin_add_eq i r
      rw [hIndex] at hAdd
      have hIH := ih (n := n + 1)
      have hIH' :
          ((F.symbolWord (n + 1) q).count .C : ℝ) =
            ((F.lengthWord (n + 1) q).map criticalMargin).sum +
              criticalMargin j -
              criticalMargin (F.index (n + (q + 1))) := by
        simpa [j, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIH
      cases hSym : O.transitionSymbol i j with
      | A =>
          have hCarry : Critical.beattyCarry i r = 1 := by
            have h := (O.transitionSymbol_eq_A_iff i j).1 hSym
            simpa [r] using h.1
          rw [hCarry] at hAdd
          norm_num at hAdd
          simp [symbolWord, lengthWord, i, j, hSym]
          linarith
      | B =>
          have hCarry : Critical.beattyCarry i r = 1 := by
            have h := (O.transitionSymbol_eq_B_iff i j).1 hSym
            simpa [r] using h.1
          rw [hCarry] at hAdd
          norm_num at hAdd
          simp [symbolWord, lengthWord, i, j, hSym]
          linarith
      | C =>
          have hCarry : Critical.beattyCarry i r = 0 := by
            have h := (O.transitionSymbol_eq_C_iff i j).1 hSym
            simpa [r] using h
          rw [hCarry] at hAdd
          norm_num at hAdd
          simp [symbolWord, lengthWord, i, j, hSym]
          linarith

end FutureMinima
end OddOrbit
end Collatz3
