import CollatzLean.CollatzSecondLayer3.FutureMinimumAllLengths
import CollatzLean.CollatzSecondLayer3.SpecialC3IntervalSubsequence
import CollatzLean.CollatzSupport.CofinalSelection

import Mathlib.Data.Finset.Basic

/-!
# 全長さ系におけるConstant terminal obstructionとterminal escape

固定future-minimumから全長さ`q + 1`を同時に見る。
任意に長いwindowでterminal timeが固定有限prefix内に残るなら、
deep lower replayは開始値の指数的下界により排除される。
したがって十分長いそのようなterminalはSpecial C3である。

terminal timeは有限集合に入るため、cofinal定数部分列を抽出できる。
よってConstant terminal Special C3 familyを排除すれば、
全長さのterminal timeは任意の固定時刻を最終的に越える。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumAllLengthTerminalData

/-- anchorから固定時刻`t`までのactual値を全て支配する有限上界。 -/
def prefixValueBound
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (t : ℕ) : ℕ :=
  Finset.sum (Finset.range (t + 1))
    (fun k => O.value (A.anchor + k))

/-- 固定prefix内のactual値は`prefixValueBound`以下。 -/
theorem value_le_prefixValueBound
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (t s : ℕ)
    (hs : s ≤ t) :
    O.value (A.anchor + s) ≤ A.prefixValueBound t := by
  unfold prefixValueBound
  exact
    Finset.single_le_sum
      (fun k (_hk : k ∈ Finset.range (t + 1)) =>
        Nat.zero_le (O.value (A.anchor + k)))
      (Finset.mem_range.mpr (by omega))

/-- `n < 2^(n+1)`。有限prefix上界とdeep下界を分離する。 -/
private theorem nat_lt_twoPow_succ_allLength (n : ℕ) :
    n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ (n + 1) :=
        Nat.pow_pos (by omega)
      omega

/-- deep lower replayの開始値はresidue modulus以上。 -/
theorem deep_residueModulus_le_startValue
    {O : OddOrbit}
    {start length : ℕ}
    (D : GenericDeepLowerReplayAt O start length) :
    residueModulus (O.segmentWord start length) ≤ O.value start := by
  have hstart := D.lowerReplay.start_step
  omega

/-- deep terminalの開始値は`2^(length+1)`以上。 -/
theorem deep_twoPow_length_succ_le_startValue
    {O : OddOrbit}
    {start length : ℕ}
    (D : GenericDeepLowerReplayAt O start length) :
    2 ^ (length + 1) ≤ O.value start := by
  exact le_trans D.modulus_deep (deep_residueModulus_le_startValue D)

/--
terminal timeが`t`以下で、index `q`がprefix上界以上ならdeep terminalは不可能。
したがってbounded terminal timeを持つ十分長いwindowはSpecial C3へ強制される。
-/
theorem deep_impossible_of_terminalTime_le_of_largeIndex
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (t q : ℕ)
    (hq : A.prefixValueBound t ≤ q)
    (hterminal : A.terminalTime q ≤ t)
    (D : GenericDeepLowerReplayAt O (A.terminalStart q) (A.length q)) :
    False := by
  let B := A.prefixValueBound t
  have hvalueLe :
      O.value (A.terminalStart q) ≤ B := by
    simpa [terminalStart] using
      A.value_le_prefixValueBound t (A.terminalTime q) hterminal
  have hpowLe :
      2 ^ (A.length q + 1) ≤ O.value (A.terminalStart q) :=
    deep_twoPow_length_succ_le_startValue D
  have hBltBase : B < 2 ^ (B + 1) :=
    nat_lt_twoPow_succ_allLength B
  have hexponentLe : B + 1 ≤ A.length q + 1 := by
    dsimp [B]
    unfold length
    omega
  have hBlt : B < 2 ^ (A.length q + 1) :=
    lt_of_lt_of_le hBltBase
      (Nat.pow_le_pow_right (by omega) hexponentLe)
  omega

/--
全長さ系から抽出されるConstant terminal Special C3 family。
全seedは同じactual start `anchor + terminal` を持ち、lengthだけが狭義増加する。
-/
structure ConstantTerminalSpecialC3FamilyData
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O) where
  terminal : ℕ
  select : ℕ → ℕ
  select_strict : StrictMono select
  terminal_eq : ∀ n : ℕ, A.terminalTime (select n) = terminal
  special : ∀ n : ℕ, A.IsSpecial (select n)

namespace ConstantTerminalSpecialC3FamilyData

/-- Constant familyのactual terminal startは全項で同じ。 -/
theorem terminalStart_eq
    {O : OddOrbit}
    {A : FutureMinimumAllLengthTerminalData O}
    (F : ConstantTerminalSpecialC3FamilyData A)
    (n : ℕ) :
    A.terminalStart (F.select n) = A.anchor + F.terminal := by
  unfold FutureMinimumAllLengthTerminalData.terminalStart
  rw [F.terminal_eq n]

/-- Constant familyのwindow長は狭義増加。 -/
theorem length_strict
    {O : OddOrbit}
    {A : FutureMinimumAllLengthTerminalData O}
    (F : ConstantTerminalSpecialC3FamilyData A) :
    StrictMono (fun n => A.length (F.select n)) := by
  intro a b hab
  unfold FutureMinimumAllLengthTerminalData.length
  dsimp only
  have hs := F.select_strict hab
  omega

end ConstantTerminalSpecialC3FamilyData

/-- terminal timeが任意の固定時刻を最終的に越える性質。 -/
def TerminalTimeEscapes
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O) : Prop :=
  ∀ t : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → t < A.terminalTime q

/--
Constant terminal familyが存在しなければ、全長さterminal timeは無限遠へ逃げる。

証明：escape失敗ならbounded terminal timeを持つqがcofinalに存在する。
十分大きいqではdeep lower replayが指数的開始値下界により不可能なのでSpecial C3。
そのcofinal列上のterminal timeは固定`t`以下であり、自然数列部分列分類の
increasing枝は`t + 1`番目で矛盾する。従ってconstant枝が残る。
-/
theorem terminalTime_escapes_of_no_constant
    {O : OddOrbit}
    (A : FutureMinimumAllLengthTerminalData O)
    (hNoConstant :
      ¬ Nonempty (ConstantTerminalSpecialC3FamilyData A)) :
    A.TerminalTimeEscapes := by
  classical
  intro t
  by_contra hNoEscape
  push Not at hNoEscape
  let P : ℕ → Prop :=
    fun q => A.terminalTime q ≤ t ∧ A.IsSpecial q
  have hP : Cofinally P := by
    intro N
    let Q := max N (A.prefixValueBound t)
    obtain ⟨q, hqQ, hqTerminal⟩ := hNoEscape Q
    have hqN : N ≤ q :=
      le_trans (le_max_left N (A.prefixValueBound t)) hqQ
    have hqLarge : A.prefixValueBound t ≤ q :=
      le_trans (le_max_right N (A.prefixValueBound t)) hqQ
    have hSpecial : A.IsSpecial q := by
      rcases A.terminal_deep_or_special q with hDeep | hSpecial
      · rcases hDeep with ⟨D⟩
        exact False.elim
          (A.deep_impossible_of_terminalTime_le_of_largeIndex
            t q hqLarge hqTerminal D)
      · exact hSpecial
    exact ⟨q, hqN, hqTerminal, hSpecial⟩
  let s : ℕ → ℕ := Cofinally.select P hP
  have hsStrict : StrictMono s :=
    Cofinally.select_strict P hP
  have hsSpec : ∀ n : ℕ, P (s n) := by
    intro n
    exact Cofinally.select_spec P hP n
  rcases
      natSequence_constant_or_increasing_subsequence
        (fun n => A.terminalTime (s n)) with
    hConst | hInc
  · rcases hConst with ⟨C⟩
    apply hNoConstant
    refine ⟨{
      terminal := C.value
      select := fun n => s (C.select n)
      select_strict := hsStrict.comp C.select_strict
      terminal_eq := ?_
      special := ?_
    }⟩
    · intro n
      exact C.value_eq n
    · intro n
      exact (hsSpec (C.select n)).2
  · rcases hInc with ⟨I⟩
    have hBound :
        A.terminalTime (s (I.select (t + 1))) ≤ t :=
      (hsSpec (I.select (t + 1))).1
    have hLarge :
        t + 1 ≤ A.terminalTime (s (I.select (t + 1))) := by
      exact
        nat_le_strictMono_apply
          (fun n => A.terminalTime (s (I.select n)))
          I.value_strict
          (t + 1)
    omega

end FutureMinimumAllLengthTerminalData
end CollatzSecondLayer3
