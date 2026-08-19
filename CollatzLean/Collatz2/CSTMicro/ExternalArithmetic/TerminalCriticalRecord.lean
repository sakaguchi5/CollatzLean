import CollatzLean.Collatz2.Geometry.CriticalCarry
import CollatzLean.Collatz2.Geometry.BestUpperSlope
import CollatzLean.Collatz2.Geometry.PrimitiveBestUpper
import CollatzLean.Collatz2.Geometry.PrimitiveReducedChristoffelBridge
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.CriticalBoundaryExtraDepth
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Terminal critical records

minimal B の terminal critical suffix で使う、current-A 非依存の pure record 幾何。

`criticalCarry s r = 1` が初めて起こる `r` を一つの record piece とする。
この定義から

* proper local phase は origin critical phase と exact に一致する、
* terminal だけ carry が 1、
* record piece の upper pair は smaller denominator に対する best upper、
* 従って StripReduced、

を導く。

さらに任意の finite intervalは first-carry record pieces と最後の no-carry fragment に
有限分解できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- Beatty index と odd-only critical height の 0 を含む統一版。 -/
theorem beattyIndex_eq_wordCriticalHeight_all (n : ℕ) :
    beattyIndex n = Collatz2.Word.criticalHeight n := by
  by_cases hn : n = 0
  · subst n
    simp
  · exact beattyIndex_eq_wordCriticalHeight (Nat.pos_of_ne_zero hn)

/-- critical carry を Beatty index で読む exact formula。 -/
theorem beattyIndex_add_eq_add_carry (a b : ℕ) :
    beattyIndex (a + b) =
      beattyIndex a + beattyIndex b + Collatz2.Word.criticalCarry a b := by
  simpa only [beattyIndex_eq_wordCriticalHeight_all] using
    Collatz2.Word.criticalHeight_add_eq a b

/-- 一つの first-carry record piece。 -/
structure CriticalRecordPiece (start length : ℕ) : Prop where
  length_pos : 0 < length
  before_noCarry :
    ∀ j : ℕ, 0 < j → j < length →
      Collatz2.Word.criticalCarry start j = 0
  terminal_carry :
    Collatz2.Word.criticalCarry start length = 1

/-- 最後に残る、interval 内で carry が一度も起きない fragment。 -/
structure CriticalNoCarryFragment (start length : ℕ) : Prop where
  noCarry :
    ∀ j : ℕ, 0 < j → j ≤ length →
      Collatz2.Word.criticalCarry start j = 0

/--
`[start,start+remaining)` の canonical first-carry decomposition。
`step` は一つの first-carry record、`final` は高々一つの no-carry fragment。
-/
inductive CriticalRecordChain : ℕ → ℕ → Type
  | final {start remaining : ℕ}
      (fragment : CriticalNoCarryFragment start remaining) :
      CriticalRecordChain start remaining
  | step {start remaining r : ℕ}
      (r_pos : 0 < r)
      (r_le : r ≤ remaining)
      (piece : CriticalRecordPiece start r)
      (tail : CriticalRecordChain (start + r) (remaining - r)) :
      CriticalRecordChain start remaining

namespace CriticalRecordChain

/-- record lengths。final no-carry fragment は含めない。 -/
def recordLengths
    {start remaining : ℕ}
    (C : CriticalRecordChain start remaining) : List ℕ :=
  match C with
  | .final _ => []
  | .step (r := r) _ _ _ tail => r :: tail.recordLengths

/-- record 個数。 -/
def recordCount
    {start remaining : ℕ}
    (C : CriticalRecordChain start remaining) : ℕ :=
  C.recordLengths.length

/-- 最後の no-carry fragment の長さ。 -/
def finalLength
    {start remaining : ℕ}
    (C : CriticalRecordChain start remaining) : ℕ :=
  match C with
  | .final _ => remaining
  | .step _ _ _ tail => tail.finalLength

/-- record lengths と final fragment は元 interval を exact に覆う。 -/
theorem recordLengths_sum_add_finalLength_eq
    {start remaining : ℕ}
    (C : CriticalRecordChain start remaining) :
    C.recordLengths.sum + C.finalLength = remaining := by
  induction C with
  | final fragment =>
      simp [recordLengths, finalLength]
  | @step start remaining r hrPos hrLe piece tail ih =>
      simp only [recordLengths, List.sum_cons, finalLength]
      rw [Nat.add_assoc, ih]
      omega

/-- record 個数の再帰式。 -/
@[simp] theorem recordCount_step
    {start remaining r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ remaining)
    (piece : CriticalRecordPiece start r)
    (tail : CriticalRecordChain (start + r) (remaining - r)) :
    (CriticalRecordChain.step hrPos hrLe piece tail).recordCount =
      tail.recordCount + 1 := by
  simp [recordCount, recordLengths]

@[simp] theorem recordCount_final
    {start remaining : ℕ}
    (fragment : CriticalNoCarryFragment start remaining) :
    (CriticalRecordChain.final fragment).recordCount = 0 := by
  simp [recordCount, recordLengths]

end CriticalRecordChain

/--
任意有限 interval は first-carry records と final no-carry fragment に分解できる。
最初の carry は `Nat.find` で取り、残長が strict に減るので strong induction で停止する。
-/
theorem exists_criticalRecordChain
    (start remaining : ℕ) :
    Nonempty (CriticalRecordChain start remaining) := by
  induction remaining using Nat.strong_induction_on generalizing start with
  | h n ih =>
      by_cases hCarry :
          ∃ r : ℕ,
            0 < r ∧ r ≤ n ∧ Collatz2.Word.criticalCarry start r = 1
      · let r : ℕ := Nat.find hCarry
        have hrSpec :
            0 < r ∧ r ≤ n ∧ Collatz2.Word.criticalCarry start r = 1 := by
          simpa [r] using Nat.find_spec hCarry
        have hBefore :
            ∀ j : ℕ, 0 < j → j < r →
              Collatz2.Word.criticalCarry start j = 0 := by
          intro j hjPos hjLt
          rcases Collatz2.Word.criticalCarry_eq_zero_or_one start j with h0 | h1
          · exact h0
          · have hjWitness :
                0 < j ∧ j ≤ n ∧ Collatz2.Word.criticalCarry start j = 1 := by
              exact ⟨hjPos, by omega, h1⟩
            have hMin : r ≤ j := by
              simpa [r] using Nat.find_min' hCarry hjWitness
            omega
        have hRemLt : n - r < n := by
          omega
        obtain ⟨tail⟩ := ih (n - r) hRemLt (start + r)
        exact ⟨CriticalRecordChain.step
          hrSpec.1 hrSpec.2.1
          ⟨hrSpec.1, hBefore, hrSpec.2.2⟩
          tail⟩
      · have hNo : CriticalNoCarryFragment start n := by
          refine ⟨?_⟩
          intro j hjPos hjLe
          rcases Collatz2.Word.criticalCarry_eq_zero_or_one start j with h0 | h1
          · exact h0
          · exact False.elim (hCarry ⟨j, hjPos, hjLe, h1⟩)
        exact ⟨CriticalRecordChain.final hNo⟩

namespace CriticalRecordPiece

/-- proper offset では shifted Beatty phase が origin phaseと exact に一致。 -/
theorem local_beatty_eq
    {start r i : ℕ}
    (P : CriticalRecordPiece start r)
    (hi : i < r) :
    beattyIndex (start + i) - beattyIndex start = beattyIndex i := by
  by_cases hi0 : i = 0
  · subst i
    simp
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hCarry := P.before_noCarry i hiPos hi
    have hAdd := beattyIndex_add_eq_add_carry start i
    rw [hCarry, Nat.add_zero] at hAdd
    omega

/-- terminal offset だけは Beatty carry が exact に一つ入る。 -/
theorem terminal_beatty_eq
    {start r : ℕ}
    (P : CriticalRecordPiece start r) :
    beattyIndex (start + r) - beattyIndex start = beattyIndex r + 1 := by
  have hAdd := beattyIndex_add_eq_add_carry start r
  rw [P.terminal_carry] at hAdd
  omega

/-- `Ico a (a+n)` を local offset rangeへ移す public helper。 -/
theorem sum_Ico_eq_sum_range_add
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    (a n : ℕ) :
    Finset.sum (Finset.Ico a (a + n)) f =
      Finset.sum (Finset.range n) (fun i => f (a + i)) := by
  classical
  symm
  refine Finset.sum_bij (fun i _ => a + i) ?_ ?_ ?_ ?_
  · intro i hi
    have hiLt : i < n := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i₁ hi₁ i₂ hi₂ hEq
    omega
  · intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    refine ⟨k - a, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro i hi
    rfl

/-- `Ico a b` を length `b-a` の offset rangeへ移す public helper。 -/
theorem sum_Ico_eq_sum_range_sub_public
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    {a b : ℕ}
    (hab : a ≤ b) :
    Finset.sum (Finset.Ico a b) f =
      Finset.sum (Finset.range (b - a)) (fun i => f (a + i)) := by
  classical
  symm
  refine Finset.sum_bij (fun i _ => a + i) ?_ ?_ ?_ ?_
  · intro i hi
    have hiLt : i < b - a := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i₁ hi₁ i₂ hi₂ hEq
    omega
  · intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    refine ⟨k - a, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro i hi
    rfl

/--
first-carry record の local critical numerator は origin critical numeratorそのもの。
長さだけではなく、全 proper local Beatty exponents が一致することを使う。
-/
theorem intervalPhi_eq_prefixPhi
    {start r : ℕ}
    (P : CriticalRecordPiece start r) :
    criticalIntervalPhiZ start (start + r) =
      criticalPrefixPhiZ r := by
  classical
  unfold criticalIntervalPhiZ criticalPrefixPhiZ
  rw [sum_Ico_eq_sum_range_add
    (fun k =>
      (2 : ℤ) ^ (beattyIndex k - beattyIndex start) *
        (3 : ℤ) ^ (start + r - 1 - k)) start r]
  apply Finset.sum_congr rfl
  intro i hiMem
  have hi : i < r := Finset.mem_range.mp hiMem
  have hBeta := P.local_beatty_eq hi
  have hThree :
      start + r - 1 - (start + i) = r - 1 - i := by
    omega
  rw [hBeta, hThree]

end CriticalRecordPiece

namespace CriticalNoCarryFragment

/-- no-carry fragment では endpoint を含む全 local Beatty phase が origin と一致。 -/
theorem local_beatty_eq
    {start r i : ℕ}
    (F : CriticalNoCarryFragment start r)
    (hi : i ≤ r) :
    beattyIndex (start + i) - beattyIndex start = beattyIndex i := by
  by_cases hi0 : i = 0
  · subst i
    simp
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hCarry := F.noCarry i hiPos hi
    have hAdd := beattyIndex_add_eq_add_carry start i
    rw [hCarry, Nat.add_zero] at hAdd
    omega

/-- no-carry fragment の endpoint rise。 -/
theorem terminal_beatty_eq
    {start r : ℕ}
    (F : CriticalNoCarryFragment start r) :
    beattyIndex (start + r) - beattyIndex start = beattyIndex r := by
  by_cases hr0 : r = 0
  · subst r
    simp
  · exact F.local_beatty_eq le_rfl

/-- no-carry fragment の local numerator も origin critical numerator。 -/
theorem intervalPhi_eq_prefixPhi
    {start r : ℕ}
    (F : CriticalNoCarryFragment start r) :
    criticalIntervalPhiZ start (start + r) = criticalPrefixPhiZ r := by
  classical
  unfold criticalIntervalPhiZ criticalPrefixPhiZ
  rw [CriticalRecordPiece.sum_Ico_eq_sum_range_add
    (fun k =>
      (2 : ℤ) ^ (beattyIndex k - beattyIndex start) *
        (3 : ℤ) ^ (start + r - 1 - k)) start r]
  apply Finset.sum_congr rfl
  intro i hiMem
  have hi : i < r := Finset.mem_range.mp hiMem
  have hBeta := F.local_beatty_eq (Nat.le_of_lt hi)
  have hThree : start + r - 1 - (start + i) = r - 1 - i := by omega
  rw [hBeta, hThree]

end CriticalNoCarryFragment

/-- critical logarithmic phase `n log 3 - beta_n log 2`。 -/
noncomputable def criticalRealPhase (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log 3 - (beattyIndex n : ℝ) * Real.log 2

/-- upper error `(beta_n+1)log2 - n log3 = log2 - phase(n)`。 -/
noncomputable def criticalUpperError (n : ℕ) : ℝ :=
  ((beattyIndex n + 1 : ℕ) : ℝ) * Real.log 2 -
    (n : ℝ) * Real.log 3

/-- `log 2` は正。 -/
theorem real_log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

/-- critical phase は非負。 -/
theorem criticalRealPhase_nonneg (n : ℕ) :
    0 ≤ criticalRealPhase n := by
  have hPowNat := beattyIndex_lower n
  have hPow :
      (2 : ℝ) ^ beattyIndex n ≤ (3 : ℝ) ^ n := by
    exact_mod_cast hPowNat
  have hLog :=
    Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ beattyIndex n) hPow
  rw [Real.log_pow, Real.log_pow] at hLog
  unfold criticalRealPhase
  nlinarith

/-- Beatty upper inequality は常に strict。 -/
theorem threePow_lt_twoPow_beatty_succ (n : ℕ) :
    3 ^ n < 2 ^ (beattyIndex n + 1) := by
  have hLe := beattyIndex_upper n
  have hNe : 3 ^ n ≠ 2 ^ (beattyIndex n + 1) := by
    intro hEq
    have hOdd : Odd (3 ^ n) :=
      (show Odd (3 : ℕ) by decide).pow
    rcases hOdd with ⟨a, ha⟩
    have hEven :
        ∃ b : ℕ, 2 ^ (beattyIndex n + 1) = 2 * b := by
      refine ⟨2 ^ beattyIndex n, ?_⟩
      rw [pow_succ]
      ring
    rcases hEven with ⟨b, hb⟩
    rw [ha, hb] at hEq
    omega
  exact lt_of_le_of_ne hLe hNe

/-- critical phase は `log 2` 未満。 -/
theorem criticalRealPhase_lt_log_two (n : ℕ) :
    criticalRealPhase n < Real.log 2 := by
  have hPowNat := threePow_lt_twoPow_beatty_succ n
  have hPow :
      (3 : ℝ) ^ n < (2 : ℝ) ^ (beattyIndex n + 1) := by
    exact_mod_cast hPowNat
  have hLog :=
    Real.log_lt_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ n) hPow
  rw [Real.log_pow, Real.log_pow] at hLog
  unfold criticalRealPhase
  push_cast at hLog ⊢
  nlinarith

/-- upper error は `log2 - phase`。 -/
theorem criticalUpperError_eq_log_two_sub_phase (n : ℕ) :
    criticalUpperError n = Real.log 2 - criticalRealPhase n := by
  unfold criticalUpperError criticalRealPhase
  push_cast
  ring

/-- upper error は strict positive。 -/
theorem criticalUpperError_pos (n : ℕ) :
    0 < criticalUpperError n := by
  rw [criticalUpperError_eq_log_two_sub_phase]
  exact sub_pos.mpr (criticalRealPhase_lt_log_two n)

/-- phase の exact carry law。 -/
theorem criticalRealPhase_add
    (a b : ℕ) :
    criticalRealPhase (a + b) =
      criticalRealPhase a + criticalRealPhase b -
        (Collatz2.Word.criticalCarry a b : ℝ) * Real.log 2 := by
  unfold criticalRealPhase
  rw [beattyIndex_add_eq_add_carry]
  push_cast
  ring

namespace CriticalRecordPiece

/-- first carry 以前の phase は terminal record phase より strict に小さい。 -/
theorem phase_lt_terminal_phase
    {start r j : ℕ}
    (P : CriticalRecordPiece start r)
    (hjPos : 0 < j)
    (hj : j < r) :
    criticalRealPhase j < criticalRealPhase r := by
  have hNo := P.before_noCarry j hjPos hj
  have hBefore := criticalRealPhase_add start j
  rw [hNo] at hBefore
  norm_num at hBefore
  have hBeforeUpper := criticalRealPhase_lt_log_two (start + j)
  rw [hBefore] at hBeforeUpper
  have hTerminal := criticalRealPhase_add start r
  rw [P.terminal_carry] at hTerminal
  norm_num at hTerminal
  have hTerminalNonneg := criticalRealPhase_nonneg (start + r)
  rw [hTerminal] at hTerminalNonneg
  linarith

/-- first-carry record は smaller denominator に対する best-upper pair。 -/
theorem criticalUpperPair_bestUpper
    {start r : ℕ}
    (P : CriticalRecordPiece start r) :
    (Word.ContractingExponentPair.criticalUpperPair r P.length_pos).BestUpperAtSmallerDenominators
      := by
  intro j hjPos hjLt
  have hPhase := P.phase_lt_terminal_phase hjPos hjLt
  have hErr : criticalUpperError r < criticalUpperError j := by
    rw [criticalUpperError_eq_log_two_sub_phase,
      criticalUpperError_eq_log_two_sub_phase]
    linarith
  have hErrJPos := criticalUpperError_pos j
  have hjrNat : j ≤ r := Nat.le_of_lt hjLt
  have hjr : (j : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjrNat
  have hjNonneg : (0 : ℝ) ≤ j := by positivity
  have h1 :
      (j : ℝ) * criticalUpperError r ≤
        (j : ℝ) * criticalUpperError j :=
    mul_le_mul_of_nonneg_left (le_of_lt hErr) hjNonneg
  have h2 :
      (j : ℝ) * criticalUpperError j ≤
        (r : ℝ) * criticalUpperError j :=
    mul_le_mul_of_nonneg_right hjr (le_of_lt hErrJPos)
  have hScaled := le_trans h1 h2
  have hLogPos := real_log_two_pos
  have hCrossReal :
      (((beattyIndex r + 1) * j : ℕ) : ℝ) ≤
        ((r * (beattyIndex j + 1) : ℕ) : ℝ) := by
    unfold criticalUpperError at hScaled
    push_cast at hScaled
    have hScaled' :
        (((beattyIndex r : ℝ) + 1) * (j : ℝ)) * Real.log 2 ≤
          ((r : ℝ) * ((beattyIndex j : ℝ) + 1)) * Real.log 2 := by
      nlinarith [hScaled]
    push_cast
    nlinarith [hScaled', hLogPos]
  have hCrossNat :
      (beattyIndex r + 1) * j ≤ r * (beattyIndex j + 1) := by
    exact_mod_cast hCrossReal
  change
    (Collatz2.Word.criticalHeight r + 1) * j ≤
      r * (Collatz2.Word.criticalHeight j + 1)
  simpa only [beattyIndex_eq_wordCriticalHeight_all] using hCrossNat

/-- first-carry record は smaller denominator の critical upper slope より strict に良い。 -/
theorem criticalUpperPair_strictAtSmallerDenominators
    {start r j : ℕ}
    (P : CriticalRecordPiece start r)
    (hjPos : 0 < j)
    (hjLt : j < r) :
    (beattyIndex r + 1) * j < r * (beattyIndex j + 1) := by
  have hPhase := P.phase_lt_terminal_phase hjPos hjLt
  have hErr : criticalUpperError r < criticalUpperError j := by
    rw [criticalUpperError_eq_log_two_sub_phase,
      criticalUpperError_eq_log_two_sub_phase]
    linarith
  have hErrRPos := criticalUpperError_pos r
  have hErrJPos := criticalUpperError_pos j
  have hjr : (j : ℝ) < (r : ℝ) := by exact_mod_cast hjLt
  have hjPosR : (0 : ℝ) < j := by exact_mod_cast hjPos
  have h1 :
      (j : ℝ) * criticalUpperError r <
        (j : ℝ) * criticalUpperError j :=
    mul_lt_mul_of_pos_left hErr hjPosR
  have h2 :
      (j : ℝ) * criticalUpperError j <
        (r : ℝ) * criticalUpperError j :=
    mul_lt_mul_of_pos_right hjr hErrJPos
  have hScaled := lt_trans h1 h2
  have hLogPos := real_log_two_pos
  have hCrossReal :
      (((beattyIndex r + 1) * j : ℕ) : ℝ) <
        ((r * (beattyIndex j + 1) : ℕ) : ℝ) := by
    unfold criticalUpperError at hScaled
    push_cast at hScaled
    have hScaled' :
        (((beattyIndex r : ℝ) + 1) * (j : ℝ)) * Real.log 2 <
          ((r : ℝ) * ((beattyIndex j : ℝ) + 1)) * Real.log 2 := by
      nlinarith [hScaled]
    push_cast
    by_contra hNot
    have hRev :
        (r : ℝ) * ((beattyIndex j : ℝ) + 1) ≤
          ((beattyIndex r : ℝ) + 1) * (j : ℝ) := by
      exact le_of_not_gt hNot
    have hRevScaled :
        ((r : ℝ) * ((beattyIndex j : ℝ) + 1)) * Real.log 2 ≤
          (((beattyIndex r : ℝ) + 1) * (j : ℝ)) * Real.log 2 := by
      exact mul_le_mul_of_nonneg_right hRev (le_of_lt hLogPos)
    linarith
  exact_mod_cast hCrossReal

/-- 従って record upper pair は StripReduced。 -/
theorem criticalUpperPair_stripReduced
    {start r : ℕ}
    (P : CriticalRecordPiece start r) :
    (Collatz2.Word.ContractingExponentPair.criticalUpperPair r P.length_pos).StripReduced :=
  Collatz2.Word.ContractingExponentPair.stripReduced_of_bestUpper
    P.criticalUpperPair_bestUpper

/--
first-carry record の upper pair `(r, beta_r+1)` は primitive。
非 primitive なら primitive 化が同じ slope の smaller denominator contracting pair を与えるが、
record の strict best-upper 性と矛盾する。
-/
theorem criticalUpperPair_isPrimitive
    {start r : ℕ}
    (P : CriticalRecordPiece start r) :
    (Collatz2.Word.ContractingExponentPair.criticalUpperPair r P.length_pos).IsPrimitive := by
  let U :=
    Collatz2.Word.ContractingExponentPair.criticalUpperPair r P.length_pos
  by_contra hNot
  have hDenLt : U.primitivePair.oddCount < U.oddCount :=
    U.primitivePair_denominator_lt_of_not_primitive hNot
  have hDenPos : 0 < U.primitivePair.oddCount :=
    U.primitivePair.oddCount_pos
  have hDenLtR : U.primitivePair.oddCount < r := by
    simpa [U] using hDenLt
  have hStrict0 :=
    P.criticalUpperPair_strictAtSmallerDenominators hDenPos hDenLtR
  have hStrict :
      U.twoDepth * U.primitivePair.oddCount <
        U.oddCount *
          (Collatz2.Word.criticalHeight U.primitivePair.oddCount + 1) := by
    simpa [U, beattyIndex_eq_wordCriticalHeight_all] using hStrict0
  have hMinDepth :
      Collatz2.Word.criticalHeight U.primitivePair.oddCount + 1 ≤
        U.primitivePair.twoDepth := by
    have hCritPow :=
      Collatz2.Word.criticalHeight_pow_lt_threePow hDenPos
    by_contra hNotLe
    have hDepthLe :
        U.primitivePair.twoDepth ≤
          Collatz2.Word.criticalHeight U.primitivePair.oddCount := by
      omega
    have hTwoLe :
        2 ^ U.primitivePair.twoDepth ≤
          2 ^ Collatz2.Word.criticalHeight U.primitivePair.oddCount :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepthLe
    have hContract := U.primitivePair.contracting
    omega
  have hStrict' :
      U.twoDepth * U.primitivePair.oddCount <
        U.oddCount * U.primitivePair.twoDepth :=
    lt_of_lt_of_le hStrict
      (Nat.mul_le_mul_left U.oddCount hMinDepth)
  have hSlope := U.primitivePair_slope_eq
  have hSlope' :
      U.oddCount * U.primitivePair.twoDepth =
        U.twoDepth * U.primitivePair.oddCount := by
    calc
      U.oddCount * U.primitivePair.twoDepth
          = U.primitivePair.twoDepth * U.oddCount := by ring
      _ = U.twoDepth * U.primitivePair.oddCount := hSlope
  rw [hSlope'] at hStrict'
  exact (Nat.lt_irrefl _ hStrict')

/--
primitive + reduced bridge により、record upper pair の rational chord は
全 proper denominator で critical/Christoffel roof と exact に一致する。
-/
theorem criticalUpperPair_christoffelFloor
    {start r j : ℕ}
    (P : CriticalRecordPiece start r)
    (hjPos : 0 < j)
    (hjLt : j < r) :
    Collatz2.Word.criticalHeight j =
      (beattyIndex r + 1) * j / r := by
  let U :=
    Collatz2.Word.ContractingExponentPair.criticalUpperPair r P.length_pos
  have h :=
    U.criticalHeight_eq_chordFloor_of_primitive_reduced
      P.criticalUpperPair_isPrimitive
      P.criticalUpperPair_stripReduced
      hjPos (by simpa [U] using hjLt)
  simpa [U, beattyIndex_eq_wordCriticalHeight_all] using h

end CriticalRecordPiece

end ExternalArithmetic
end CSTMicro
end Collatz2
