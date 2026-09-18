import CollatzLean.Collatz3.Mersenne.TwoSidedSparseDefectEscape
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: small-hole exact normal forms

`ExactBlockSparseEquation` を hole 数 0,1,2 に特殊化する。

ここで行うのは有限分類そのものではなく、binary word の情報を

* hole 0: Mersenne 対 Mersenne
* hole 1: 片側に一つの 2 冪 correction
* hole 2: 片側二つ、または両側一つずつ

という exact exponential Diophantine equation に落とすところまで。

数値目標

* hole 0 なら `k ≤ 2`
* hole ≤ 1 なら `k ≤ 5`
* hole ≤ 2 なら `k ≤ 6`

は後段の modular lifting 層で扱う。
-/

namespace Collatz3
namespace Binary

/-- one-count が 0 なら binary word の値も 0。 -/
theorem valueLSB_eq_zero_of_oneCount_eq_zero
    (bits : List Bool)
    (h : oneCount bits = 0) :
    valueLSB bits = 0 := by
  induction bits with
  | nil => simp
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [oneCount_cons, bitValue_false, zero_add] at h
          simp [valueLSB, ih h]
      | true =>
          simp [oneCount] at h

/-- one-count が 1 なら値は一つの 2 冪。 -/
theorem exists_singleBit_of_oneCount_eq_one
    (bits : List Bool)
    (h : oneCount bits = 1) :
    ∃ a : ℕ,
      a < bits.length ∧
      valueLSB bits = 2 ^ a := by
  induction bits with
  | nil =>
      simp at h
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [oneCount_cons, bitValue_false, zero_add] at h
          rcases ih h with ⟨a, ha, hValue⟩
          refine ⟨a + 1, ?_, ?_⟩
          · simp
            omega
          · simp only [valueLSB_cons, bitValue_false, zero_add, hValue]
            rw [pow_succ]
            ring
      | true =>
          have hZero : oneCount bs = 0 := by
            simp [oneCount] at h
            omega
          have hValueZero := valueLSB_eq_zero_of_oneCount_eq_zero bs hZero
          refine ⟨0, by simp, ?_⟩
          simp [valueLSB, hValueZero]

/-- one-count が 2 なら値は異なる二つの 2 冪の和。 -/
theorem exists_twoBits_of_oneCount_eq_two
    (bits : List Bool)
    (h : oneCount bits = 2) :
    ∃ a b : ℕ,
      a < b ∧
      b < bits.length ∧
      valueLSB bits = 2 ^ a + 2 ^ b := by
  induction bits with
  | nil =>
      simp at h
  | cons bit bs ih =>
      cases bit with
      | false =>
          simp only [oneCount_cons, bitValue_false, zero_add] at h
          rcases ih h with ⟨a, b, hab, hb, hValue⟩
          refine ⟨a + 1, b + 1, by omega, ?_, ?_⟩
          · simp
            omega
          · simp only [valueLSB_cons, bitValue_false, zero_add, hValue]
            rw [pow_succ, pow_succ]
            ring
      | true =>
          have hOne : oneCount bs = 1 := by
            simp [oneCount] at h
            omega
          rcases exists_singleBit_of_oneCount_eq_one bs hOne with
            ⟨a, ha, hValue⟩
          refine ⟨0, a + 1, by omega, ?_, ?_⟩
          · simp
            omega
          · simp only [valueLSB_cons, bitValue_true, hValue, pow_zero]
            rw [pow_succ]
            ring

end Binary

namespace Mersenne

/-- exact equation に含まれる source/target hole の総数。 -/
def exactHoleCount
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (_hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits) : ℕ :=
  Binary.oneCount sourceTail + Binary.oneCount targetBits

/-- hole 0 の正規形。 -/
def NoHoleEquation (k n r L : ℕ) : Prop :=
  (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1) =
    (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1) + 1

/-- source 側だけに一つ hole `2^a` がある正規形。 -/
def SourceOneHoleEquation (k n r L a : ℕ) : Prop :=
  (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1 - (2 : ℤ) ^ a) =
    (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1) + 1

/-- target 側だけに一つ hole `2^b` がある正規形。 -/
def TargetOneHoleEquation (k n r L b : ℕ) : Prop :=
  (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1) =
    (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ b) + 1

/-- source 側に二つ hole がある正規形。 -/
def SourceTwoHoleEquation (k n r L a b : ℕ) : Prop :=
  (3 : ℤ) ^ k *
      ((2 : ℤ) ^ n - 1 - (2 : ℤ) ^ a - (2 : ℤ) ^ b) =
    (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1) + 1

/-- target 側に二つ hole がある正規形。 -/
def TargetTwoHoleEquation (k n r L a b : ℕ) : Prop :=
  (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1) =
    (2 : ℤ) ^ r *
      ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ a - (2 : ℤ) ^ b) + 1

/-- source/target に一つずつ hole がある正規形。 -/
def SplitTwoHoleEquation (k n r L a b : ℕ) : Prop :=
  (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1 - (2 : ℤ) ^ a) =
    (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ b) + 1

/-- hole 数 0 の exact equation は Mersenne 対 Mersenne の形になる。 -/
theorem noHole_normalForm
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits)
    (hHole : Binary.oneCount sourceTail + Binary.oneCount targetBits = 0) :
    NoHoleEquation k sourceLength r targetLength := by
  have hSourceCount : Binary.oneCount sourceTail = 0 := by
    omega
  have hTargetCount : Binary.oneCount targetBits = 0 := by
    omega
  have hSourceValue :=
    Binary.valueLSB_eq_zero_of_oneCount_eq_zero
      sourceTail hSourceCount
  have hTargetValue :=
    Binary.valueLSB_eq_zero_of_oneCount_eq_zero
      targetBits hTargetCount
  unfold NoHoleEquation
  have h := hEq.equation
  simp only [Int.reduceNeg, Binary.valueLSB, Binary.bitValue_false, hSourceValue,
            mul_zero, add_zero, Nat.cast_zero,sub_zero, hTargetValue] at h
  rw [pow_add] at h
  linear_combination h

/-- hole 数 1 なら source 一個または target 一個の二択。 -/
theorem oneHole_normalForm
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits)
    (hHole : Binary.oneCount sourceTail + Binary.oneCount targetBits = 1) :
    (∃ a : ℕ,
        0 < a ∧ a < sourceLength ∧
        SourceOneHoleEquation k sourceLength r targetLength a) ∨
      (∃ b : ℕ,
        0 < b ∧ b < targetLength ∧
        TargetOneHoleEquation k sourceLength r targetLength b) := by
  by_cases hSource : Binary.oneCount sourceTail = 1
  · have hTarget : Binary.oneCount targetBits = 0 := by omega
    rcases Binary.exists_singleBit_of_oneCount_eq_one sourceTail hSource with
      ⟨a, ha, hValue⟩
    have hTargetValue :=
      Binary.valueLSB_eq_zero_of_oneCount_eq_zero targetBits hTarget
    refine Or.inl ⟨a + 1, by omega, ?_, ?_⟩
    · have hLen := hEq.sourceTail_length
      simp at hLen
      omega
    · unfold SourceOneHoleEquation
      have h := hEq.equation
      simp only [Binary.valueLSB_cons, Binary.bitValue_false, zero_add,
        hValue, hTargetValue] at h
      push_cast at h
      rw [pow_add] at h
      rw [pow_succ]
      linear_combination h
  · have hSourceZero : Binary.oneCount sourceTail = 0 := by omega
    have hTargetOne : Binary.oneCount targetBits = 1 := by omega
    have hSourceValue :=
      Binary.valueLSB_eq_zero_of_oneCount_eq_zero sourceTail hSourceZero
    rcases hEq.targetBits_lsb_false with ⟨targetTail, hTargetBits⟩
    have hTargetTailOne : Binary.oneCount targetTail = 1 := by
      rw [hTargetBits] at hTargetOne
      simpa [Binary.oneCount] using hTargetOne
    rcases Binary.exists_singleBit_of_oneCount_eq_one targetTail hTargetTailOne with
      ⟨b, hb, hTargetValue⟩
    refine Or.inr ⟨b + 1, by omega, ?_, ?_⟩
    · have hLen := hEq.targetBits_length
      rw [hTargetBits] at hLen
      simp at hLen
      omega
    · unfold TargetOneHoleEquation
      have h := hEq.equation
      rw [hTargetBits] at h
      simp only [Binary.valueLSB_cons, Binary.bitValue_false, zero_add,
        hSourceValue, hTargetValue] at h
      push_cast at h
      rw [pow_add] at h
      rw [pow_succ]
      linear_combination h

/-- hole 数 2 は `(2,0)`, `(1,1)`, `(0,2)` の三ケースに exact に分解できる。 -/
theorem twoHole_normalForm
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits)
    (hHole : Binary.oneCount sourceTail + Binary.oneCount targetBits = 2) :
    (∃ a b : ℕ,
        0 < a ∧ a < b ∧ b < sourceLength ∧
        SourceTwoHoleEquation k sourceLength r targetLength a b) ∨
    (∃ a b : ℕ,
        0 < a ∧ a < sourceLength ∧
        0 < b ∧ b < targetLength ∧
        SplitTwoHoleEquation k sourceLength r targetLength a b) ∨
    (∃ a b : ℕ,
        0 < a ∧ a < b ∧ b < targetLength ∧
        TargetTwoHoleEquation k sourceLength r targetLength a b) := by
  rcases Nat.eq_zero_or_pos (Binary.oneCount sourceTail) with hSourceZero | hSourcePos
  · have hTargetTwo : Binary.oneCount targetBits = 2 := by omega
    rcases hEq.targetBits_lsb_false with ⟨targetTail, hTargetBits⟩
    have hTailTwo : Binary.oneCount targetTail = 2 := by
      rw [hTargetBits] at hTargetTwo
      simpa [Binary.oneCount] using hTargetTwo
    rcases Binary.exists_twoBits_of_oneCount_eq_two targetTail hTailTwo with
      ⟨a, b, hab, hb, hValue⟩
    have hSourceValue :=
      Binary.valueLSB_eq_zero_of_oneCount_eq_zero sourceTail hSourceZero
    refine Or.inr (Or.inr ⟨a + 1, b + 1, by omega, by omega, ?_, ?_⟩)
    · have hLen := hEq.targetBits_length
      rw [hTargetBits] at hLen
      simp at hLen
      omega
    · unfold TargetTwoHoleEquation
      have h := hEq.equation
      rw [hTargetBits] at h
      simp only [Binary.valueLSB_cons, Binary.bitValue_false, zero_add,
        hSourceValue, hValue] at h
      push_cast at h
      rw [pow_add] at h
      rw [pow_succ, pow_succ]
      linear_combination h
  · by_cases hSourceTwo : Binary.oneCount sourceTail = 2
    · have hTargetZero : Binary.oneCount targetBits = 0 := by omega
      rcases Binary.exists_twoBits_of_oneCount_eq_two sourceTail hSourceTwo with
        ⟨a, b, hab, hb, hValue⟩
      have hTargetValue :=
        Binary.valueLSB_eq_zero_of_oneCount_eq_zero targetBits hTargetZero
      refine Or.inl ⟨a + 1, b + 1, by omega, by omega, ?_, ?_⟩
      · have hLen := hEq.sourceTail_length
        simp at hLen
        omega
      · unfold SourceTwoHoleEquation
        have h := hEq.equation
        simp only [Binary.valueLSB_cons, Binary.bitValue_false, zero_add,
          hValue, hTargetValue] at h
        push_cast at h
        rw [pow_add] at h
        rw [pow_succ, pow_succ]
        linear_combination h
    · have hSourceOne : Binary.oneCount sourceTail = 1 := by omega
      have hTargetOne : Binary.oneCount targetBits = 1 := by omega
      rcases Binary.exists_singleBit_of_oneCount_eq_one sourceTail hSourceOne with
        ⟨a, ha, hSourceValue⟩
      rcases hEq.targetBits_lsb_false with ⟨targetTail, hTargetBits⟩
      have hTargetTailOne : Binary.oneCount targetTail = 1 := by
        rw [hTargetBits] at hTargetOne
        simpa [Binary.oneCount] using hTargetOne
      rcases Binary.exists_singleBit_of_oneCount_eq_one targetTail hTargetTailOne with
        ⟨b, hb, hTargetValue⟩
      refine Or.inr (Or.inl ⟨a + 1, b + 1, by omega, ?_, by omega, ?_, ?_⟩)
      · have hLen := hEq.sourceTail_length
        simp at hLen
        omega
      · have hLen := hEq.targetBits_length
        rw [hTargetBits] at hLen
        simp at hLen
        omega
      · unfold SplitTwoHoleEquation
        have h := hEq.equation
        rw [hTargetBits] at h
        simp only [Binary.valueLSB_cons, Binary.bitValue_false, zero_add,
          hSourceValue, hTargetValue] at h
        push_cast at h
        rw [pow_add] at h
        rw [pow_succ, pow_succ]
        linear_combination h

/-- at most one hole は hole 0 または hole 1。 -/
theorem atMostOneHole_cases
    {a b : ℕ}
    (h : a + b ≤ 1) :
    a + b = 0 ∨ a + b = 1 := by
  omega

/-- at most two holes は hole 0,1,2 のいずれか。 -/
theorem atMostTwoHole_cases
    {a b : ℕ}
    (h : a + b ≤ 2) :
    a + b = 0 ∨ a + b = 1 ∨ a + b = 2 := by
  omega


/-- 期待される no-hole 解 `(1,1,1,1)`。 -/
theorem noHole_solution_1_1_1_1 :
    NoHoleEquation 1 1 1 1 := by
  norm_num [NoHoleEquation]

/-- 期待される no-hole 解 `(1,2,3,1)`。 -/
theorem noHole_solution_1_2_3_1 :
    NoHoleEquation 1 2 3 1 := by
  norm_num [NoHoleEquation]

/-- 期待される no-hole 解 `(2,1,3,1)`。 -/
theorem noHole_solution_2_1_3_1 :
    NoHoleEquation 2 1 3 1 := by
  norm_num [NoHoleEquation]

/-- 期待される no-hole 解 `(2,3,1,5)`。 -/
theorem noHole_solution_2_3_1_5 :
    NoHoleEquation 2 3 1 5 := by
  norm_num [NoHoleEquation]

/--
hole 0 の完全分類 target。

期待される四解は
`(k,n,r,L)=(1,1,1,1),(1,2,3,1),(2,1,3,1),(2,3,1,5)`。
この定義自体は仮定や axiom ではない。
-/
def NoHoleCompleteClassification : Prop :=
  ∀ k n r L : ℕ,
    0 < k → 0 < n → 0 < r → 0 < L →
    NoHoleEquation k n r L →
    (k = 1 ∧ n = 1 ∧ r = 1 ∧ L = 1) ∨
    (k = 1 ∧ n = 2 ∧ r = 3 ∧ L = 1) ∨
    (k = 2 ∧ n = 1 ∧ r = 3 ∧ L = 1) ∨
    (k = 2 ∧ n = 3 ∧ r = 1 ∧ L = 5)

/-- complete no-hole classification が得られれば、特に `k ≤ 2`。 -/
theorem NoHoleCompleteClassification.depth_le_two
    (hClass : NoHoleCompleteClassification)
    {k n r L : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) (hL : 0 < L)
    (hEq : NoHoleEquation k n r L) :
    k ≤ 2 := by
  rcases hClass k n r L hk hn hr hL hEq with h | h | h | h <;>
    rcases h with ⟨rfl, _⟩ <;> omega

/-- hole ≤ 1 に対する有限分類の数値 target。 -/
def AtMostOneHoleDepthBound : Prop :=
  ∀ k sourceLength r targetLength : ℕ,
    ∀ sourceTail targetBits : List Bool,
      ExactBlockSparseEquation
        k sourceLength r targetLength sourceTail targetBits →
      Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ 1 →
      k ≤ 5

/-- hole ≤ 2 に対する有限分類の数値 target。 -/
def AtMostTwoHoleDepthBound : Prop :=
  ∀ k sourceLength r targetLength : ℕ,
    ∀ sourceTail targetBits : List Bool,
      ExactBlockSparseEquation
        k sourceLength r targetLength sourceTail targetBits →
      Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ 2 →
      k ≤ 6


/--
small-hole finite theory が閉じたときに得られる最初の具体的 complexity lower bound。

* `k ≤ 2` では何も要求しない。
* `3 ≤ k ≤ 5` では少なくとも1 hole。
* `k = 6` では少なくとも2 holes。
* `7 ≤ k` では少なくとも3 holes。
-/
def smallHoleLowerBound (k : ℕ) : ℕ :=
  if k ≤ 2 then 0
  else if k ≤ 5 then 1
  else if k ≤ 6 then 2
  else 3

/--
0-hole 完全分類、≤1-hole bound、≤2-hole bound の三つが閉じれば、
`smallHoleLowerBound` は `BlockSparsePow3LowerBound` を満たす。

有限小-hole 理論を一般 `G(k)` 研究へ接続する glue theorem。
-/
theorem blockSparsePow3LowerBound_smallHole
    (hZero : NoHoleCompleteClassification)
    (hOne : AtMostOneHoleDepthBound)
    (hTwo : AtMostTwoHoleDepthBound) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  intro k sourceLength r targetLength sourceTail targetBits hEq
  by_cases hk2 : k ≤ 2
  · simp [smallHoleLowerBound, hk2]
  · by_cases hk5 : k ≤ 5
    · have hHolePos :
          0 < Binary.oneCount sourceTail + Binary.oneCount targetBits := by
        by_contra hNot
        have hHoleZero :
            Binary.oneCount sourceTail + Binary.oneCount targetBits = 0 := by
          omega
        have hNorm := noHole_normalForm hEq hHoleZero
        have hkLe : k ≤ 2 :=
          NoHoleCompleteClassification.depth_le_two
            hZero hEq.depth_pos hEq.sourceLength_pos
            hEq.exitDepth_pos hEq.targetLength_pos hNorm
        omega
      simp [smallHoleLowerBound, hk2, hk5]
      omega
    · by_cases hk6 : k ≤ 6
      · have hHoleTwo :
            2 ≤ Binary.oneCount sourceTail + Binary.oneCount targetBits := by
          by_contra hNot
          have hAtMost :
              Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ 1 := by
            omega
          have hkLe : k ≤ 5 :=
            hOne k sourceLength r targetLength sourceTail targetBits hEq hAtMost
          omega
        simp [smallHoleLowerBound, hk2, hk5, hk6]
        omega
      · have hHoleThree :
            3 ≤ Binary.oneCount sourceTail + Binary.oneCount targetBits := by
          by_contra hNot
          have hAtMost :
              Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ 2 := by
            omega
          have hkLe : k ≤ 6 :=
            hTwo k sourceLength r targetLength sourceTail targetBits hEq hAtMost
          omega
        simp [smallHoleLowerBound, hk2, hk5, hk6]
        omega

end Mersenne
end Collatz3
