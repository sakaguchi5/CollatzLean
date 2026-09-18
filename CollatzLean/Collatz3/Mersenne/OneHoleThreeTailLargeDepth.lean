import CollatzLean.Collatz3.Mersenne.OneHoleFiniteLift65536
import Std.Data.HashSet.Lemmas
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: one-hole large-depth 3-adic tail sieve

`k ≤ 5` を証明するには、3 が unit である modulus をいくら lift しても
large `k` が小さい residue class へ wrap around し続ける。

そこでこの層では `3^6` を modulus に入れ、`k ≥ 6` を 3-adic tail として
有限状態へ送る。

主 modulus は

`M₄ = 3^6 * 7 * 19 * 73 * 163 * 487 = 561847684041`。

この modulus では

* `2` は period 486、
* `3` は tail 6、その後 period 972

を持つ。

これにより

* source-one の低位 resonance `a=2` は `k≥6` で完全排除、
* target-one の low-source `n=1` は `k≥6` で完全排除、
* `n=2` も既存 bridge により排除

までを finite certificate で閉じる。

さらに source の `r=2` branch は mod 3 だけで一括排除し、large-depth source-one を

`k even`, `a≥3`, `r=1`

という一枝へ局所化する。
-/

namespace Collatz3
namespace Mersenne

/-! ## 3-adic tail modulus -/

/-- `M₄ = 3^6 * 7 * 19 * 73 * 163 * 487`。 -/
def oneHoleThreeTailModulus : ℕ := 561847684041

/-- `mod M₄` では 2 は period 486。 -/
theorem powTailLoop_two_oneHoleThreeTail :
    PowTailLoop oneHoleThreeTailModulus 2 0 486 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- `mod M₄` では 3 は tail 6、その後 period 972。 -/
theorem powTailLoop_three_oneHoleThreeTail :
    PowTailLoop oneHoleThreeTailModulus 3 6 972 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- `M₄` 上の 2/3 combined tail-loop certificate。 -/
theorem pow23TailLoops_oneHoleThreeTail :
    Pow23TailLoops oneHoleThreeTailModulus 0 486 6 972 :=
  ⟨powTailLoop_two_oneHoleThreeTail,
    powTailLoop_three_oneHoleThreeTail⟩

/-- `k≥6` の 3-exponent representative。 -/
private def largeDepthKRep (j : Fin 972) : ℕ := 6 + j.1

/-! ## source `a=2`: large depth は survivor 0 -/

private def sourceHoleTwoLhs
    (K N : ℕ) : ZMod oneHoleThreeTailModulus :=
  (3 : ZMod oneHoleThreeTailModulus) ^ K *
    ((2 : ZMod oneHoleThreeTailModulus) ^ N - 1 -
      (2 : ZMod oneHoleThreeTailModulus) ^ 2)

private def sourceAnyRhs
    (R L : ℕ) : ZMod oneHoleThreeTailModulus :=
  (2 : ZMod oneHoleThreeTailModulus) ^ R *
      ((2 : ZMod oneHoleThreeTailModulus) ^ L - 1) + 1

private def sourceAnyRhsList : List ℕ :=
  (List.range 486).flatMap fun R =>
    (List.range 486).map fun L =>
      (sourceAnyRhs R L).val

private def sourceAnyRhsSet : Std.HashSet ℕ :=
  Std.HashSet.ofList sourceAnyRhsList

private theorem sourceAnyRhsSet_contains
    (R L : Fin 486) :
    sourceAnyRhsSet.contains (sourceAnyRhs R.1 L.1).val = true := by
  have hMem :
      (sourceAnyRhs R.1 L.1).val ∈ sourceAnyRhsList := by
    unfold sourceAnyRhsList
    apply List.mem_flatMap.mpr
    refine ⟨R.1, List.mem_range.mpr R.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨L.1, List.mem_range.mpr L.2, rfl⟩
  simpa only [
    sourceAnyRhsSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
`M₄` の finite certificate。

`k≥6`, `a=2` に対応する全 972 個の 3-tail state と全 486 個の source-length stateで、
左辺 residue は source RHS reachable set に一度も入らない。
-/
private theorem sourceHoleTwo_largeDepth_finite_sieve :
    ∀ J : Fin 972,
      ∀ N : Fin 486,
        sourceAnyRhsSet.contains
            (sourceHoleTwoLhs (largeDepthKRep J) N.1).val = false := by
  native_decide

/-- source-one `a=2` は `k≥6` では不可能。 -/
theorem SourceOneHoleEquation.largeDepth_hole_two_impossible
    {k n r L : ℕ}
    (hk : 6 ≤ k)
    (hEq : SourceOneHoleEquation k n r L 2) :
    False := by
  have hMod := hEq.to_mod oneHoleThreeTailModulus
  have hRed := hMod.reduce_tailLoop pow23TailLoops_oneHoleThreeTail
  let J : ℕ := (k - 6) % 972
  have hJlt : J < 972 := by
    dsimp [J]
    exact Nat.mod_lt _ (by norm_num)
  let Jf : Fin 972 := ⟨J, hJlt⟩
  let N : ℕ := n % 486
  let R : ℕ := r % 486
  let T : ℕ := L % 486
  have hNlt : N < 486 := by
    dsimp [N]
    exact Nat.mod_lt _ (by norm_num)
  have hRlt : R < 486 := by
    dsimp [R]
    exact Nat.mod_lt _ (by norm_num)
  have hTlt : T < 486 := by
    dsimp [T]
    exact Nat.mod_lt _ (by norm_num)
  let Nf : Fin 486 := ⟨N, hNlt⟩
  let Rf : Fin 486 := ⟨R, hRlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  have hkNot : ¬ k < 6 := by omega
  have hEqFinite :
      SourceOneHoleModEquation oneHoleThreeTailModulus
        (largeDepthKRep Jf) Nf.1 Rf.1 Tf.1 2 := by
    dsimp [largeDepthKRep, Jf, J, Nf, Rf, Tf, N, R, T]
    simpa [tailLoopExponent, hkNot] using hRed
  have hEqZ :
      sourceHoleTwoLhs (largeDepthKRep Jf) Nf.1 =
        sourceAnyRhs Rf.1 Tf.1 := by
    simpa [sourceHoleTwoLhs, sourceAnyRhs,
      SourceOneHoleModEquation] using hEqFinite
  have hEqVal := congrArg ZMod.val hEqZ
  have hMem :
      sourceAnyRhsSet.contains
        (sourceHoleTwoLhs (largeDepthKRep Jf) Nf.1).val = true := by
    rw [hEqVal]
    exact sourceAnyRhsSet_contains Rf Tf
  have hNo := sourceHoleTwo_largeDepth_finite_sieve Jf Nf
  rw [hMem] at hNo
  cases hNo

/-! ## target `n=1`: large depth は survivor 0 -/

private def targetDiff
    (L B : ℕ) : ZMod oneHoleThreeTailModulus :=
  (2 : ZMod oneHoleThreeTailModulus) ^ L - 1 -
    (2 : ZMod oneHoleThreeTailModulus) ^ B

private def targetDiffList : List ℕ :=
  (List.range 486).flatMap fun L =>
    (List.range 486).map fun B =>
      (targetDiff L B).val

private def targetDiffSet : Std.HashSet ℕ :=
  Std.HashSet.ofList targetDiffList

private theorem targetDiffSet_contains
    (L B : Fin 486) :
    targetDiffSet.contains (targetDiff L.1 B.1).val = true := by
  have hMem :
      (targetDiff L.1 B.1).val ∈ targetDiffList := by
    unfold targetDiffList
    apply List.mem_flatMap.mpr
    refine ⟨L.1, List.mem_range.mpr L.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    targetDiffSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
`3^K-1` を `2^R` で割る代わりに、period 486 を使って `2^(486-R)` を掛ける。
-/
private def targetNormalized
    (K R : ℕ) : ZMod oneHoleThreeTailModulus :=
  ((3 : ZMod oneHoleThreeTailModulus) ^ K - 1) *
    (2 : ZMod oneHoleThreeTailModulus) ^ (486 - R)

/-- target `n=1`, `k≥6` の finite certificate。 -/
private theorem targetSourceOne_largeDepth_finite_sieve :
    ∀ J : Fin 972,
      ∀ R : Fin 486,
        targetDiffSet.contains
            (targetNormalized (largeDepthKRep J) R.1).val = false := by
  native_decide

/-- `mod M₄` で `2^R * 2^(486-R)=1`。 -/
private theorem twoPow_mul_complement_eq_one
    (R : Fin 486) :
    (2 : ZMod oneHoleThreeTailModulus) ^ R.1 *
        (2 : ZMod oneHoleThreeTailModulus) ^ (486 - R.1) = 1 := by
  have hPeriod :
      (2 : ZMod oneHoleThreeTailModulus) ^ 486 = 1 := by
    simpa using powTailLoop_two_oneHoleThreeTail.loop_at_tail
  rw [← pow_add, show R.1 + (486 - R.1) = 486 by omega, hPeriod]

/-- target-one `n=1` は `k≥6` では不可能。 -/
theorem TargetOneHoleEquation.largeDepth_source_one_impossible
    {k r L b : ℕ}
    (hk : 6 ≤ k)
    (hEq : TargetOneHoleEquation k 1 r L b) :
    False := by
  have hMod := hEq.to_mod oneHoleThreeTailModulus
  have hRed := hMod.reduce_tailLoop pow23TailLoops_oneHoleThreeTail
  let J : ℕ := (k - 6) % 972
  have hJlt : J < 972 := by
    dsimp [J]
    exact Nat.mod_lt _ (by norm_num)
  let Jf : Fin 972 := ⟨J, hJlt⟩
  let R : ℕ := r % 486
  let T : ℕ := L % 486
  let B : ℕ := b % 486
  have hRlt : R < 486 := by
    dsimp [R]
    exact Nat.mod_lt _ (by norm_num)
  have hTlt : T < 486 := by
    dsimp [T]
    exact Nat.mod_lt _ (by norm_num)
  have hBlt : B < 486 := by
    dsimp [B]
    exact Nat.mod_lt _ (by norm_num)
  let Rf : Fin 486 := ⟨R, hRlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  let Bf : Fin 486 := ⟨B, hBlt⟩
  have hkNot : ¬ k < 6 := by omega
  have hEqFinite :
      TargetOneHoleModEquation oneHoleThreeTailModulus
        (largeDepthKRep Jf) 1 Rf.1 Tf.1 Bf.1 := by
    dsimp [largeDepthKRep, Jf, J, Rf, Tf, Bf, R, T, B]
    simpa [tailLoopExponent, hkNot] using hRed
  have hFinite' := hEqFinite
  unfold TargetOneHoleModEquation at hFinite'
  norm_num at hFinite'
  have hSub :
      (3 : ZMod oneHoleThreeTailModulus) ^ (largeDepthKRep Jf) - 1 =
        (2 : ZMod oneHoleThreeTailModulus) ^ Rf.1 *
          targetDiff Tf.1 Bf.1 := by
    unfold targetDiff
    linear_combination hFinite'
  have hNorm :
      targetNormalized (largeDepthKRep Jf) Rf.1 =
        targetDiff Tf.1 Bf.1 := by
    unfold targetNormalized
    rw [hSub]
    calc
      ((2 : ZMod oneHoleThreeTailModulus) ^ Rf.1 *
          targetDiff Tf.1 Bf.1) *
          (2 : ZMod oneHoleThreeTailModulus) ^ (486 - Rf.1)
          = targetDiff Tf.1 Bf.1 *
              ((2 : ZMod oneHoleThreeTailModulus) ^ Rf.1 *
                (2 : ZMod oneHoleThreeTailModulus) ^ (486 - Rf.1)) := by
              ring
      _ = targetDiff Tf.1 Bf.1 := by
            rw [twoPow_mul_complement_eq_one Rf, mul_one]
  have hVal := congrArg ZMod.val hNorm
  have hMem :
      targetDiffSet.contains
        (targetNormalized (largeDepthKRep Jf) Rf.1).val = true := by
    rw [hVal]
    exact targetDiffSet_contains Tf Bf
  have hNo := targetSourceOne_largeDepth_finite_sieve Jf Rf
  rw [hMem] at hNo
  cases hNo

/-- `n=2` は既存 bridge で `n=1, depth=k+1` へ移るため、`k≥6` では不可能。 -/
theorem TargetOneHoleEquation.largeDepth_source_two_impossible
    {k r L b : ℕ}
    (hk : 6 ≤ k)
    (hEq : TargetOneHoleEquation k 2 r L b) :
    False := by
  exact hEq.source_two_to_source_one.largeDepth_source_one_impossible (by omega)

/-! ## source exit-depth 2 は mod 3 で一括排除 -/

/-- source-one では positive depth と `r=2` は両立しない。 -/
theorem SourceOneHoleEquation.exitDepth_two_impossible
    {k n L a : ℕ}
    (hk : 0 < k)
    (hEq : SourceOneHoleEquation k n 2 L a) :
    False := by
  have hMod := hEq.to_mod 3
  unfold SourceOneHoleModEquation at hMod
  have hThree : (3 : ZMod 3) ^ k = 0 := by
    obtain ⟨j, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ]
    have h3 : (3 : ZMod 3) = 0 := by
      decide
    simp [h3]
  have hTwoSq : (2 : ZMod 3) ^ 2 = 1 := by
    decide
  have hZero :
      (0 : ZMod 3) = (2 : ZMod 3) ^ L := by
    rw [hThree] at hMod
    simpa [hTwoSq] using hMod
  have hTwoUnit : IsUnit (2 : ZMod 3) := by
    exact (ZMod.isUnit_iff_coprime 2 3).2 (by decide)
  have hPowNe :
      (2 : ZMod 3) ^ L ≠ 0 :=
    (hTwoUnit.pow L).ne_zero
  exact hPowNe hZero.symm

/-! ## source hole 1, r=1 の小さい 3-tail certificate -/

/-- source `a=1,r=1` には `729*7=5103` だけで十分。 -/
theorem pow23TailLoops_sourceHoleOneSmall :
    Pow23TailLoops 5103 0 486 6 6 := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    native_decide
  · refine ⟨by norm_num, ?_⟩
    native_decide

/-- source `a=1,r=1` の左辺 residue。 -/
private def sourceHoleOneROneLhs
    (K N : ℕ) : ZMod 5103 :=
  (3 : ZMod 5103) ^ K *
    ((2 : ZMod 5103) ^ N - 1 - (2 : ZMod 5103) ^ 1)

/-- source `a=1,r=1` の右辺 residue。`L` だけに依存する。 -/
private def sourceHoleOneROneRhs
    (L : ℕ) : ZMod 5103 :=
  (2 : ZMod 5103) ^ 1 * ((2 : ZMod 5103) ^ L - 1) + 1

/--
source `a=1,r=1` の右辺 reachable residue。

従来の `J × N × L = 6 × 486²` 全探索を避けるため、
`L` 側 486 個だけを先に table 化する。
-/
private def sourceHoleOneROneRhsList : List ℕ :=
  (List.range 486).map fun L =>
    (sourceHoleOneROneRhs L).val

private def sourceHoleOneROneRhsSet : Std.HashSet ℕ :=
  Std.HashSet.ofList sourceHoleOneROneRhsList

/-- 任意の finite `L` は右辺 reachable set に入る。 -/
private theorem sourceHoleOneROneRhsSet_contains
    (L : Fin 486) :
    sourceHoleOneROneRhsSet.contains
        (sourceHoleOneROneRhs L.1).val = true := by
  have hMem :
      (sourceHoleOneROneRhs L.1).val ∈ sourceHoleOneROneRhsList := by
    unfold sourceHoleOneROneRhsList
    apply List.mem_map.mpr
    exact ⟨L.1, List.mem_range.mpr L.2, rfl⟩
  simpa only [
    sourceHoleOneROneRhsSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
source `a=1,r=1`, `k≥6` の finite certificate。

計算核は `J × N = 6 × 486 = 2916` 状態だけ。
各状態では 486 要素の右辺 HashSet への membership だけを判定する。
-/
private theorem sourceHoleOneROne_largeDepth_finite_sieve :
    ∀ J : Fin 6,
      ∀ N : Fin 486,
        sourceHoleOneROneRhsSet.contains
            (sourceHoleOneROneLhs (6 + J.1) N.1).val = false := by
  native_decide

/-- source-one `a=1,r=1` は `k≥6` では不可能。 -/
theorem SourceOneHoleEquation.largeDepth_hole_one_exit_one_impossible
    {k n L : ℕ}
    (hk : 6 ≤ k)
    (hEq : SourceOneHoleEquation k n 1 L 1) :
    False := by
  have hMod := hEq.to_mod 5103
  have hRed := hMod.reduce_tailLoop pow23TailLoops_sourceHoleOneSmall
  let J : ℕ := (k - 6) % 6
  have hJlt : J < 6 := by
    dsimp [J]
    exact Nat.mod_lt _ (by norm_num)
  let Jf : Fin 6 := ⟨J, hJlt⟩
  let N : ℕ := n % 486
  let T : ℕ := L % 486
  have hNlt : N < 486 := by
    dsimp [N]
    exact Nat.mod_lt _ (by norm_num)
  have hTlt : T < 486 := by
    dsimp [T]
    exact Nat.mod_lt _ (by norm_num)
  let Nf : Fin 486 := ⟨N, hNlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  have hkNot : ¬ k < 6 := by omega
  have hEqFinite :
      SourceOneHoleModEquation 5103 (6 + Jf.1) Nf.1 1 Tf.1 1 := by
    dsimp [Jf, J, Nf, Tf, N, T]
    simpa [tailLoopExponent, hkNot] using hRed
  have hEqZ :
      sourceHoleOneROneLhs (6 + Jf.1) Nf.1 =
        sourceHoleOneROneRhs Tf.1 := by
    simpa [sourceHoleOneROneLhs, sourceHoleOneROneRhs,
      SourceOneHoleModEquation] using hEqFinite
  have hEqVal := congrArg ZMod.val hEqZ
  have hMem :
      sourceHoleOneROneRhsSet.contains
        (sourceHoleOneROneLhs (6 + Jf.1) Nf.1).val = true := by
    rw [hEqVal]
    exact sourceHoleOneROneRhsSet_contains Tf
  have hNo := sourceHoleOneROne_largeDepth_finite_sieve Jf Nf
  rw [hMem] at hNo
  cases hNo

/-! ## large-depth normal forms after the 3-tail sieve -/

/--
large-depth source-one は一枝だけ残る。

`k≥6` の exact source-one equation なら

* `k` は even、
* source hole は `a≥3`、
* exit depth は `r=1`

でなければならない。
-/
theorem SourceOneHoleEquation.largeDepth_shape
    {k n r L a : ℕ}
    (hk : 6 ≤ k)
    (ha0 : 0 < a) (han : a < n)
    (hr : 0 < r) (hL : 0 < L)
    (hEq : SourceOneHoleEquation k n r L a) :
    k % 2 = 0 ∧ 3 ≤ a ∧ r = 1 := by
  rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
  · have haCases : a = 1 ∨ a = 2 ∨ 3 ≤ a := by omega
    rcases haCases with rfl | rfl | haThree
    · have hn2 : 2 ≤ n := by omega
      by_cases hnEq : n = 2
      · subst n
        have hClass := hEq.source_two_hole_one_classification
          (by omega) hr hL
        rcases hClass with h | h <;> omega
      · have hn3 : 3 ≤ n := by omega
        have hr2 := hEq.exitDepth_eq_two_of_even_hole_one
          hkEven hn3 hr hL
        subst r
        exact (hEq.exitDepth_two_impossible (by omega)).elim
    · exact (hEq.largeDepth_hole_two_impossible hk).elim
    · have hr1 := hEq.exitDepth_eq_one_of_even_of_two_le_hole
          hkEven (by omega) han hr
      exact ⟨hkEven, haThree, hr1⟩
  · have haCases : a = 1 ∨ a = 2 ∨ 3 ≤ a := by omega
    rcases haCases with rfl | rfl | haThree
    · have hr1 := hEq.exitDepth_eq_one_of_odd_hole_one
          hkOdd (by omega) hr
      subst r
      exact (hEq.largeDepth_hole_one_exit_one_impossible hk).elim
    · exact (hEq.largeDepth_hole_two_impossible hk).elim
    · have hr2 := hEq.exitDepth_eq_two_of_odd_of_three_le_hole
          hkOdd haThree han hr hL
      subst r
      exact (hEq.exitDepth_two_impossible (by omega)).elim

/--
large-depth target-one では low-source `n=1,2` は消え、`n≥3` だけが残る。
その場合 exit depth は `k` の parity で exact に 1/2 に固定される。
-/
theorem TargetOneHoleEquation.largeDepth_shape
    {k n r L b : ℕ}
    (hk : 6 ≤ k)
    (hn : 0 < n) (hr : 0 < r)
    (hb : 0 < b) (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    3 ≤ n ∧
      ((k % 2 = 0 ∧ r = 1) ∨
       (k % 2 = 1 ∧ r = 2)) := by
  have hnCases : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
  rcases hnCases with rfl | rfl | hn3
  · exact (hEq.largeDepth_source_one_impossible hk).elim
  · exact (hEq.largeDepth_source_two_impossible hk).elim
  · constructor
    · exact hn3
    · rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
      · exact Or.inl ⟨hkEven,
          hEq.exitDepth_eq_one_of_largeSource_even hkEven hn3 hr⟩
      · exact Or.inr ⟨hkOdd,
          hEq.exitDepth_eq_two_of_largeSource_odd
            hkOdd hn3 hr hb hbL⟩

/-- 今回の large-depth reduction のまとめ。 -/
theorem oneHole_threeTail_largeDepth_ready :
    (∀ {k n r L : ℕ},
      6 ≤ k →
      SourceOneHoleEquation k n r L 2 → False) ∧
    (∀ {k r L b : ℕ},
      6 ≤ k →
      TargetOneHoleEquation k 1 r L b → False) ∧
    (∀ {k r L b : ℕ},
      6 ≤ k →
      TargetOneHoleEquation k 2 r L b → False) := by
  exact ⟨
    fun hk h => h.largeDepth_hole_two_impossible hk,
    fun hk h => h.largeDepth_source_one_impossible hk,
    fun hk h => h.largeDepth_source_two_impossible hk
  ⟩

end Mersenne
end Collatz3
