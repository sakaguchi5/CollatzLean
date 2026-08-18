import CollatzLean.Collatz2.CSTMicro.CarryGeometry.WeightedRankSmallResidueBridge

/-!
# General CST: canonical representative as an actual Collatz trace

parity cylinder の `leastRepresentative` は、これまで主に

  3^m * R + B ≡ 0 mod 2^k

を満たす canonical residue として扱ってきた。

このファイルでは whole affine equation が step-by-step parity trace を
実際に強制することを証明し、

  AffineRealizes v x y -> TraceRealizes v x y

を得る。

したがって既存

  representativeAffineEndpoint v
    = (3^m * leastRepresentative v + B) / 2^k

は単なる affine quotient ではなく、canonical representative から
word `v` を本当に辿った actual endpoint になる。

さらに同じ parity cylinder の全 lift

  R + n * 2^k

も exact trace を持ち、B first-failure upper word では `n = 0`
すなわち least representative だけが nondecreasing になり得ることを証明する。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. whole affine equation から exact parity trace を復元 -/

/--
`ZMod 2` で zero になる natural number は exact に `2 * (n/2)`。
parity extraction の小さな arithmetic helper。
-/
private theorem eq_two_mul_half_of_cast_zmod_two_eq_zero
    (n : ℕ)
    (h : ((n : ℕ) : ZMod 2) = 0) :
    n = 2 * (n / 2) := by
  have hv := congrArg ZMod.val h
  have hmod : n % 2 = 0 := by
    simpa [ZMod.val_natCast] using hv
  have hdecomp := Nat.mod_add_div n 2
  rw [hmod] at hdecomp
  omega

/--
false-step の affine equation から、開始値が even であることを
`ZMod 2` 上で抽出する。
-/
private theorem cast_zmod_two_eq_zero_of_false_affine_eq
    {n m B x y : ℕ}
    (hEq :
      2 ^ (n + 1) * y =
        3 ^ m * x + 2 * B) :
    ((x : ℕ) : ZMod 2) = 0 := by
  have hcast :=
    congrArg (fun t : ℕ => (t : ZMod 2)) hEq
  push_cast at hcast
  have htwo : (2 : ZMod 2) = 0 := by
    decide
  have hthree : (3 : ZMod 2) = 1 := by
    decide
  simpa [htwo, hthree, pow_succ] using hcast.symm


/--
true-step の affine equation から、`3*x+1` が even であることを
`ZMod 2` 上で抽出する。
-/
private theorem three_mul_add_one_cast_zmod_two_eq_zero_of_true_affine_eq
    {n m B x y : ℕ}
    (hEq :
      2 ^ (n + 1) * y =
        3 ^ (m + 1) * x +
          (3 ^ m + 2 * B)) :
    (((3 * x + 1 : ℕ)) : ZMod 2) = 0 := by
  have hcast :=
    congrArg (fun t : ℕ => (t : ZMod 2)) hEq
  push_cast at hcast ⊢
  have htwo : (2 : ZMod 2) = 0 := by
    decide
  have hthree : (3 : ZMod 2) = 1 := by
    decide
  simpa [
    htwo,
    hthree,
    pow_succ,
    add_comm,
    add_left_comm,
    add_assoc
  ] using hcast.symm

/--
`false :: v` の whole affine equation から、
最初の even step と tail の affine equation を復元する。
-/
private theorem exists_false_step_of_affineRealizes
    {v : ParityWord}
    {x y : ℕ}
    (h : AffineRealizes (false :: v) x y) :
    ∃ z : ℕ,
      x = 2 * z ∧
      AffineRealizes v z y := by
  have hEq := h
  unfold AffineRealizes at hEq
  simp only [
    List.length_cons,
    oddCount_false_cons,
    affineConst_false_cons
  ] at hEq
  have hxCast :
      ((x : ℕ) : ZMod 2) = 0 :=
    cast_zmod_two_eq_zero_of_false_affine_eq hEq
  let z : ℕ := x / 2
  have hx :
      x = 2 * z := by
    dsimp [z]
    exact
      eq_two_mul_half_of_cast_zmod_two_eq_zero
        x hxCast
  have hTail :
      AffineRealizes v z y := by
    unfold AffineRealizes
    have hTwo :
        2 * (2 ^ v.length * y) =
          2 * (3 ^ oddCount v * z + affineConst v) := by
      calc
        2 * (2 ^ v.length * y)
            = 2 ^ (v.length + 1) * y := by
              rw [pow_succ]
              ring
        _ =
            3 ^ oddCount v * x +
              2 * affineConst v :=
          hEq
        _ =
            2 * (3 ^ oddCount v * z +
              affineConst v) := by
          rw [hx]
          ring
    omega
  exact ⟨z, hx, hTail⟩

/--
`true :: v` の whole affine equation から、
最初の odd Collatz step と tail の affine equation を復元する。
-/
private theorem exists_true_step_of_affineRealizes
    {v : ParityWord}
    {x y : ℕ}
    (h : AffineRealizes (true :: v) x y) :
    ∃ z : ℕ,
      3 * x + 1 = 2 * z ∧
      AffineRealizes v z y := by
  have hEq := h
  unfold AffineRealizes at hEq
  simp only [
    List.length_cons,
    oddCount_true_cons,
    affineConst_true_cons
  ] at hEq
  have hStepCast :
      (((3 * x + 1 : ℕ)) : ZMod 2) = 0 :=
    three_mul_add_one_cast_zmod_two_eq_zero_of_true_affine_eq
      hEq
  let z : ℕ := (3 * x + 1) / 2
  have hx :
      3 * x + 1 = 2 * z := by
    dsimp [z]
    exact
      eq_two_mul_half_of_cast_zmod_two_eq_zero
        (3 * x + 1) hStepCast
  have hTail :
      AffineRealizes v z y := by
    unfold AffineRealizes
    have hTwo :
        2 * (2 ^ v.length * y) =
          2 * (3 ^ oddCount v * z + affineConst v) := by
      calc
        2 * (2 ^ v.length * y)
            = 2 ^ (v.length + 1) * y := by
              rw [pow_succ]
              ring
        _ =
            3 ^ (oddCount v + 1) * x +
              (3 ^ oddCount v +
                2 * affineConst v) :=
          hEq
        _ =
            3 ^ oddCount v * (3 * x + 1) +
              2 * affineConst v := by
          rw [pow_succ]
          ring
        _ =
            2 * (3 ^ oddCount v * z +
              affineConst v) := by
          rw [hx]
          ring
    omega
  exact ⟨z, hx, hTail⟩

/--
whole affine equation は parity word の step-by-step trace を強制する。

この theorem により `ExactRealizes` の trace 成分は
affine equation から復元可能。
-/
theorem traceRealizes_of_affineRealizes
    {v : ParityWord}
    {x y : ℕ}
    (h : AffineRealizes v x y) :
    TraceRealizes v x y := by
  induction v generalizing x y with
  | nil =>
      unfold AffineRealizes at h
      simp [TraceRealizes, affineConst, oddCount] at h ⊢
      omega
  | cons b v ih =>
      cases b
      · rcases exists_false_step_of_affineRealizes h with
          ⟨z, hx, hTail⟩
        unfold TraceRealizes
        exact ⟨z, hx, ih hTail⟩
      · rcases exists_true_step_of_affineRealizes h with
          ⟨z, hx, hTail⟩
        unfold TraceRealizes
        exact ⟨z, hx, ih hTail⟩

/-- `ExactRealizes` は実際には whole affine equation と同値。 -/
theorem exactRealizes_iff_affineRealizes
    (v : ParityWord)
    (x y : ℕ) :
    ExactRealizes v x y ↔ AffineRealizes v x y := by
  constructor
  · intro h
    exact h.affine
  · intro h
    exact ⟨traceRealizes_of_affineRealizes h, h⟩

/-! ## 2. least representative の canonical actual trace -/

/--
least representative と既存 canonical endpoint は whole affine equation を満たす。
-/
theorem leastRepresentative_affineRealizes
    (v : ParityWord) :
    AffineRealizes v
      (leastRepresentative v)
      (representativeAffineEndpoint v) := by
  unfold AffineRealizes
  simpa [parityModulus] using
    parityModulus_mul_representativeAffineEndpoint v

/--
least representative は本当に word `v` を step-by-step 辿り、
既存 `representativeAffineEndpoint` へ到達する。
-/
theorem leastRepresentative_exactRealizes
    (v : ParityWord) :
    ExactRealizes v
      (leastRepresentative v)
      (representativeAffineEndpoint v) := by
  exact
    (exactRealizes_iff_affineRealizes
      v (leastRepresentative v) (representativeAffineEndpoint v)).2
      (leastRepresentative_affineRealizes v)

/-! ## 3. parity cylinder 全体の actual lift -/

/--
同じ parity cylinder の全 natural lift は whole affine equation を exact に保つ。

  start_n    = R + n * 2^k
  endpoint_n = E + n * 3^m
-/
theorem leastRepresentative_cylinder_affineRealizes
    (v : ParityWord)
    (n : ℕ) :
    AffineRealizes v
      (leastRepresentative v + n * parityModulus v)
      (representativeAffineEndpoint v + n * 3 ^ oddCount v) := by
  have hBase :=
    parityModulus_mul_representativeAffineEndpoint v
  unfold AffineRealizes
  unfold parityModulus at hBase ⊢
  calc
    2 ^ v.length *
        (representativeAffineEndpoint v + n * 3 ^ oddCount v)
        =
      2 ^ v.length * representativeAffineEndpoint v +
        n * (2 ^ v.length * 3 ^ oddCount v) := by
          ring
    _ =
      (3 ^ oddCount v * leastRepresentative v + affineConst v) +
        n * (2 ^ v.length * 3 ^ oddCount v) := by
          rw [hBase]
    _ =
      3 ^ oddCount v *
          (leastRepresentative v + n * 2 ^ v.length) +
        affineConst v := by
          ring

/--
同じ parity cylinder の全 natural lift は同じ parity word を actual に辿る。
-/
theorem leastRepresentative_cylinder_exactRealizes
    (v : ParityWord)
    (n : ℕ) :
    ExactRealizes v
      (leastRepresentative v + n * parityModulus v)
      (representativeAffineEndpoint v + n * 3 ^ oddCount v) := by
  exact
    (exactRealizes_iff_affineRealizes
      v
      (leastRepresentative v + n * parityModulus v)
      (representativeAffineEndpoint v + n * 3 ^ oddCount v)).2
      (leastRepresentative_cylinder_affineRealizes v n)

/-! ## 4. B first-failure upper cylinder -/

namespace FirstFailureEdge

/--
first-failure upper の canonical affine endpoint は exact に `R + q`。
-/
theorem upper_representativeAffineEndpoint_eq_upperR_add_upperNormalizedDefectNat
    (F : FirstFailureEdge) :
    representativeAffineEndpoint F.step.edge.upperWord =
      F.step.edge.upperR + F.upperNormalizedDefectNat := by
  have hle :
      F.step.edge.upperR ≤
        representativeAffineEndpoint F.step.edge.upperWord := by
    simpa [AdjacentFerrersSwap.upperR] using
      F.upperR_le_representativeAffineEndpoint
  unfold upperNormalizedDefectNat
  unfold AdjacentFerrersSwap.upperR at hle ⊢
  omega

/--
first-failure upper least representative は actual near-return を実現する。

  R_upper --upperWord--> R_upper + q.
-/
theorem upperCanonical_exactRealizes
    (F : FirstFailureEdge) :
    ExactRealizes F.step.edge.upperWord
      F.step.edge.upperR
      (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
  have h :=
    leastRepresentative_exactRealizes F.step.edge.upperWord
  rw [
    F.upper_representativeAffineEndpoint_eq_upperR_add_upperNormalizedDefectNat
  ] at h
  simpa [AdjacentFerrersSwap.upperR] using h

/--
first-failure upper parity cylinder の任意の lift も actual trace を実現する。
-/
theorem upperCylinder_exactRealizes
    (F : FirstFailureEdge)
    (n : ℕ) :
    ExactRealizes F.step.edge.upperWord
      (F.step.edge.upperR + n * F.step.edge.modulus)
      (representativeAffineEndpoint F.step.edge.upperWord +
        n * 3 ^ F.step.edge.oddTotal) := by
  have h :=
    leastRepresentative_cylinder_exactRealizes
      F.step.edge.upperWord n
  rw [
    F.step.edge.parityModulus_upperWord,
    F.step.edge.upperWord_oddCount
  ] at h
  simpa [AdjacentFerrersSwap.upperR] using h

/-- first-failure upper の natural `q` は terminal gap より strict に小さい。 -/
theorem upperNormalizedDefectNat_lt_terminalGap
    (F : FirstFailureEdge) :
    F.upperNormalizedDefectNat <
      wordTerminalGap F.step.edge.upperWord := by
  let D := F.toFirstFailureFareyData
  have hqD :
      (F.upperNormalizedDefectNat : ℤ) < D.farey.residue := by
    rw [F.upperNormalizedDefectNat_cast]
    exact D.upper_normalizedSeparationDefectInt_lt_residue
  have hqG :
      (F.upperNormalizedDefectNat : ℤ) <
        (wordTerminalGap F.step.edge.upperWord : ℤ) := by
    calc
      (F.upperNormalizedDefectNat : ℤ)
          < D.farey.residue := hqD
      _ < D.farey.G := D.residue_lt_gap
      _ = (wordTerminalGap F.step.edge.lowerWord : ℤ) :=
        D.farey_G_eq_wordTerminalGap
      _ = (wordTerminalGap F.step.edge.upperWord : ℤ) := by
        rw [F.step.edge.wordTerminalGap_eq]
  exact_mod_cast hqG

/--
upper cylinder の index `n > 0` の lift は terminal endpoint で strict に減少する。

したがって dangerous/nondecreasing になり得るのは least representative 側だけ。
-/
theorem upperCylinder_decreases_of_pos
    (F : FirstFailureEdge)
    {n : ℕ}
    (hn : 0 < n) :
    representativeAffineEndpoint F.step.edge.upperWord +
        n * 3 ^ F.step.edge.oddTotal <
      F.step.edge.upperR + n * F.step.edge.modulus := by
  have hThree :
      3 ^ F.step.edge.oddTotal < F.step.edge.modulus :=
    F.upper_threePow_lt_modulus
  have hThreeLe :
      3 ^ F.step.edge.oddTotal ≤ F.step.edge.modulus :=
    Nat.le_of_lt hThree
  have hqGap := F.upperNormalizedDefectNat_lt_terminalGap
  have hqBase :
      F.upperNormalizedDefectNat + 3 ^ F.step.edge.oddTotal <
        F.step.edge.modulus := by
    rw [F.step.edge.wordTerminalGap_upperWord] at hqGap
    have hCancel :
        F.step.edge.modulus - 3 ^ F.step.edge.oddTotal +
            3 ^ F.step.edge.oddTotal =
          F.step.edge.modulus :=
      Nat.sub_add_cancel hThreeLe
    omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hTail :
      t * 3 ^ F.step.edge.oddTotal ≤
        t * F.step.edge.modulus :=
    Nat.mul_le_mul_left t hThreeLe
  have hCore :
      F.upperNormalizedDefectNat +
          (t + 1) * 3 ^ F.step.edge.oddTotal <
        (t + 1) * F.step.edge.modulus := by
    calc
      F.upperNormalizedDefectNat +
          (t + 1) * 3 ^ F.step.edge.oddTotal
          =
        (F.upperNormalizedDefectNat + 3 ^ F.step.edge.oddTotal) +
          t * 3 ^ F.step.edge.oddTotal := by
            ring
      _ <
        F.step.edge.modulus +
          t * 3 ^ F.step.edge.oddTotal :=
            Nat.add_lt_add_right hqBase _
      _ ≤
        F.step.edge.modulus + t * F.step.edge.modulus :=
          Nat.add_le_add_left hTail _
      _ = (t + 1) * F.step.edge.modulus := by
        ring
  rw [
    F.upper_representativeAffineEndpoint_eq_upperR_add_upperNormalizedDefectNat
  ]
  calc
    F.step.edge.upperR + F.upperNormalizedDefectNat +
        (t + 1) * 3 ^ F.step.edge.oddTotal
        =
      F.step.edge.upperR +
        (F.upperNormalizedDefectNat +
          (t + 1) * 3 ^ F.step.edge.oddTotal) := by
            ring
    _ <
      F.step.edge.upperR +
        ((t + 1) * F.step.edge.modulus) :=
          Nat.add_lt_add_left hCore _
    _ =
      F.step.edge.upperR +
        (t + 1) * F.step.edge.modulus := rfl

/--
同じ upper parity cylinder では、terminal endpoint が start 以上になることと
`n = 0` が同値。

これは least representative が cylinder 内の唯一の nondecreasing start
であることの exact statement。
-/
theorem upperCylinder_nondecreasing_iff_index_zero
    (F : FirstFailureEdge)
    (n : ℕ) :
    F.step.edge.upperR + n * F.step.edge.modulus ≤
        representativeAffineEndpoint F.step.edge.upperWord +
          n * 3 ^ F.step.edge.oddTotal
      ↔
    n = 0 := by
  constructor
  · intro hNondec
    by_contra hn
    have hnPos : 0 < n := by omega
    have hDec := F.upperCylinder_decreases_of_pos hnPos
    omega
  · intro hn
    subst n
    simp only [zero_mul, add_zero]
    simpa [AdjacentFerrersSwap.upperR] using
      F.upperR_le_representativeAffineEndpoint

end FirstFailureEdge

end CSTMicro
end Collatz2
