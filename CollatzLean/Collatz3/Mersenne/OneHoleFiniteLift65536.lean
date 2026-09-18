import CollatzLean.Collatz3.Mersenne.OneHoleFiniteTailLoopSieve
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: one-hole finite lift to mod 65536

one-hole finite sieve の第2段。

前段では

* source resonance `a=2`: `k mod 256` を10 class、
* target low-source `n=1`: `k mod 256` を8 class

まで絞った。

ここでは

`M₃ = 2^8 * 5 * 17 * 257 * 65537 = 366503875840`

へ lift する。この modulus 上では

* `2` は tail 8、その後 period 32、
* `3` は period 65536

となる。

重要なのは、`k` を 65536 class 全体から再探索しないこと。
前段の surviving `mod 256` class を各256通りだけ lift し、
`3^(c+256j) = 3^c * (3^256)^j` を使って有限計算を軽くする。

source resonance では odd `k` を既に知っているため、前段10 class から
`0,254` を除いた8 classだけを lift する。
-/

namespace Collatz3
namespace Mersenne

/-! ## M₃ tail/loop certificate -/

/-- `mod 366503875840` では 2冪は tail 8、その後 period 32。 -/
theorem powTailLoop_two_mod366503875840 :
    PowTailLoop 366503875840 2 8 32 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- `mod 366503875840` では 3 は unit で period 65536。 -/
theorem powTailLoop_three_mod366503875840 :
    PowTailLoop 366503875840 3 0 65536 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- `mod 366503875840` の combined certificate。 -/
theorem pow23TailLoops_mod366503875840 :
    Pow23TailLoops 366503875840 8 32 0 65536 :=
  ⟨powTailLoop_two_mod366503875840,
    powTailLoop_three_mod366503875840⟩


/-! ## 共通: old residue class の lift -/

/-- source resonance で前段から残る odd `k mod 256` の8 class。 -/
private def sourceOldOddClass (i : Fin 8) : ℕ :=
  match i.1 with
  | 0 => 1
  | 1 => 5
  | 2 => 85
  | 3 => 125
  | 4 => 127
  | 5 => 149
  | 6 => 253
  | _ => 255

/-- target `n=1` で前段から残る `k mod 256` の8 class。 -/
private def targetOldClass (i : Fin 8) : ℕ :=
  match i.1 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 48
  | 6 => 128
  | _ => 208

/-- 一つの old class を `mod 65536` へ256通り lift する。 -/
private def liftK256 (c : ℕ) (j : Fin 256) : ℕ :=
  c + 256 * j.1

/-- `3^(c+256j)` を lift 形のまま評価する。 -/
private def threePowLift256
    (c : ℕ) (j : Fin 256) : ZMod 366503875840 :=
  (3 : ZMod 366503875840) ^ c *
    ((3 : ZMod 366503875840) ^ 256) ^ j.1

/-- lift 形は通常の power と一致する。 -/
private theorem threePowLift256_eq
    (c : ℕ) (j : Fin 256) :
    threePowLift256 c j =
      (3 : ZMod 366503875840) ^ (liftK256 c j) := by
  unfold threePowLift256 liftK256
  rw [pow_add, pow_mul]


/-! ## source one-hole resonance `a=2` -/

/--
第2段で残る source resonance の `k mod 65536`。

前段の odd residue 8 class を各256通り lift したあと、
`M₃` の modular equation を通過するのは14 classだけ。
-/
def SourceOneHoleKResidue65536 (K : ℕ) : Prop :=
  K = 1 ∨ K = 5 ∨
  K = 3069 ∨ K = 3071 ∨
  K = 10237 ∨ K = 10239 ∨
  K = 32765 ∨ K = 32767 ∨
  K = 52221 ∨ K = 52223 ∨
  K = 55293 ∨ K = 55295 ∨
  K = 65533 ∨ K = 65535

/-- source resonance の lift 左辺。 -/
private def sourceOneHoleLiftLhs
    (i : Fin 8) (j : Fin 256) (N : ℕ) : ZMod 366503875840 :=
  threePowLift256 (sourceOldOddClass i) j *
    ((2 : ZMod 366503875840) ^ N - 1 -
      (2 : ZMod 366503875840) ^ 2)

/-- source-one の `M₃` 右辺。 -/
private def sourceOneHoleLiftRhs
    (R L : ℕ) : ZMod 366503875840 :=
  (2 : ZMod 366503875840) ^ R *
      ((2 : ZMod 366503875840) ^ L - 1) + 1

/-- `M₃` 上で到達可能な source-one RHS residue table。 -/
private def sourceOneHoleLiftRhsTable : List ℕ :=
  ((List.range 40).flatMap fun R =>
    (List.range 40).map fun L =>
      (sourceOneHoleLiftRhs R L).val).eraseDups

/-- 任意の finite RHS witness は table に入る。 -/
private theorem sourceOneHoleLiftRhs_mem
    (R L : Fin 40) :
    (sourceOneHoleLiftRhs R.1 L.1).val ∈
      sourceOneHoleLiftRhsTable := by
  simp only [sourceOneHoleLiftRhsTable, List.mem_eraseDups,
    List.mem_flatMap, List.mem_map]
  exact ⟨R.1, List.mem_range.mpr R.2,
    L.1, List.mem_range.mpr L.2, rfl⟩

/-- 一つの lifted `k` が source equation を通過しうること。 -/
private def sourceOneHoleLiftSurvives
    (i : Fin 8) (j : Fin 256) : Prop :=
  ∃ N : Fin 40,
    (sourceOneHoleLiftLhs i j N.1).val ∈
      sourceOneHoleLiftRhsTable

/--
source resonance の第2段 finite certificate。

探索対象は `8 * 256` 個の lifted `k` だけ。
各 `k` では 2-exponent representative `N<40` を調べる。
-/
private theorem sourceOneHole_lift65536_finite_sieve :
    ∀ i : Fin 8,
      ∀ j : Fin 256,
        sourceOneHoleLiftSurvives i j →
          SourceOneHoleKResidue65536
            (liftK256 (sourceOldOddClass i) j) := by
  unfold sourceOneHoleLiftSurvives
  unfold SourceOneHoleKResidue65536
  native_decide

/-- 前段の source residue と oddness から old odd class を一つ取る。 -/
private theorem exists_sourceOldOddClass
    {k : ℕ}
    (hOld : SourceOneHoleKResidue256 (k % 256))
    (hkOdd : k % 2 = 1) :
    ∃ i : Fin 8, k % 256 = sourceOldOddClass i := by
  have hParity : (k % 256) % 2 = k % 2 := by
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  unfold SourceOneHoleKResidue256 at hOld
  rcases hOld with h0 | h1 | h5 | h85 | h125 | h127 |
      h149 | h253 | h254 | h255
  · rw [h0, hkOdd] at hParity
    norm_num at hParity
  · exact ⟨⟨0, by norm_num⟩, by simpa [sourceOldOddClass] using h1⟩
  · exact ⟨⟨1, by norm_num⟩, by simpa [sourceOldOddClass] using h5⟩
  · exact ⟨⟨2, by norm_num⟩, by simpa [sourceOldOddClass] using h85⟩
  · exact ⟨⟨3, by norm_num⟩, by simpa [sourceOldOddClass] using h125⟩
  · exact ⟨⟨4, by norm_num⟩, by simpa [sourceOldOddClass] using h127⟩
  · exact ⟨⟨5, by norm_num⟩, by simpa [sourceOldOddClass] using h149⟩
  · exact ⟨⟨6, by norm_num⟩, by simpa [sourceOldOddClass] using h253⟩
  · rw [h254, hkOdd] at hParity
    norm_num at hParity
  · exact ⟨⟨7, by norm_num⟩, by simpa [sourceOldOddClass] using h255⟩

/--
source resonance `a=2`, odd `k` は第2段で14個の `mod 65536` class に限られる。
-/
theorem SourceOneHoleEquation.k_mod_65536_of_hole_two_odd
    {k n r L : ℕ}
    (hkOdd : k % 2 = 1)
    (hEq : SourceOneHoleEquation k n r L 2) :
    SourceOneHoleKResidue65536 (k % 65536) := by
  have hOld := hEq.k_mod_256_of_hole_two
  rcases exists_sourceOldOddClass hOld hkOdd with ⟨i, hi⟩
  let K : ℕ := k % 65536
  have hKlt : K < 65536 := by
    dsimp [K]
    exact Nat.mod_lt _ (by norm_num)
  have hKmod256 : K % 256 = sourceOldOddClass i := by
    dsimp [K]
    have hmod : (k % 65536) % 256 = k % 256 := by
       simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hi]
  let J : ℕ := K / 256
  have hJlt : J < 256 := by
    dsimp [J]
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 256)).2
    simpa using hKlt
  let Jf : Fin 256 := ⟨J, hJlt⟩
  have hLiftK : liftK256 (sourceOldOddClass i) Jf = K := by
    have hDecomp := Nat.mod_add_div K 256
    rw [hKmod256] at hDecomp
    dsimp [liftK256, Jf, J]
    omega
  have hMod := hEq.to_mod 366503875840
  have hRed :=
    hMod.reduce_tailLoop pow23TailLoops_mod366503875840
  let N : ℕ := tailLoopExponent 8 32 n
  let R : ℕ := tailLoopExponent 8 32 r
  let T : ℕ := tailLoopExponent 8 32 L
  have hNlt : N < 40 := by
    dsimp [N]
    have h := powTailLoop_two_mod366503875840.tailLoopExponent_lt (e := n)
    norm_num at h ⊢
    exact h
  have hRlt : R < 40 := by
    dsimp [R]
    have h := powTailLoop_two_mod366503875840.tailLoopExponent_lt (e := r)
    norm_num at h ⊢
    exact h
  have hTlt : T < 40 := by
    dsimp [T]
    have h := powTailLoop_two_mod366503875840.tailLoopExponent_lt (e := L)
    norm_num at h ⊢
    exact h
  let Nf : Fin 40 := ⟨N, hNlt⟩
  let Rf : Fin 40 := ⟨R, hRlt⟩
  let Tf : Fin 40 := ⟨T, hTlt⟩
  have hEqFinite :
      SourceOneHoleModEquation 366503875840
        (liftK256 (sourceOldOddClass i) Jf)
        Nf.1 Rf.1 Tf.1 2 := by
    rw [hLiftK]
    dsimp [K, Nf, Rf, Tf, N, R, T]
    simpa [tailLoopExponent] using hRed
  have hSurvive : sourceOneHoleLiftSurvives i Jf := by
    refine ⟨Nf, ?_⟩
    have hEqZ :
        sourceOneHoleLiftLhs i Jf Nf.1 =
          sourceOneHoleLiftRhs Rf.1 Tf.1 := by
      simpa [sourceOneHoleLiftLhs, sourceOneHoleLiftRhs,
        SourceOneHoleModEquation, threePowLift256_eq] using hEqFinite
    have hEqVal := congrArg ZMod.val hEqZ
    change (sourceOneHoleLiftLhs i Jf Nf.1).val ∈
      sourceOneHoleLiftRhsTable
    rw [hEqVal]
    exact sourceOneHoleLiftRhs_mem Rf Tf
  have hFinite :=
    sourceOneHole_lift65536_finite_sieve i Jf hSurvive
  rw [hLiftK] at hFinite
  simpa [K] using hFinite


/-! ## target one-hole low-source `n=1,2` -/

/--
第2段で残る target `n=1` の `k mod 65536`。
-/
def TargetOneHoleSourceOneKResidue65536 (K : ℕ) : Prop :=
  K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨
  K = 3072 ∨ K = 10240 ∨ K = 32768 ∨
  K = 52224 ∨ K = 55296

/-- target low-source の lift 左辺。 -/
private def targetOneHoleLiftLhs
    (i : Fin 8) (j : Fin 256) : ZMod 366503875840 :=
  threePowLift256 (targetOldClass i) j

/-- target-one の `M₃` RHS。 -/
private def targetOneHoleLiftRhs
    (R L B : ℕ) : ZMod 366503875840 :=
  (2 : ZMod 366503875840) ^ R *
      ((2 : ZMod 366503875840) ^ L - 1 -
        (2 : ZMod 366503875840) ^ B) + 1

/-- target-one RHS table。重複を落として lookup を軽くする。 -/
private def targetOneHoleLiftRhsTable : List ℕ :=
  ((List.range 40).flatMap fun R =>
    (List.range 40).flatMap fun L =>
      (List.range 40).map fun B =>
        (targetOneHoleLiftRhs R L B).val).eraseDups

/-- 任意の finite target RHS witness は table に入る。 -/
private theorem targetOneHoleLiftRhs_mem
    (R L B : Fin 40) :
    (targetOneHoleLiftRhs R.1 L.1 B.1).val ∈
      targetOneHoleLiftRhsTable := by
  simp only [targetOneHoleLiftRhsTable, List.mem_eraseDups,
    List.mem_flatMap, List.mem_map]
  exact ⟨R.1, List.mem_range.mpr R.2,
    L.1, List.mem_range.mpr L.2,
    B.1, List.mem_range.mpr B.2, rfl⟩

/-- 一つの target lift が modular equation を通過しうること。 -/
private def targetOneHoleLiftSurvives
    (i : Fin 8) (j : Fin 256) : Prop :=
  (targetOneHoleLiftLhs i j).val ∈ targetOneHoleLiftRhsTable

/-- target low-source の第2段 finite certificate。 -/
private theorem targetOneHole_lift65536_finite_sieve :
    ∀ i : Fin 8,
      ∀ j : Fin 256,
        targetOneHoleLiftSurvives i j →
          TargetOneHoleSourceOneKResidue65536
            (liftK256 (targetOldClass i) j) := by
  unfold targetOneHoleLiftSurvives
  unfold TargetOneHoleSourceOneKResidue65536
  native_decide

/-- 前段 target residue predicate を old class index に戻す。 -/
private theorem exists_targetOldClass
    {k : ℕ}
    (hOld : TargetOneHoleSourceOneKResidue256 (k % 256)) :
    ∃ i : Fin 8, k % 256 = targetOldClass i := by
  unfold TargetOneHoleSourceOneKResidue256 at hOld
  rcases hOld with h0 | h1 | h2 | h3 | h4 | h48 | h128 | h208
  · exact ⟨⟨0, by norm_num⟩, by simpa [targetOldClass] using h0⟩
  · exact ⟨⟨1, by norm_num⟩, by simpa [targetOldClass] using h1⟩
  · exact ⟨⟨2, by norm_num⟩, by simpa [targetOldClass] using h2⟩
  · exact ⟨⟨3, by norm_num⟩, by simpa [targetOldClass] using h3⟩
  · exact ⟨⟨4, by norm_num⟩, by simpa [targetOldClass] using h4⟩
  · exact ⟨⟨5, by norm_num⟩, by simpa [targetOldClass] using h48⟩
  · exact ⟨⟨6, by norm_num⟩, by simpa [targetOldClass] using h128⟩
  · exact ⟨⟨7, by norm_num⟩, by simpa [targetOldClass] using h208⟩

/-- `n=1` target-one は第2段で10個の `mod 65536` class に限られる。 -/
theorem TargetOneHoleEquation.k_mod_65536_of_source_one
    {k r L b : ℕ}
    (hEq : TargetOneHoleEquation k 1 r L b) :
    TargetOneHoleSourceOneKResidue65536 (k % 65536) := by
  have hOld := hEq.k_mod_256_of_source_one
  rcases exists_targetOldClass hOld with ⟨i, hi⟩
  let K : ℕ := k % 65536
  have hKlt : K < 65536 := by
    dsimp [K]
    exact Nat.mod_lt _ (by norm_num)
  have hKmod256 : K % 256 = targetOldClass i := by
    dsimp [K]
    have hmod : (k % 65536) % 256 = k % 256 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hi]
  let J : ℕ := K / 256
  have hJlt : J < 256 := by
    dsimp [J]
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 256)).2
    simpa using hKlt
  let Jf : Fin 256 := ⟨J, hJlt⟩
  have hLiftK : liftK256 (targetOldClass i) Jf = K := by
    have hDecomp := Nat.mod_add_div K 256
    rw [hKmod256] at hDecomp
    dsimp [liftK256, Jf, J]
    omega
  have hMod := hEq.to_mod 366503875840
  have hRed :=
    hMod.reduce_tailLoop pow23TailLoops_mod366503875840
  let R : ℕ := tailLoopExponent 8 32 r
  let T : ℕ := tailLoopExponent 8 32 L
  let B : ℕ := tailLoopExponent 8 32 b
  have hRlt : R < 40 := by
    dsimp [R]
    have h := powTailLoop_two_mod366503875840.tailLoopExponent_lt (e := r)
    norm_num at h ⊢
    exact h
  have hTlt : T < 40 := by
    dsimp [T]
    have h := powTailLoop_two_mod366503875840.tailLoopExponent_lt (e := L)
    norm_num at h ⊢
    exact h
  have hBlt : B < 40 := by
    dsimp [B]
    have h := powTailLoop_two_mod366503875840.tailLoopExponent_lt (e := b)
    norm_num at h ⊢
    exact h
  let Rf : Fin 40 := ⟨R, hRlt⟩
  let Tf : Fin 40 := ⟨T, hTlt⟩
  let Bf : Fin 40 := ⟨B, hBlt⟩
  have hEqFinite :
      TargetOneHoleModEquation 366503875840
        (liftK256 (targetOldClass i) Jf)
        1 Rf.1 Tf.1 Bf.1 := by
    rw [hLiftK]
    dsimp [K, Rf, Tf, Bf, R, T, B]
    simpa [tailLoopExponent] using hRed
  have hSurvive : targetOneHoleLiftSurvives i Jf := by
    have hEqFinite' := hEqFinite
    unfold TargetOneHoleModEquation at hEqFinite'
    norm_num at hEqFinite'
    have hEqZ :
        targetOneHoleLiftLhs i Jf =
          targetOneHoleLiftRhs Rf.1 Tf.1 Bf.1 := by
      simpa [targetOneHoleLiftLhs, targetOneHoleLiftRhs,
        threePowLift256_eq] using hEqFinite'
    have hEqVal :
        (targetOneHoleLiftLhs i Jf).val =
          (targetOneHoleLiftRhs Rf.1 Tf.1 Bf.1).val :=
      congrArg ZMod.val hEqZ
    change (targetOneHoleLiftLhs i Jf).val ∈
      targetOneHoleLiftRhsTable
    rw [hEqVal]
    exact targetOneHoleLiftRhs_mem Rf Tf Bf
  have hFinite :=
    targetOneHole_lift65536_finite_sieve i Jf hSurvive
  rw [hLiftK] at hFinite
  simpa [K] using hFinite

/--
`n=2` は `n=1, depth=k+1` へ移るので、
`(k+1) mod 65536` が同じ10 class に限られる。
-/
theorem TargetOneHoleEquation.succ_k_mod_65536_of_source_two
    {k r L b : ℕ}
    (hEq : TargetOneHoleEquation k 2 r L b) :
    TargetOneHoleSourceOneKResidue65536 ((k + 1) % 65536) := by
  exact
    hEq.source_two_to_source_one.k_mod_65536_of_source_one


/-! ## 第2段 summary -/

/--
source resonance と target low-source の `mod 65536` lift が閉じている。
-/
theorem oneHole_secondFiniteSieve_ready :
    (∀ {k n r L : ℕ},
      k % 2 = 1 →
      SourceOneHoleEquation k n r L 2 →
      SourceOneHoleKResidue65536 (k % 65536)) ∧
    (∀ {k r L b : ℕ},
      TargetOneHoleEquation k 1 r L b →
      TargetOneHoleSourceOneKResidue65536 (k % 65536)) ∧
    (∀ {k r L b : ℕ},
      TargetOneHoleEquation k 2 r L b →
      TargetOneHoleSourceOneKResidue65536 ((k + 1) % 65536)) := by
  exact ⟨
    fun hk h => h.k_mod_65536_of_hole_two_odd hk,
    fun h => h.k_mod_65536_of_source_one,
    fun h => h.succ_k_mod_65536_of_source_two
  ⟩

end Mersenne
end Collatz3
