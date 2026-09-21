import CollatzLean.Collatz3.Mersenne.SourceTwoHoleRegularProof
import CollatzLean.Collatz3.Mersenne.ThreeTailModular
import Std.Data.HashSet.Lemmas
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: source-two low resonance の M₄ reduction

`SourceTwoHoleRegularProof` により `k≥7` の source-two は

* even `k`, `(a,b)=(1,2)`,
* odd `k`, `a=2`,

という二つの low resonance にしか残らない。

このファイルでは共通 modulus

`M₄ = 3^6 * 7 * 19 * 73 * 163 * 487 = 561847684041`

を使い、resonance を 3-adic tail / 2-adic loop の有限状態へ送る。

重要なのは M₄ の役割を過大評価しないことである。

even resonance `(a,b)=(1,2)` は M₄ だけで

`k ≡ 972 (tail 972), n ≡ 394, r ≡ 3, L ≡ 391 (mod 486)`

という単一 residual class まで縮む。一方 odd resonance `a=2` は
M₄ 単独では survivor が残るので、この層では有限状態への reduction までを
無条件 theorem として固定する。

外部 S-unit / Baker 型入力は使用しない。
-/

namespace Collatz3
namespace Mersenne

/-! ## 共通: large depth では exit depth は少なくとも 3 -/

/--
`k≥7` の well-formed source-two では `r=1,2` はともに不可能なので `r≥3`。

`r=1` は既存の large-depth regular equation 排除、`r=2` は mod 3 排除を使う。
resonance の形そのものはここでは仮定しない。
-/
theorem SourceTwoHoleEquation.largeDepth_exitDepth_ge_three
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    3 ≤ r := by
  by_contra hNot
  have hrCases : r = 1 ∨ r = 2 := by omega
  rcases hrCases with rfl | rfl
  · exact hEq.largeDepth_exit_one_impossible hk7 ha0 hab hbn hL
  · exact hEq.exitDepth_two_impossible (by omega)

/-! ## M₄ 上の共通 residue -/

/-- source-two の target side residue。 -/
private def sourceTwoThreeTailRhs
    (R T : ℕ) : ZMod ThreeTail.modulus :=
  (2 : ZMod ThreeTail.modulus) ^ R *
      ((2 : ZMod ThreeTail.modulus) ^ T - 1) + 1

/-- `(R,T)` 全 486² 通りの reachable target residue。 -/
private def sourceTwoThreeTailRhsList : List ℕ :=
  (List.range 486).flatMap fun R =>
    (List.range 486).map fun T =>
      (sourceTwoThreeTailRhs R T).val

private def sourceTwoThreeTailRhsSet : Std.HashSet ℕ :=
  Std.HashSet.ofList sourceTwoThreeTailRhsList

private theorem sourceTwoThreeTailRhsSet_contains
    (R T : Fin 486) :
    sourceTwoThreeTailRhsSet.contains
        (sourceTwoThreeTailRhs R.1 T.1).val = true := by
  have hMem :
      (sourceTwoThreeTailRhs R.1 T.1).val ∈ sourceTwoThreeTailRhsList := by
    unfold sourceTwoThreeTailRhsList
    apply List.mem_flatMap.mpr
    refine ⟨R.1, List.mem_range.mpr R.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨T.1, List.mem_range.mpr T.2, rfl⟩
  simpa only [
    sourceTwoThreeTailRhsSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/-! ## even resonance `(a,b)=(1,2)` -/

private def sourceTwoEvenResonanceLhs
    (K N : ℕ) : ZMod ThreeTail.modulus :=
  (3 : ZMod ThreeTail.modulus) ^ K *
    ((2 : ZMod ThreeTail.modulus) ^ N - 1 -
      (2 : ZMod ThreeTail.modulus) ^ 1 -
      (2 : ZMod ThreeTail.modulus) ^ 2)

/--
M₄ finite certificate の第1段。

全 972 個の 3-tail state と全 486 個の source-width state を調べると、
target reachable set と交わるのは `J=966, N=394` だけ。
`K = 6+J` なので 3-exponent representative は 972 である。
-/
private theorem sourceTwoEvenResonance_m4_source_sieve :
    ∀ J : Fin 972,
      ∀ N : Fin 486,
        sourceTwoThreeTailRhsSet.contains
            (sourceTwoEvenResonanceLhs
              (ThreeTail.largeDepthKRep J) N.1).val = true →
          J.1 = 966 ∧ N.1 = 394 := by
  native_decide

/--
M₄ finite certificate の第2段。

固定された左 residue `(K,N)=(972,394)` と一致する target residue は
`(R,T)=(3,391)` だけ。
-/
private theorem sourceTwoEvenResonance_m4_target_sieve :
    ∀ R T : Fin 486,
      (sourceTwoThreeTailRhs R.1 T.1).val =
          (sourceTwoEvenResonanceLhs 972 394).val →
        R.1 = 3 ∧ T.1 = 391 := by
  native_decide

/--
even low resonance `(a,b)=(1,2)` は `k≥6` なら M₄ 上で単一 class に落ちる。

ここで `k` の class は通常の `k mod 972` ではなく、3-adic tail representative
`6 + ((k-6) mod 972)` に対応する。結論 `((k-6)%972)=966` はすなわち
representative が exact に 972 であることを表す。
-/
theorem SourceTwoHoleEquation.evenLowResonance_m4_classification
    {k n r L : ℕ}
    (hk6 : 6 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 1 2) :
    (k - 6) % 972 = 966 ∧
      n % 486 = 394 ∧
      r % 486 = 3 ∧
      L % 486 = 391 := by
  have hMod := hEq.to_mod ThreeTail.modulus
  have hRed := hMod.reduce_tailLoop ThreeTail.loops
  let J : ℕ := (k - 6) % 972
  let N : ℕ := n % 486
  let R : ℕ := r % 486
  let T : ℕ := L % 486
  have hJlt : J < 972 := by
    dsimp [J]
    exact Nat.mod_lt _ (by norm_num)
  have hNlt : N < 486 := by
    dsimp [N]
    exact Nat.mod_lt _ (by norm_num)
  have hRlt : R < 486 := by
    dsimp [R]
    exact Nat.mod_lt _ (by norm_num)
  have hTlt : T < 486 := by
    dsimp [T]
    exact Nat.mod_lt _ (by norm_num)
  let Jf : Fin 972 := ⟨J, hJlt⟩
  let Nf : Fin 486 := ⟨N, hNlt⟩
  let Rf : Fin 486 := ⟨R, hRlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  have hkNot : ¬ k < 6 := by omega
  have hFinite :
      SourceTwoHoleModEquation ThreeTail.modulus
        (ThreeTail.largeDepthKRep Jf) Nf.1 Rf.1 Tf.1 1 2 := by
    dsimp [Jf, Nf, Rf, Tf, J, N, R, T]
    simpa [tailLoopExponent, hkNot, ThreeTail.largeDepthKRep] using hRed
  have hEqZ :
      sourceTwoEvenResonanceLhs
          (ThreeTail.largeDepthKRep Jf) Nf.1 =
        sourceTwoThreeTailRhs Rf.1 Tf.1 := by
    simpa [sourceTwoEvenResonanceLhs, sourceTwoThreeTailRhs,
      SourceTwoHoleModEquation] using hFinite
  have hEqVal := congrArg ZMod.val hEqZ
  have hMem :
      sourceTwoThreeTailRhsSet.contains
          (sourceTwoEvenResonanceLhs
            (ThreeTail.largeDepthKRep Jf) Nf.1).val = true := by
    rw [hEqVal]
    exact sourceTwoThreeTailRhsSet_contains Rf Tf
  have hJN := sourceTwoEvenResonance_m4_source_sieve Jf Nf hMem
  have hFixed :
      (sourceTwoThreeTailRhs Rf.1 Tf.1).val =
        (sourceTwoEvenResonanceLhs 972 394).val := by
    rw [← hEqVal]
    simp [ThreeTail.largeDepthKRep, hJN.1, hJN.2]
  have hRT := sourceTwoEvenResonance_m4_target_sieve Rf Tf hFixed
  dsimp [Jf, Nf, Rf, Tf, J, N, R, T] at hJN hRT
  exact ⟨hJN.1, hJN.2, hRT.1, hRT.2⟩

/-! ## odd resonance `a=2` -/

/--
odd resonance `a=2` の M₄ finite state。

M₄ 単独ではこの predicate を満たす state が残るため、ここでは survivor 0 を主張しない。
後段ではこの finite state に 2-adic order / 追加 modulus を重ねる。
-/
def SourceTwoOddResonanceM4State
    (J : Fin 972) (N R T B : Fin 486) : Prop :=
  SourceTwoHoleModEquation ThreeTail.modulus
    (ThreeTail.largeDepthKRep J) N.1 R.1 T.1 2 B.1

/--
`k≥6, a=2` の exact equation は必ず上の有限 M₄ state を一つ与える。

各 witness は元 exponent の tail/loop representative をそのまま保持するので、
後段 sieve で元の変数との対応を再構成する必要がない。
-/
theorem SourceTwoHoleEquation.oddLowResonance_exists_m4_state
    {k n r L b : ℕ}
    (hk6 : 6 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 2 b) :
    ∃ J : Fin 972, ∃ N R T B : Fin 486,
      J.1 = (k - 6) % 972 ∧
      N.1 = n % 486 ∧
      R.1 = r % 486 ∧
      T.1 = L % 486 ∧
      B.1 = b % 486 ∧
      SourceTwoOddResonanceM4State J N R T B := by
  have hMod := hEq.to_mod ThreeTail.modulus
  have hRed := hMod.reduce_tailLoop ThreeTail.loops
  let J : ℕ := (k - 6) % 972
  let N : ℕ := n % 486
  let R : ℕ := r % 486
  let T : ℕ := L % 486
  let B : ℕ := b % 486
  have hJlt : J < 972 := by
    dsimp [J]
    exact Nat.mod_lt _ (by norm_num)
  have hNlt : N < 486 := by
    dsimp [N]
    exact Nat.mod_lt _ (by norm_num)
  have hRlt : R < 486 := by
    dsimp [R]
    exact Nat.mod_lt _ (by norm_num)
  have hTlt : T < 486 := by
    dsimp [T]
    exact Nat.mod_lt _ (by norm_num)
  have hBlt : B < 486 := by
    dsimp [B]
    exact Nat.mod_lt _ (by norm_num)
  let Jf : Fin 972 := ⟨J, hJlt⟩
  let Nf : Fin 486 := ⟨N, hNlt⟩
  let Rf : Fin 486 := ⟨R, hRlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  let Bf : Fin 486 := ⟨B, hBlt⟩
  have hkNot : ¬ k < 6 := by omega
  have hFinite :
      SourceTwoHoleModEquation ThreeTail.modulus
        (ThreeTail.largeDepthKRep Jf) Nf.1 Rf.1 Tf.1 2 Bf.1 := by
    dsimp [Jf, Nf, Rf, Tf, Bf, J, N, R, T, B]
    simpa [tailLoopExponent, hkNot, ThreeTail.largeDepthKRep] using hRed
  refine ⟨Jf, Nf, Rf, Tf, Bf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hFinite

/--
`k≥7` source-two の二つの low resonance を M₄ residual にまとめる。

even branch は単一 residue class、odd branch は明示的有限 state に落ちる。
また両 branch 共通で `r≥3` が得られる。
-/
theorem SourceTwoHoleEquation.largeDepth_lowResonance_m4_reduction
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    3 ≤ r ∧
      ((k % 2 = 0 ∧ a = 1 ∧ b = 2 ∧
          (k - 6) % 972 = 966 ∧
          n % 486 = 394 ∧
          r % 486 = 3 ∧
          L % 486 = 391) ∨
       (k % 2 = 1 ∧ a = 2 ∧
          ∃ J : Fin 972, ∃ N R T B : Fin 486,
            J.1 = (k - 6) % 972 ∧
            N.1 = n % 486 ∧
            R.1 = r % 486 ∧
            T.1 = L % 486 ∧
            B.1 = b % 486 ∧
            SourceTwoOddResonanceM4State J N R T B)) := by
  have hr3 := hEq.largeDepth_exitDepth_ge_three hk7 ha0 hab hbn hr hL
  have hRes := hEq.largeDepth_forces_lowResonance hk7 ha0 hab hbn hr hL
  refine ⟨hr3, ?_⟩
  rcases hRes with hEven | hOdd
  · rcases hEven with ⟨hkEven, rfl, rfl⟩
    have hClass := hEq.evenLowResonance_m4_classification (by omega)
    exact Or.inl ⟨hkEven, rfl, rfl, hClass.1,
      hClass.2.1, hClass.2.2.1, hClass.2.2.2⟩
  · rcases hOdd with ⟨hkOdd, rfl⟩
    rcases hEq.oddLowResonance_exists_m4_state (by omega) with
      ⟨J, N, R, T, B, hJ, hN, hR, hT, hB, hState⟩
    exact Or.inr ⟨hkOdd, rfl, J, N, R, T, B,
      hJ, hN, hR, hT, hB, hState⟩

end Mersenne
end Collatz3
