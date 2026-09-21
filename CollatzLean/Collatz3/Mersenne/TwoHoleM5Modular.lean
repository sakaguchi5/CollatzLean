import CollatzLean.Collatz3.Mersenne.SourceTwoHoleResonanceThreeTail
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: two-hole M₅ tail/loop reduction

source/split の low resonance を一段細かく読むため、

`M₅ = M₄ * 2593 = 1456871044718313`

を共通 modulus とする。

`2593` を加えても 2-exponent の loop は 486 のまま保たれ、
3-exponent の large-depth loop だけが 972 から 1944 へ細分化される。
このファイルでは residue の最終判定は行わず、exact equation を finite state へ送る
共通 infrastructure だけを内部 theorem として固定する。
-/

namespace Collatz3
namespace Mersenne
namespace TwoHoleM5

/-- `M₄ * 2593`。 -/
def modulus : ℕ := 1456871044718313

/-- corrected decimal value of `M₄ * 2593`。 -/
theorem modulus_eq_threeTail_mul_2593 :
    modulus = ThreeTail.modulus * 2593 := by
  norm_num [modulus, ThreeTail.modulus]

/-- M₅ 上でも 2 は tail 0、period 486。 -/
theorem twoLoop :
    PowTailLoop modulus 2 0 486 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- M₅ 上で 3 は tail 6、その後 period 1944。 -/
theorem threeLoop :
    PowTailLoop modulus 3 6 1944 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- 2/3 を同時に使う M₅ certificate。 -/
theorem loops :
    Pow23TailLoops modulus 0 486 6 1944 :=
  ⟨twoLoop, threeLoop⟩

/-- `k≥6` の M₅ 3-tail representative。 -/
def largeDepthKRep (j : Fin 1944) : ℕ :=
  6 + j.1

/-- source odd `a=2` の finite M₅ state。 -/
def SourceOddState
    (J : Fin 1944) (N R T B : Fin 486) : Prop :=
  SourceTwoHoleModEquation modulus
    (largeDepthKRep J) N.1 R.1 T.1 2 B.1

/-- split odd `a=2` の finite M₅ state。 -/
def SplitOddA2State
    (J : Fin 1944) (N R T B : Fin 486) : Prop :=
  SplitTwoHoleModEquation modulus
    (largeDepthKRep J) N.1 R.1 T.1 2 B.1

end TwoHoleM5

/--
`k≥6, a=2` の source-two exact equation は必ず一つの M₅ finite state を与える。
-/
theorem SourceTwoHoleEquation.oddLowResonance_exists_m5_state
    {k n r L b : ℕ}
    (hk6 : 6 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 2 b) :
    ∃ J : Fin 1944, ∃ N R T B : Fin 486,
      J.1 = (k - 6) % 1944 ∧
      N.1 = n % 486 ∧
      R.1 = r % 486 ∧
      T.1 = L % 486 ∧
      B.1 = b % 486 ∧
      TwoHoleM5.SourceOddState J N R T B := by
  have hMod := hEq.to_mod TwoHoleM5.modulus
  have hRed := hMod.reduce_tailLoop TwoHoleM5.loops
  let J : ℕ := (k - 6) % 1944
  let N : ℕ := n % 486
  let R : ℕ := r % 486
  let T : ℕ := L % 486
  let B : ℕ := b % 486
  have hJlt : J < 1944 := by
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
  let Jf : Fin 1944 := ⟨J, hJlt⟩
  let Nf : Fin 486 := ⟨N, hNlt⟩
  let Rf : Fin 486 := ⟨R, hRlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  let Bf : Fin 486 := ⟨B, hBlt⟩
  have hkNot : ¬ k < 6 := by omega
  have hFinite :
      SourceTwoHoleModEquation TwoHoleM5.modulus
        (TwoHoleM5.largeDepthKRep Jf) Nf.1 Rf.1 Tf.1 2 Bf.1 := by
    dsimp [Jf, Nf, Rf, Tf, Bf, J, N, R, T, B]
    simpa [tailLoopExponent, hkNot, TwoHoleM5.largeDepthKRep] using hRed
  refine ⟨Jf, Nf, Rf, Tf, Bf, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try rfl
  exact hFinite

/--
`k≥6, a=2` の split-two exact equation も一つの M₅ finite state を与える。
-/
theorem SplitTwoHoleEquation.oddA2_exists_m5_state
    {k n r L b : ℕ}
    (hk6 : 6 ≤ k)
    (hEq : SplitTwoHoleEquation k n r L 2 b) :
    ∃ J : Fin 1944, ∃ N R T B : Fin 486,
      J.1 = (k - 6) % 1944 ∧
      N.1 = n % 486 ∧
      R.1 = r % 486 ∧
      T.1 = L % 486 ∧
      B.1 = b % 486 ∧
      TwoHoleM5.SplitOddA2State J N R T B := by
  have hMod := hEq.to_mod TwoHoleM5.modulus
  have hRed := hMod.reduce_tailLoop TwoHoleM5.loops
  let J : ℕ := (k - 6) % 1944
  let N : ℕ := n % 486
  let R : ℕ := r % 486
  let T : ℕ := L % 486
  let B : ℕ := b % 486
  have hJlt : J < 1944 := by
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
  let Jf : Fin 1944 := ⟨J, hJlt⟩
  let Nf : Fin 486 := ⟨N, hNlt⟩
  let Rf : Fin 486 := ⟨R, hRlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  let Bf : Fin 486 := ⟨B, hBlt⟩
  have hkNot : ¬ k < 6 := by omega
  have hFinite :
      SplitTwoHoleModEquation TwoHoleM5.modulus
        (TwoHoleM5.largeDepthKRep Jf) Nf.1 Rf.1 Tf.1 2 Bf.1 := by
    dsimp [Jf, Nf, Rf, Tf, Bf, J, N, R, T, B]
    simpa [tailLoopExponent, hkNot, TwoHoleM5.largeDepthKRep] using hRed
  refine ⟨Jf, Nf, Rf, Tf, Bf, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try rfl
  exact hFinite

end Mersenne
end Collatz3
