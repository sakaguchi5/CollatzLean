import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalDepthPattern
import CollatzLean.CollatzOrbitCore.Crossing
import CollatzLean.CollatzFirstLayer.SignedReplay

/-!
# Constant terminalのendpoint指数二分岐

Constant nested Special C3のendpoint位置は狭義増加し、非有界軌道では値が再訪しない。
したがってendpoint値には狭義増加部分列がある。その部分列上のendpoint exponentを
さらに分類すると、cofinal定数部分列または狭義増加部分列を得る。

* endpoint exponent一定なら、連続endpointを結ぶsuffix windowは開始時からsynchronized
* endpoint exponent増加なら、suffix windowの差depthはlower exponentとexact一致してdeferred

増加枝ではさらにgapを大きく取り、suffix開始値をresidue modulus未満へ押し込む。
するとsuffix actual runはcanonical runとなり、deferred + negative predecessor shadowから
suffixそのものがSpecial C3になる。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData
namespace ConstantTerminalNestedAlignmentData

@[simp] theorem refine_fixedStart
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (s : ℕ → ℕ)
    (hs : StrictMono s) :
    (D.refine s hs).fixedStart = D.fixedStart :=
  rfl

@[simp] theorem refine_selectedLength
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (s : ℕ → ℕ)
    (hs : StrictMono s)
    (n : ℕ) :
    (D.refine s hs).selectedLength n = D.selectedLength (s n) :=
  rfl

@[simp] theorem refine_endpointPosition
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (s : ℕ → ℕ)
    (hs : StrictMono s)
    (n : ℕ) :
    (D.refine s hs).endpointPosition n = D.endpointPosition (s n) :=
  rfl

@[simp] theorem refine_endpointValue
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (s : ℕ → ℕ)
    (hs : StrictMono s)
    (n : ℕ) :
    (D.refine s hs).endpointValue n = D.endpointValue (s n) :=
  rfl

@[simp] theorem refine_endpointExponent
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (s : ℕ → ℕ)
    (hs : StrictMono s)
    (n : ℕ) :
    (D.refine s hs).endpointExponent n = D.endpointExponent (s n) :=
  rfl

/-- endpoint位置列は狭義増加。 -/
theorem endpointPosition_strict
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) :
    StrictMono D.endpointPosition := by
  intro a b hab
  unfold endpointPosition
  exact Nat.add_lt_add_left (D.selectedLength_strict hab) D.fixedStart

/-- 非有界軌道上ではConstant nested endpoint値列も単射。 -/
theorem endpointValue_injective
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) :
    Function.Injective D.endpointValue := by
  intro a b hab
  have hpos : D.endpointPosition a = D.endpointPosition b :=
    (O.value_injective_of_unbounded R.unbounded) (by
      simpa [endpointValue] using hab)
  exact D.endpointPosition_strict.injective hpos

/-- `endpointIncreasingSubsequence`: endpoint値は狭義増加部分列を持つ。 -/
theorem endpointIncreasingSubsequence
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) :
    Nonempty (IncreasingNatSubsequenceData D.endpointValue) := by
  rcases natSequence_constant_or_increasing_subsequence D.endpointValue with
    hConst | hInc
  · rcases hConst with ⟨C⟩
    have hEq :
        D.endpointValue (C.select 0) =
          D.endpointValue (C.select 1) := by
      rw [C.value_eq 0, C.value_eq 1]
    have hIndex := D.endpointValue_injective hEq
    have hStrict := C.select_strict (by omega : 0 < 1)
    exact False.elim (by omega)
  · exact hInc

/-- endpoint値狭義増加まで選び直したConstant nested tower。 -/
structure EndpointIncreasingNestedData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O} where
  nested : ConstantTerminalNestedAlignmentData R
  endpoint_strict : StrictMono nested.endpointValue

/-- 任意のConstant nested towerをendpoint値狭義増加部分列へ精製。 -/
noncomputable def toEndpointIncreasing
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) :
    EndpointIncreasingNestedData (R := R) := by
  let E := Classical.choice D.endpointIncreasingSubsequence
  let N := D.refine E.select E.select_strict
  refine { nested := N, endpoint_strict := ?_ }
  intro a b hab
  change D.endpointValue (E.select a) < D.endpointValue (E.select b)
  exact E.value_strict hab

/-- ordered endpoint間suffixの完全2進差分。 -/
noncomputable def suffixDifference
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (hValue : StrictMono D.endpointValue)
    (n : ℕ) :
    O.WindowDifferenceData (D.endpointPosition n) (D.suffixLength n) := by
  apply O.windowDifferenceData_of_lt
  have h := hValue (Nat.lt_succ_self n)
  rw [D.suffixEnd_eq_nextEndpointPosition n]
  simpa [endpointValue] using h

/-- endpoint実行の一段式をendpoint記法へ移す。 -/
theorem endpoint_step
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    2 ^ D.endpointExponent n * O.value (D.endpointPosition n + 1) =
      3 * D.endpointValue n + 1 := by
  simpa [endpointExponent, endpointValue] using
    O.step (D.endpointPosition n)

/--
suffix difference が与える endpoint value の加法分解。
-/
private theorem suffixDifference_endpointValue_decomp
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (hValue : StrictMono D.endpointValue)
    (n : ℕ) :
    D.endpointValue (n + 1) =
      D.endpointValue n +
        2 ^ (D.suffixDifference hValue n).depth *
          (D.suffixDifference hValue n).oddPart := by
  let W := D.suffixDifference hValue n
  have hDiff0 := W.difference
  rw [D.suffixEnd_eq_nextEndpointPosition n] at hDiff0
  change
    D.endpointValue (n + 1) =
      D.endpointValue n + 2 ^ W.depth * W.oddPart
  simpa [endpointValue] using hDiff0


/--
二endpointが同じ actual exponent を使い、
endpoint value が増加しているなら、その直後の軌道値も増加する。
-/
private theorem equalEndpointExponent_successor_lt
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (hValue : StrictMono D.endpointValue)
    (n : ℕ)
    (hExponent :
      D.endpointExponent (n + 1) = D.endpointExponent n) :
    O.value (D.endpointPosition n + 1) <
      O.value (D.endpointPosition (n + 1) + 1) := by
  let e := D.endpointExponent n
  let a := O.value (D.endpointPosition n + 1)
  let b := O.value (D.endpointPosition (n + 1) + 1)
  have hA : 2 ^ e * a = 3 * D.endpointValue n + 1 := by
    simpa [e, a] using D.endpoint_step n
  have hB : 2 ^ e * b = 3 * D.endpointValue (n + 1) + 1 := by
    have h := D.endpoint_step (n + 1)
    rw [hExponent] at h
    simpa [e, b] using h
  have hv :
      D.endpointValue n < D.endpointValue (n + 1) := by
    simpa [Nat.succ_eq_add_one] using
      hValue (Nat.lt_succ_self n)
  have hscaled : 2 ^ e * a < 2 ^ e * b := by
    rw [hA, hB]
    omega
  exact
    (Nat.mul_lt_mul_left
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))).mp
      hscaled


/--
二つの奇数 a < b の差 b - a は偶数。
-/
private theorem odd_sub_even_of_lt
    {a b : ℕ}
    (ha : Odd a)
    (hb : Odd b)
    (hab : a < b) :
    Even (b - a) := by
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  have huv : u < v := by
    rw [hu, hv] at hab
    omega
  refine ⟨v - u, ?_⟩
  rw [hu, hv]
  omega


/--
同じ endpoint exponent を使う二endpointについて、
successor の差と suffix difference の間の scaled gap 等式を得る。
-/
private theorem equalEndpointExponent_scaled_gap
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (hValue : StrictMono D.endpointValue)
    (n : ℕ)
    (hExponent :
      D.endpointExponent (n + 1) = D.endpointExponent n) :
    2 ^ D.endpointExponent n *
        O.value (D.endpointPosition (n + 1) + 1) =
      2 ^ D.endpointExponent n *
          O.value (D.endpointPosition n + 1) +
        3 *
          2 ^ (D.suffixDifference hValue n).depth *
          (D.suffixDifference hValue n).oddPart := by
  let W := D.suffixDifference hValue n
  let e := D.endpointExponent n
  let a := O.value (D.endpointPosition n + 1)
  let b := O.value (D.endpointPosition (n + 1) + 1)
  have hDiff :
      D.endpointValue (n + 1) =
        D.endpointValue n + 2 ^ W.depth * W.oddPart := by
    simpa [W] using
      suffixDifference_endpointValue_decomp D hValue n
  have hA : 2 ^ e * a = 3 * D.endpointValue n + 1 := by
    simpa [e, a] using D.endpoint_step n
  have hB : 2 ^ e * b = 3 * D.endpointValue (n + 1) + 1 := by
    have h := D.endpoint_step (n + 1)
    rw [hExponent] at h
    simpa [e, b] using h
  change
    2 ^ e * b =
      2 ^ e * a + 3 * 2 ^ W.depth * W.oddPart
  calc
    2 ^ e * b =
        3 * D.endpointValue (n + 1) + 1 := hB
    _ =
        3 * (D.endpointValue n + 2 ^ W.depth * W.oddPart) + 1 := by
          rw [hDiff]
    _ =
        (3 * D.endpointValue n + 1) +
          3 * 2 ^ W.depth * W.oddPart := by
          ring
    _ =
        2 ^ e * a +
          3 * 2 ^ W.depth * W.oddPart := by
          rw [← hA]


/--
純算術補題。

2^e b = 2^e a + 3 * 2^d q

で a < b、b-a が偶数、q が奇数なら e < d。

そうでなければ 2^d を消去した後、
偶数 = 奇数 が生じる。
-/
private theorem scaled_odd_gap_forces_deeper_depth
    {e d a b q : ℕ}
    (hab : a < b)
    (hdeltaEven : Even (b - a))
    (hqOdd : Odd q)
    (hAB :
      2 ^ e * b =
        2 ^ e * a + 3 * 2 ^ d * q) :
    e < d := by
  by_contra hnot
  have hde : d ≤ e :=
    Nat.le_of_not_gt hnot
  let r := e - d
  have he : e = d + r := by
    dsimp [r]
    omega
  have hbdecomp : b = a + (b - a) := by
    omega
  have hAB' := hAB
  simp only [he, pow_add] at hAB'
  have hFactor :
      2 ^ d * (2 ^ r * b) =
        2 ^ d * (2 ^ r * a + 3 * q) := by
    calc
      2 ^ d * (2 ^ r * b) =
          (2 ^ d * 2 ^ r) * b := by
            ring
      _ =
          (2 ^ d * 2 ^ r) * a +
            3 * 2 ^ d * q := hAB'
      _ =
          2 ^ d * (2 ^ r * a + 3 * q) := by
            ring
  have hpowPos : 0 < 2 ^ d :=
    Nat.pow_pos (by omega)
  have hCancel :
      2 ^ r * b =
        2 ^ r * a + 3 * q :=
    Nat.mul_left_cancel hpowPos hFactor
  rw [hbdecomp, Nat.mul_add] at hCancel
  have hGap :
      2 ^ r * (b - a) = 3 * q :=
    Nat.add_left_cancel hCancel
  have hEven : Even (2 ^ r * (b - a)) := by
    rcases hdeltaEven with ⟨u, hu⟩
    refine ⟨2 ^ r * u, ?_⟩
    rw [hu]
    ring
  have hOdd : Odd (3 * q) :=
    (show Odd (3 : ℕ) by decide).mul hqOdd
  rw [hGap] at hEven
  exact odd_even_false_nat hOdd hEven


/--
二endpointが同じ actual exponent を使い値が増加しているなら、
endpoint差depthはその指数より真に深い。
-/
private noncomputable def equalEndpointExponent_forces_synchronized
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (hValue : StrictMono D.endpointValue)
    (n : ℕ)
    (hExponent :
      D.endpointExponent (n + 1) = D.endpointExponent n) :
    O.SynchronizedWindowAt
      (D.endpointPosition n) (D.suffixLength n) := by
  let W := D.suffixDifference hValue n
  let e := D.endpointExponent n
  let a := O.value (D.endpointPosition n + 1)
  let b := O.value (D.endpointPosition (n + 1) + 1)
  have hab :=
    equalEndpointExponent_successor_lt
      D hValue n hExponent
  change a < b at hab
  have hdeltaEven : Even (b - a) := by
    exact
      odd_sub_even_of_lt
        (O.value_odd (D.endpointPosition n + 1))
        (O.value_odd (D.endpointPosition (n + 1) + 1))
        hab
  have hAB :=
    equalEndpointExponent_scaled_gap
      D hValue n hExponent
  change
    2 ^ e * b =
      2 ^ e * a + 3 * 2 ^ W.depth * W.oddPart
    at hAB
  refine
    { toWindowDifferenceData := W
      synchronized := ?_ }
  change e < W.depth
  exact
    scaled_odd_gap_forces_deeper_depth
      hab
      hdeltaEven
      W.oddPart_odd
      hAB

/-- endpoint exponent一定部分列の各隣接suffixはsynchronized。 -/
noncomputable def suffixSynchronized_of_endpointExponent_constant
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (hValue : StrictMono D.endpointValue)
    {e : ℕ}
    (hExponent : ∀ n : ℕ, D.endpointExponent n = e)
    (n : ℕ) :
    O.SynchronizedWindowAt
      (D.endpointPosition n) (D.suffixLength n) := by
  apply equalEndpointExponent_forces_synchronized D hValue n
  rw [hExponent (n + 1), hExponent n]

/--
endpoint exponentが真に増えるordered pairでは、endpoint差depthはlower exponentとexact一致。
-/
private noncomputable def increasingEndpointExponent_forces_deferred
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (hValue : StrictMono D.endpointValue)
    (n : ℕ)
    (hExponent : D.endpointExponent n < D.endpointExponent (n + 1)) :
    O.DeferredWindowAt
      (D.endpointPosition n) (D.suffixLength n) := by
  let W := D.suffixDifference hValue n
  let e := D.endpointExponent n
  let f := D.endpointExponent (n + 1)
  let a := O.value (D.endpointPosition n + 1)
  let b := O.value (D.endpointPosition (n + 1) + 1)
  have hDiff0 := W.difference
  rw [D.suffixEnd_eq_nextEndpointPosition n] at hDiff0
  have hDiff :
      D.endpointValue (n + 1) =
        D.endpointValue n + 2 ^ W.depth * W.oddPart := by
    simpa [endpointValue] using hDiff0
  have hA : 2 ^ e * a = 3 * D.endpointValue n + 1 := by
    simpa [e, a] using D.endpoint_step n
  have hB : 2 ^ f * b = 3 * D.endpointValue (n + 1) + 1 := by
    simpa [f, b] using D.endpoint_step (n + 1)
  have hAB :
      2 ^ f * b =
        2 ^ e * a + 3 * 2 ^ W.depth * W.oddPart := by
    calc
      2 ^ f * b = 3 * D.endpointValue (n + 1) + 1 := hB
      _ = 3 * (D.endpointValue n + 2 ^ W.depth * W.oddPart) + 1 := by
        rw [hDiff]
      _ = (3 * D.endpointValue n + 1) +
          3 * 2 ^ W.depth * W.oddPart := by ring
      _ = 2 ^ e * a + 3 * 2 ^ W.depth * W.oddPart := by rw [← hA]
  have hef : e < f := by simpa [e, f] using hExponent
  have hDepth : W.depth = e := by
    rcases lt_trichotomy W.depth e with hde | hde | hed
    · let r := e - W.depth
      let s := f - W.depth
      have hr : 0 < r := by dsimp [r]; omega
      have hs : 0 < s := by dsimp [s]; omega
      have heq : e = W.depth + r := by dsimp [r]; omega
      have hfq : f = W.depth + s := by dsimp [s]; omega
      have hAB' := hAB
      simp only [hfq, heq, pow_add] at hAB'
      have hFactor :
          2 ^ W.depth * (2 ^ s * b) =
            2 ^ W.depth * (2 ^ r * a + 3 * W.oddPart) := by
        calc
          2 ^ W.depth * (2 ^ s * b)
              = (2 ^ W.depth * 2 ^ s) * b := by ring
          _ = (2 ^ W.depth * 2 ^ r) * a +
                3 * 2 ^ W.depth * W.oddPart := hAB'
          _ = 2 ^ W.depth * (2 ^ r * a + 3 * W.oddPart) := by ring
      have hpowPos : 0 < 2 ^ W.depth := Nat.pow_pos (by omega)
      have hCancel :
          2 ^ s * b = 2 ^ r * a + 3 * W.oddPart :=
        Nat.mul_left_cancel hpowPos hFactor
      obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, s = s0 + 1 :=
        ⟨s - 1, by omega⟩
      obtain ⟨r0, hr0⟩ : ∃ r0 : ℕ, r = r0 + 1 :=
        ⟨r - 1, by omega⟩
      rcases W.oddPart_odd with ⟨u, hu⟩
      have hEven : Even (2 ^ s * b) := by
        refine ⟨2 ^ s0 * b, ?_⟩
        rw [hs0, pow_succ]
        ring
      have hOdd : Odd (2 ^ r * a + 3 * W.oddPart) := by
        refine ⟨2 ^ r0 * a + 3 * u + 1, ?_⟩
        rw [hr0, hu, pow_succ]
        ring
      rw [hCancel] at hEven
      exact False.elim (odd_even_false_nat hOdd hEven)
    · exact hde
    · let r := f - e
      let s := W.depth - e
      have hr : 0 < r := by dsimp [r]; omega
      have hs : 0 < s := by dsimp [s]; omega
      have hfq : f = e + r := by dsimp [r]; omega
      have hdq : W.depth = e + s := by dsimp [s]; omega
      have hAB' := hAB
      simp only [hfq, hdq, pow_add] at hAB'
      have hFactor :
          2 ^ e * (2 ^ r * b) =
            2 ^ e * (a + 3 * 2 ^ s * W.oddPart) := by
        calc
          2 ^ e * (2 ^ r * b)
              = (2 ^ e * 2 ^ r) * b := by ring
          _ = 2 ^ e * a + 3 * (2 ^ e * 2 ^ s) * W.oddPart := hAB'
          _ = 2 ^ e * (a + 3 * 2 ^ s * W.oddPart) := by ring
      have hpowPos : 0 < 2 ^ e := Nat.pow_pos (by omega)
      have hCancel :
          2 ^ r * b = a + 3 * 2 ^ s * W.oddPart :=
        Nat.mul_left_cancel hpowPos hFactor
      obtain ⟨r0, hr0⟩ : ∃ r0 : ℕ, r = r0 + 1 :=
        ⟨r - 1, by omega⟩
      obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, s = s0 + 1 :=
        ⟨s - 1, by omega⟩
      rcases O.value_odd (D.endpointPosition n + 1) with ⟨u, hu⟩
      have hua : a = 2 * u + 1 := by
        simpa [a] using hu
      have hEven : Even (2 ^ r * b) := by
        refine ⟨2 ^ r0 * b, ?_⟩
        rw [hr0, pow_succ]
        ring
      have hOdd : Odd (a + 3 * 2 ^ s * W.oddPart) := by
        refine ⟨u + 3 * 2 ^ s0 * W.oddPart, ?_⟩
        rw [hua, hs0, pow_succ]
        ring
      rw [hCancel] at hEven
      exact False.elim (odd_even_false_nat hOdd hEven)
  exact
    { toWindowDifferenceData := W
      deferred := hDepth }

/-- fixed exponent synchronized tail tower。 -/
structure FixedExponentSynchronizedTailTowerData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O} where
  nested : ConstantTerminalNestedAlignmentData R
  endpoint_strict : StrictMono nested.endpointValue
  exponent : ℕ
  endpointExponent_eq : ∀ n : ℕ, nested.endpointExponent n = exponent
  suffixSynchronized : ∀ n : ℕ,
    O.SynchronizedWindowAt
      (nested.endpointPosition n) (nested.suffixLength n)

/-- endpoint exponent狭義増加のnested tower。 -/
structure EndpointExponentIncreasingNestedData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O} where
  nested : ConstantTerminalNestedAlignmentData R
  endpoint_strict : StrictMono nested.endpointValue
  exponent_strict : StrictMono nested.endpointExponent

/-- `n < 2^(n+1)`。canonical gap選択に使う。 -/
private theorem nat_lt_twoPow_succ_local (n : ℕ) :
    n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
      omega

/-- StrictMono自然数列は添字差以上に値が増える。 -/
private theorem strictMono_add_le
    (f : ℕ → ℕ)
    (hf : StrictMono f)
    (a d : ℕ) :
    f a + d ≤ f (a + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hs : f (a + d) < f (a + d + 1) :=
        hf (by omega)
      have hindex : a + (d + 1) = a + d + 1 := by omega
      rw [hindex]
      omega

namespace EndpointExponentIncreasingNestedData

/-- 現endpoint値より十分大きいindex gapを再帰的に取る。 -/
noncomputable def largeGapSelect
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R)) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      E.largeGapSelect n +
        E.nested.endpointValue (E.largeGapSelect n) + 1

/-- large-gap選択は狭義増加。 -/
theorem largeGapSelect_strict
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R)) :
    StrictMono E.largeGapSelect := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [largeGapSelect]
  omega

/-- large-gapで再選択したnested tower。 -/
noncomputable def largeGapNested
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R)) :
    ConstantTerminalNestedAlignmentData R :=
  E.nested.refine E.largeGapSelect E.largeGapSelect_strict

/-- large-gap後もendpoint値は狭義増加。 -/
theorem largeGap_endpoint_strict
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R)) :
    StrictMono E.largeGapNested.endpointValue := by
  intro a b hab
  change
    E.nested.endpointValue (E.largeGapSelect a) <
      E.nested.endpointValue (E.largeGapSelect b)
  exact E.endpoint_strict (E.largeGapSelect_strict hab)

/-- large-gap後もendpoint exponentは狭義増加。 -/
theorem largeGap_exponent_strict
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R)) :
    StrictMono E.largeGapNested.endpointExponent := by
  intro a b hab
  change
    E.nested.endpointExponent (E.largeGapSelect a) <
      E.nested.endpointExponent (E.largeGapSelect b)
  exact E.exponent_strict (E.largeGapSelect_strict hab)

/-- large-gap suffix長はその開始endpoint値より大きい。 -/
theorem endpointValue_lt_suffixLength
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R))
    (n : ℕ) :
    E.largeGapNested.endpointValue n <
      E.largeGapNested.suffixLength n := by
  let a := E.largeGapSelect n
  let d := E.nested.endpointValue a + 1
  have hSelect : E.largeGapSelect (n + 1) = a + d := by
    simp [largeGapSelect, a, d, Nat.add_assoc]
  have hGrow :=
    strictMono_add_le
      E.nested.selectedLength E.nested.selectedLength_strict a d
  have hLength :
      E.nested.selectedLength a + d ≤
        E.nested.selectedLength (E.largeGapSelect (n + 1)) := by
    rw [hSelect]
    exact hGrow
  change
    E.nested.endpointValue a <
      E.nested.selectedLength (E.largeGapSelect (n + 1)) -
        E.nested.selectedLength a
  dsimp [d] at hLength
  omega

/-- large-gap suffix開始値はsuffix residue modulus未満。 -/
theorem endpointValue_lt_suffixResidueModulus
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R))
    (n : ℕ) :
    E.largeGapNested.endpointValue n <
      residueModulus (E.largeGapNested.suffixWord n) := by
  let D := E.largeGapNested
  have hLen :
      D.endpointValue n < D.suffixLength n := by
    simpa [D] using E.endpointValue_lt_suffixLength n
  have hExpLe :
      D.endpointValue n + 1 ≤ D.suffixLength n + 1 :=
    Nat.succ_le_succ (Nat.le_of_lt hLen)
  have hValid := D.suffixWord_valid n
  have hSteps :
      D.suffixLength n ≤ twoSteps (D.suffixWord n) := by
    have h := oddSteps_le_twoSteps hValid
    simpa [suffixWord, oddSteps] using h
  have hStepsSucc :
      D.suffixLength n + 1 ≤
        twoSteps (D.suffixWord n) + 1 :=
    Nat.succ_le_succ hSteps
  have hPow0 :=
    nat_lt_twoPow_succ_local (D.endpointValue n)
  have hPow1 :
      2 ^ (D.endpointValue n + 1) ≤
        2 ^ (D.suffixLength n + 1) :=
    Nat.pow_le_pow_right (by decide) hExpLe
  have hPow2 :
      2 ^ (D.suffixLength n + 1) ≤
        2 ^ (twoSteps (D.suffixWord n) + 1) :=
    Nat.pow_le_pow_right (by decide) hStepsSucc
  unfold residueModulus
  exact lt_of_lt_of_le hPow0 (le_trans hPow1 hPow2)

/-- large-gap suffix actual runはcanonical startから始まる。 -/
theorem suffix_canonicalStart
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R))
    (n : ℕ) :
    E.largeGapNested.endpointValue n =
      canonicalStart (E.largeGapNested.suffixWord n) := by
  let D := E.largeGapNested
  let C :=
    canonicalReplayCoordinate_of_runs
      (D.suffix_run n)
      (D.suffixWord_ne_nil n)
  have hlt :
      D.endpointValue n <
        residueModulus (D.suffixWord n) := by
    simpa [D] using
      E.endpointValue_lt_suffixResidueModulus n
  have hq : C.quotient = 0 := by
    by_contra hne
    have hqone : 1 ≤ C.quotient :=
      Nat.one_le_iff_ne_zero.mpr hne
    have hprodLe :
        residueModulus (D.suffixWord n) ≤
          residueModulus (D.suffixWord n) * C.quotient := by
      simpa using
        Nat.mul_le_mul_left
          (residueModulus (D.suffixWord n))
          hqone
    have hstart := C.start_eq
    have hlarge :
        residueModulus (D.suffixWord n) ≤
          D.endpointValue n := by
      calc
        residueModulus (D.suffixWord n)
            ≤ residueModulus (D.suffixWord n) * C.quotient :=
          hprodLe
        _ ≤ canonicalStart (D.suffixWord n) +
              residueModulus (D.suffixWord n) * C.quotient :=
          Nat.le_add_left _ _
        _ = D.endpointValue n :=
          hstart.symm
    exact (Nat.not_le_of_gt hlt) hlarge
  exact
    C.start_eq_canonical_of_quotient_eq_zero hq
/-- large-gap suffix actual runはcanonical endへ到達する。 -/
theorem suffix_canonicalEnd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R))
    (n : ℕ) :
    E.largeGapNested.endpointValue (n + 1) =
      canonicalEnd (E.largeGapNested.suffixWord n) := by
  let D := E.largeGapNested
  let C :=
    canonicalReplayCoordinate_of_runs
      (D.suffix_run n)
      (D.suffixWord_ne_nil n)
  have hstart := E.suffix_canonicalStart n
  have hq : C.quotient = 0 :=
    C.quotient_eq_zero_of_start_eq_canonical hstart
  have hfinish := C.finish_eq
  rw [hq] at hfinish
  simpa using hfinish

/-- large-gap suffixはactual exponent増加により開始直後deferred。 -/
noncomputable def suffix_deferred
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R))
    (n : ℕ) :
    O.DeferredWindowAt
      (E.largeGapNested.endpointPosition n)
      (E.largeGapNested.suffixLength n) := by
  exact
    increasingEndpointExponent_forces_deferred
      E.largeGapNested
      E.largeGap_endpoint_strict
      n
      (E.largeGap_exponent_strict (Nat.lt_succ_self n))

/-- large-gap suffixのpredecessor shadowは負。 -/
theorem suffix_predecessorShadow_neg
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R))
    (n : ℕ) :
    predecessorShadow (E.largeGapNested.suffixWord n) < 0 := by
  let D := E.largeGapNested
  have hRun := D.suffix_run n
  have hStart := E.suffix_canonicalStart n
  have hEnd := E.suffix_canonicalEnd n
  have hCanonical :
      Runs
        (D.suffixWord n)
        (canonicalStart (D.suffixWord n))
        (canonicalEnd (D.suffixWord n)) := by
    rw [← hStart, ← hEnd]
    exact hRun
  exact Runs.predecessorShadow_neg_of_canonical_run hCanonical

/-- large-gap後の各隣接suffixそのものがSpecial C3。 -/
noncomputable def suffix_specialC3
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (E : EndpointExponentIncreasingNestedData (R := R))
    (n : ℕ) :
    SpecialC3At O
      (E.largeGapNested.endpointPosition n)
      (E.largeGapNested.suffixLength n) := by
  let D := E.largeGapNested
  have hStart :
      O.value (D.endpointPosition n) = canonicalStart (D.suffixWord n) := by
    simpa [endpointValue] using E.suffix_canonicalStart n
  have hEnd :
      O.value (D.endpointPosition n + D.suffixLength n) =
        canonicalEnd (D.suffixWord n) := by
    rw [D.suffixEnd_eq_nextEndpointPosition n]
    simpa [endpointValue] using E.suffix_canonicalEnd n
  exact
    specialC3At_of_deferred
      (E.suffix_deferred n)
      (D.suffixLength_pos n)
      hStart
      hEnd
      (E.suffix_predecessorShadow_neg n)

end EndpointExponentIncreasingNestedData

/-- endpoint exponent増加から得る隣接Special C3 chain。 -/
structure IncreasingExponentAdjacentSpecialC3ChainData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O} where
  nested : ConstantTerminalNestedAlignmentData R
  endpoint_strict : StrictMono nested.endpointValue
  exponent_strict : StrictMono nested.endpointExponent
  suffixSpecial : ∀ n : ℕ,
    SpecialC3At O (nested.endpointPosition n) (nested.suffixLength n)

/-- endpoint指数列を最終二対象へ分解。 -/
theorem endpointExponent_constant_or_increasing
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R) :
    Nonempty (FixedExponentSynchronizedTailTowerData (R := R)) ∨
      Nonempty (IncreasingExponentAdjacentSpecialC3ChainData (R := R)) := by
  classical
  let E := D.toEndpointIncreasing
  rcases
      natSequence_constant_or_increasing_subsequence
        E.nested.endpointExponent with
    hConst | hInc
  · rcases hConst with ⟨C⟩
    let N := E.nested.refine C.select C.select_strict
    have hValue : StrictMono N.endpointValue := by
      intro a b hab
      change
        E.nested.endpointValue (C.select a) <
          E.nested.endpointValue (C.select b)
      exact E.endpoint_strict (C.select_strict hab)
    have hExponent : ∀ n : ℕ, N.endpointExponent n = C.value := by
      intro n
      change E.nested.endpointExponent (C.select n) = C.value
      exact C.value_eq n
    left
    exact ⟨{
      nested := N
      endpoint_strict := hValue
      exponent := C.value
      endpointExponent_eq := hExponent
      suffixSynchronized := fun n =>
        N.suffixSynchronized_of_endpointExponent_constant
          hValue hExponent n
    }⟩
  · rcases hInc with ⟨I⟩
    let N := E.nested.refine I.select I.select_strict
    have hValue : StrictMono N.endpointValue := by
      intro a b hab
      change
        E.nested.endpointValue (I.select a) <
          E.nested.endpointValue (I.select b)
      exact E.endpoint_strict (I.select_strict hab)
    have hExponent : StrictMono N.endpointExponent := by
      intro a b hab
      change
        E.nested.endpointExponent (I.select a) <
          E.nested.endpointExponent (I.select b)
      exact I.value_strict hab
    let G : EndpointExponentIncreasingNestedData (R := R) :=
      { nested := N
        endpoint_strict := hValue
        exponent_strict := hExponent }
    right
    exact ⟨{
      nested := G.largeGapNested
      endpoint_strict := G.largeGap_endpoint_strict
      exponent_strict := G.largeGap_exponent_strict
      suffixSpecial := G.suffix_specialC3
    }⟩

/-- Constant terminal部分列そのものを最終二対象へ送る。 -/
theorem constantTerminal_reduction
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : ConstantNatSubsequenceData R.terminalTime) :
    Nonempty (FixedExponentSynchronizedTailTowerData (R := R)) ∨
      Nonempty (IncreasingExponentAdjacentSpecialC3ChainData (R := R)) := by
  let D := ConstantTerminalNestedAlignmentData.ofConstant R S
  exact D.endpointExponent_constant_or_increasing

end ConstantTerminalNestedAlignmentData
end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
