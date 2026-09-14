import CollatzLean.Collatz3.Semantics.OrbitFateFutureMinimum
import CollatzLean.Collatz3.Bridge.InfiniteSurvivorOrbitBridge
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: normalized escape coordinate

actual odd-only orbit の `m` odd steps 後について

`D_m = infinitePrefixDepth exponent m`

とし、normalized escape coordinate

`R_m = 2^D_m * value(m) / 3^m`

を導入する。

これは新しい orbit packet ではなく、既存 actual orbit から読む一つの実数座標だけである。
一歩の actual equation

`2^e * x_(m+1) = 3 x_m + 1`

から exact に

`R_(m+1) = R_m + 2^D_m / 3^(m+1)`

を得る。従って `R_m` は strict に増加し、有限 telescope は

`R_m = x_0 + Σ_{k<m} 2^D_k / 3^(k+1)`

となる。

infinite coefficient survivor では

`D_m + δ_m = beattyIndex m`

かつ `2^(beattyIndex m) ≤ 3^m` なので、increment は

`2^D_m / 3^(m+1) ≤ 1 / (3 * 2^δ_m)`

で抑えられる。

最後に、同じ finite prefix の affine numerator

`3^m * x_0 + affineConst(word)`

が `2^D_m` で割り切れることも並べておく。後続ではこの同じ有限量を
実数極限側と 2進 residue 側から読む。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
actual orbit の normalized escape coordinate。

`R_m = 2^D_m * x_m / 3^m`。
-/
noncomputable def normalizedEscapeCoordinate
    (O : Collatz3.OddOrbit)
    (m : ℕ) : ℝ :=
  ((2 : ℝ) ^ infinitePrefixDepth O.exponent m * (O.value m : ℝ)) /
    (3 : ℝ) ^ m

/--
normalized escape coordinate の一歩増分。

`a_m = 2^D_m / 3^(m+1)`。
-/
noncomputable def normalizedEscapeIncrement
    (O : Collatz3.OddOrbit)
    (m : ℕ) : ℝ :=
  (2 : ℝ) ^ infinitePrefixDepth O.exponent m /
    (3 : ℝ) ^ (m + 1)

@[simp] theorem normalizedEscapeCoordinate_zero
    (O : Collatz3.OddOrbit) :
    O.normalizedEscapeCoordinate 0 = (O.value 0 : ℝ) := by
  simp [normalizedEscapeCoordinate]

/-- normalized escape coordinate は常に正。 -/
theorem normalizedEscapeCoordinate_pos
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    0 < O.normalizedEscapeCoordinate m := by
  have hxNat : 0 < O.value m := by
    have hOne := O.one_le_value m
    omega
  have hx : (0 : ℝ) < (O.value m : ℝ) := by
    exact_mod_cast hxNat
  unfold normalizedEscapeCoordinate
  positivity

/-- normalized escape increment は常に正。 -/
theorem normalizedEscapeIncrement_pos
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    0 < O.normalizedEscapeIncrement m := by
  unfold normalizedEscapeIncrement
  positivity

/--
一歩の normalized escape exact recurrence。

actual `+1` translation が positive increment
`2^D_m / 3^(m+1)` としてそのまま残る。
-/
theorem normalizedEscapeCoordinate_succ
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.normalizedEscapeCoordinate (m + 1) =
      O.normalizedEscapeCoordinate m + O.normalizedEscapeIncrement m := by
  have hStepNat := (O.step m).equation
  have hStep :
      (2 : ℝ) ^ O.exponent m * (O.value (m + 1) : ℝ) =
        3 * (O.value m : ℝ) + 1 := by
    exact_mod_cast hStepNat
  let D : ℕ := infinitePrefixDepth O.exponent m
  calc
    O.normalizedEscapeCoordinate (m + 1)
        = ((2 : ℝ) ^ D *
              ((2 : ℝ) ^ O.exponent m * (O.value (m + 1) : ℝ))) /
            ((3 : ℝ) ^ m * 3) := by
          unfold normalizedEscapeCoordinate
          rw [infinitePrefixDepth_succ, pow_add, pow_succ]
          dsimp [D]
          ring
    _ = ((2 : ℝ) ^ D * (3 * (O.value m : ℝ) + 1)) /
          ((3 : ℝ) ^ m * 3) := by rw [hStep]
    _ = O.normalizedEscapeCoordinate m + O.normalizedEscapeIncrement m := by
          unfold normalizedEscapeCoordinate normalizedEscapeIncrement
          dsimp [D]
          rw [pow_succ]
          field_simp

/--
任意の開始位置から `r` steps 分 telescope した exact finite sum。
-/
theorem normalizedEscapeCoordinate_add_eq_add_sum_range
    (O : Collatz3.OddOrbit)
    (a r : ℕ) :
    O.normalizedEscapeCoordinate (a + r) =
      O.normalizedEscapeCoordinate a +
        ∑ k ∈ Finset.range r, O.normalizedEscapeIncrement (a + k) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [show a + (r + 1) = (a + r) + 1 by omega]
      rw [O.normalizedEscapeCoordinate_succ (a + r)]
      rw [ih]
      rw [Finset.sum_range_succ]
      ring

/--
初期値からの finite telescope。

`R_m = x_0 + Σ_{k<m} a_k`。
-/
theorem normalizedEscapeCoordinate_eq_start_add_sum
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.normalizedEscapeCoordinate m =
      (O.value 0 : ℝ) +
        ∑ k ∈ Finset.range m, O.normalizedEscapeIncrement k := by
  simpa using O.normalizedEscapeCoordinate_add_eq_add_sum_range 0 m

/-- normalized escape coordinate は単調増加。 -/
theorem normalizedEscapeCoordinate_monotone
    (O : Collatz3.OddOrbit) :
    Monotone O.normalizedEscapeCoordinate := by
  apply monotone_nat_of_le_succ
  intro m
  rw [O.normalizedEscapeCoordinate_succ m]
  exact le_add_of_nonneg_right (O.normalizedEscapeIncrement_pos m).le

/-- normalized escape coordinate は実際には各一歩で strict に増える。 -/
theorem normalizedEscapeCoordinate_strictMono
    (O : Collatz3.OddOrbit) :
    StrictMono O.normalizedEscapeCoordinate := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [O.normalizedEscapeCoordinate_succ m]
  exact lt_add_of_pos_right _ (O.normalizedEscapeIncrement_pos m)

/--
infinite coefficient survivor では一歩 increment は current defect だけで上から抑えられる。

`a_m ≤ 1 / (3 * 2^δ_m)`。
-/
theorem normalizedEscapeIncrement_le_defectCap
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.normalizedEscapeIncrement m ≤
      1 / (3 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m) := by
  let D : ℕ := infinitePrefixDepth O.exponent m
  let d : ℕ := infiniteSurvivorDefect O.exponent m
  have hBeatty := beattyIndex_eq_prefixDepth_add_defect S m
  have hPowNat : 2 ^ (D + d) ≤ 3 ^ m := by
    dsimp [D, d]
    rw [← hBeatty]
    exact Critical.beattyIndex_lower m
  have hPow :
      (2 : ℝ) ^ (D + d) ≤ (3 : ℝ) ^ m := by
    exact_mod_cast hPowNat
  unfold normalizedEscapeIncrement
  --dsimp [D, d]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ (m + 1))
      (by positivity : (0 : ℝ) < 3 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)).2
  calc
    (2 : ℝ) ^ infinitePrefixDepth O.exponent m *
          (3 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)
        = 3 * (2 : ℝ) ^
            (infinitePrefixDepth O.exponent m +
              infiniteSurvivorDefect O.exponent m) := by
          rw [pow_add]
          ring
    _ ≤ 3 * (3 : ℝ) ^ m := by
          dsimp [D, d] at hPow
          nlinarith
    _ = (3 : ℝ) ^ (m + 1) := by
          rw [pow_succ]
          ring_nf
  simp

/--
defect が `d` 以上なら increment はより粗い geometric cap `1/(3*2^d)` 以下。
-/
theorem normalizedEscapeIncrement_le_of_le_defect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {m d : ℕ}
    (hd : d ≤ infiniteSurvivorDefect O.exponent m) :
    O.normalizedEscapeIncrement m ≤
      1 / (3 * (2 : ℝ) ^ d) := by
  have hBase := O.normalizedEscapeIncrement_le_defectCap S m
  have hPow :
      (2 : ℝ) ^ d ≤
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd
  have hDen :
      3 * (2 : ℝ) ^ d ≤
        3 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := by
    nlinarith
  have hPos : (0 : ℝ) < 3 * (2 : ℝ) ^ d := by positivity
  have hInv := one_div_le_one_div_of_le hPos hDen
  exact le_trans hBase hInv

/--
finite prefix の endpoint equation を normalized coordinate の affine-translation 表示へ直す。

`R_m = x_0 + affineConst(segmentWord 0 m) / 3^m`。
-/
theorem normalizedEscapeCoordinate_eq_start_add_affineConst_div
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.normalizedEscapeCoordinate m =
      (O.value 0 : ℝ) +
        (Word.affineConst (O.segmentWord 0 m) : ℝ) / (3 : ℝ) ^ m := by
  have hRun := O.runsSegment 0 m
  have hEndpoint :
      (O.segmentWord 0 m).EndpointEquation
        (O.value 0) (O.value m) := by
    simpa using hRun.endpointEquation
  have hEqNat :=
    (Word.endpointEquation_iff
      (O.segmentWord 0 m) (O.value 0) (O.value m)).1 hEndpoint
  have hDepth := O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth m
  have hOdd := O.segmentWord_oddSteps 0 m
  rw [hDepth, hOdd] at hEqNat
  have hEq :
      (2 : ℝ) ^ infinitePrefixDepth O.exponent m * (O.value m : ℝ) =
        (3 : ℝ) ^ m * (O.value 0 : ℝ) +
          (Word.affineConst (O.segmentWord 0 m) : ℝ) := by
    exact_mod_cast hEqNat
  unfold normalizedEscapeCoordinate
  rw [hEq]
  field_simp

/--
同じ finite affine numerator は physical modulus `2^D_m` で exact に割り切れる。

これは後続で real normalized limit と 2進 residue を接続する有限算術側の入口。
-/
theorem twoPow_prefixDepth_dvd_affineNumerator
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    2 ^ infinitePrefixDepth O.exponent m ∣
      3 ^ m * O.value 0 + Word.affineConst (O.segmentWord 0 m) := by
  refine ⟨O.value m, ?_⟩
  have hRun := O.runsSegment 0 m
  have hEndpoint :
      (O.segmentWord 0 m).EndpointEquation
        (O.value 0) (O.value m) := by
    simpa using hRun.endpointEquation
  have hEq :=
    (Word.endpointEquation_iff
      (O.segmentWord 0 m) (O.value 0) (O.value m)).1 hEndpoint
  have hDepth := O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth m
  have hOdd := O.segmentWord_oddSteps 0 m
  rw [hDepth, hOdd] at hEq
  exact hEq.symm

end OddOrbit
end Collatz3
