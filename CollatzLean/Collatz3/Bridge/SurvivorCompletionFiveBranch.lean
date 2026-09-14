import CollatzLean.Collatz3.Bridge.SurvivorCompletionFutureMinimum
import CollatzLean.Collatz3.Arithmetic.ResidueFiveCandidates
import CollatzLean.Collatz3.Arithmetic.ModTwoPow
import Mathlib.Data.ZMod.Basic

/-!
# Collatz3 Bridge: completion cocycle の exact residue class と5候補定理

`SurvivorCompletionCocycle` では、十分先の隣接 lift から

`q_m = 2^(e_m) t_(m+1) - t_m`

を作り、

`v₂(3^(m+1) q_m + 1) = E_m`

を divisibility の形で証明した。

特に `e_m = 1` の future-minimum anchor では

`-2^(E_m+1) < q_m < 2^(E_m+3)`

も同時に成立する。

このファイルではさらに一歩進める。

1. `3^(m+1) q + 1 ≡ 2^E (mod 2^(E+1))` を解き、
   `m,E` だけから決まる canonical residue `r(m,E)` を定義する。
2. actual cocycle `q_m` はその residue class に exact に属する。
3. `M = 2^(E_m+1)` とすると、`q_m` は

   `r-M, r, r+M, r+2M, r+3M`

   の5候補のどれかに限られる。
4. この5分岐 packet は任意に遠い actual future-minimum anchor で必ず現れる。

新しい orbit notion は導入しない。canonical residue は既存の
`Arithmetic.solveThreePow` の最小非負代表としてのみ定義する。
-/

namespace Collatz3
namespace Bridge

/--
`3^(m+1) q + 1 ≡ 2^E (mod 2^(E+1))`
を満たす `q` の canonical residue。

`3^(m+1)` は 2冪法で単元なので解は一意。
`solveThreePow` で

`3^(m+1) q = 2^E - 1`

を解き、その `ZMod` 値の最小非負代表を取る。
-/
def completionCocycleResidue
    (m E : ℕ) : ℕ :=
  (Arithmetic.solveThreePow
    (m + 1)
    (E + 1)
    ((((2 ^ E : ℕ) :
        ZMod (Arithmetic.twoPowModulus (E + 1)))) - 1)).val

/-- canonical cocycle residue は法 `2^(E+1)` 未満。 -/
theorem completionCocycleResidue_lt_modulus
    (m E : ℕ) :
    completionCocycleResidue m E < 2 ^ (E + 1) := by
  let z :=
    Arithmetic.solveThreePow
      (m + 1)
      (E + 1)
      ((((2 ^ E : ℕ) :
          ZMod (Arithmetic.twoPowModulus (E + 1)))) - 1)
  let : NeZero (Arithmetic.twoPowModulus (E + 1)) :=
    ⟨Nat.ne_of_gt (Arithmetic.twoPowModulus_pos (E + 1))⟩
  have hz : z.val < Arithmetic.twoPowModulus (E + 1) := ZMod.val_lt z
  simpa [completionCocycleResidue, z, Arithmetic.twoPowModulus] using hz

/-- canonical residue を `ZMod` に戻すと `solveThreePow` の解そのもの。 -/
theorem completionCocycleResidue_cast
    (m E : ℕ) :
    ((completionCocycleResidue m E : ℕ) :
        ZMod (Arithmetic.twoPowModulus (E + 1))) =
      Arithmetic.solveThreePow
        (m + 1)
        (E + 1)
        ((((2 ^ E : ℕ) :
            ZMod (Arithmetic.twoPowModulus (E + 1)))) - 1) := by
  let : NeZero (Arithmetic.twoPowModulus (E + 1)) :=
    ⟨Nat.ne_of_gt (Arithmetic.twoPowModulus_pos (E + 1))⟩
  unfold completionCocycleResidue
  exact ZMod.natCast_zmod_val _

/--
canonical residue は defining equation

`3^(m+1) r + 1 = 2^E  (mod 2^(E+1))`

を満たす。
-/
theorem completionCocycleResidue_spec_zmod
    (m E : ℕ) :
    (((3 ^ (m + 1) : ℕ) :
        ZMod (Arithmetic.twoPowModulus (E + 1))) *
      ((completionCocycleResidue m E : ℕ) :
        ZMod (Arithmetic.twoPowModulus (E + 1)))) + 1 =
      ((2 ^ E : ℕ) :
        ZMod (Arithmetic.twoPowModulus (E + 1))) := by
  rw [completionCocycleResidue_cast]
  have h :=
    Arithmetic.threePow_mul_solveThreePow
      (m + 1)
      (E + 1)
      ((((2 ^ E : ℕ) :
          ZMod (Arithmetic.twoPowModulus (E + 1)))) - 1)
  calc
    (((3 ^ (m + 1) : ℕ) :
        ZMod (Arithmetic.twoPowModulus (E + 1))) *
      Arithmetic.solveThreePow
        (m + 1)
        (E + 1)
        ((((2 ^ E : ℕ) :
            ZMod (Arithmetic.twoPowModulus (E + 1)))) - 1)) + 1
        =
      ((((2 ^ E : ℕ) :
          ZMod (Arithmetic.twoPowModulus (E + 1)))) - 1) + 1 := by
            rw [h]
    _ = ((2 ^ E : ℕ) :
          ZMod (Arithmetic.twoPowModulus (E + 1))) := by ring

end Bridge

namespace OddOrbit

open Bridge

/-
隣接 completion cocycle の signed lift step は、`m,E_m` だけで決まる
canonical residue class に属する。

これは exact cocycle equation の奇数 cofactor を modulo `2^(E_m+1)` へ落とし、
`solveThreePow` の一意性を使ったもの。
-/

/--
cocycle factor が奇数なら、mod `2^(E+1)` で
`3^(m+1) q = 2^E - 1`
という一次合同式になる。
-/
theorem endpointCompletionLiftStep_zmod_linear
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u) :
    let E := O.endpointCompletionExtraDepth m
    let M := 2 ^ (E + 1)
    (((3 ^ (m + 1) : ℕ) : ZMod M) *
        (endpointCompletionLiftStep O m t u : ZMod M)) =
      (((2 ^ E : ℕ) : ZMod M) - 1) := by
  dsimp
  let E := O.endpointCompletionExtraDepth m
  let M := 2 ^ (E + 1)
  let q : ℤ := endpointCompletionLiftStep O m t u
  let F : ℤ :=
    (2 : ℤ) ^ completionCriticalStep m *
        (O.endpointCompletionEnd SInf
          (by omega : 0 < m + 1) : ℤ) -
      3 * (O.endpointCompletionEnd SInf hm : ℤ)
  have hCoc :
      (3 : ℤ) ^ (m + 1) * q + 1 =
        (2 : ℤ) ^ E * F := by
    simpa [q, E, F] using
      O.endpointCompletion_endpoint_cocycle
        SInf hm hStartM hStartN
  have hOdd : Odd F := by
    simpa [F] using
      O.endpointCompletionCocycleFactor_odd SInf hm
  rcases hOdd with ⟨z, hz⟩
  have hMPos : 0 < M := by
    dsimp [M]
    exact Arithmetic.twoPow_pos (E + 1)
  let : NeZero M := ⟨Nat.ne_of_gt hMPos⟩
  have hPowZero :
      (2 : ZMod M) ^ (E + 1) = 0 := by
    dsimp [M]
    exact ZMod.natCast_pow_eq_zero_of_le 2 le_rfl
  have hCastCoc :=
    congrArg (fun a : ℤ => (a : ZMod M)) hCoc
  rw [hz] at hCastCoc
  push_cast at hCastCoc
  have hRight :
      (2 : ZMod M) ^ E *
          (2 * (z : ZMod M) + 1) =
        (2 : ZMod M) ^ E := by
    calc
      (2 : ZMod M) ^ E *
          (2 * (z : ZMod M) + 1)
          =
          (2 : ZMod M) ^ E +
            (2 : ZMod M) ^ (E + 1) * (z : ZMod M) := by
              rw [pow_succ]
              ring
      _ = (2 : ZMod M) ^ E := by
          rw [hPowZero]
          simp
  have hEquation :
      (3 : ZMod M) ^ (m + 1) * (q : ZMod M) + 1 =
        (2 : ZMod M) ^ E := by
    exact hCastCoc.trans hRight
  have h3 :
      (((3 : ℕ) : ZMod M)) = (3 : ZMod M) := by
    norm_num
  have h2 :
      (((2 : ℕ) : ZMod M)) = (2 : ZMod M) := by
    norm_num
  have hLinearLocal :
      (((3 ^ (m + 1) : ℕ) : ZMod M) * (q : ZMod M)) =
        (((2 ^ E : ℕ) : ZMod M) - 1) := by
    apply (eq_sub_iff_add_eq).2
    simpa only [Nat.cast_pow, h3, h2] using hEquation
  simpa only [E, M, q] using hLinearLocal

/--
`3^(m+1) q = 2^E - 1` を満たす解は
`solveThreePow` が返す解に一致する。
-/
theorem endpointCompletionLiftStep_zmod_eq_solveThreePow
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u) :
    let E := O.endpointCompletionExtraDepth m
    let M := Arithmetic.twoPowModulus (E + 1)
    (endpointCompletionLiftStep O m t u : ZMod M) =
      Arithmetic.solveThreePow
        (m + 1)
        (E + 1)
        ((((2 ^ E : ℕ) : ZMod M)) - 1) := by
  dsimp
  let E := O.endpointCompletionExtraDepth m
  let M := Arithmetic.twoPowModulus (E + 1)
  have hLinear :=
    O.endpointCompletionLiftStep_zmod_linear
      SInf hm hStartM hStartN
  have hLinear' :
      (((3 ^ (m + 1) : ℕ) : ZMod M) *
          (endpointCompletionLiftStep O m t u : ZMod M)) =
        (((2 ^ E : ℕ) : ZMod M) - 1) := by
    dsimp only at hLinear
    dsimp only [E, M, Arithmetic.twoPowModulus]
    exact hLinear
  exact
    Arithmetic.solveThreePow_unique
      (m + 1)
      (E + 1)
      ((((2 ^ E : ℕ) : ZMod M)) - 1)
      (endpointCompletionLiftStep O m t u : ZMod M)
      hLinear'

/--
`solveThreePow` で得られる residue は
`completionCocycleResidue` の canonical representative と一致する。
-/
theorem solveThreePow_eq_completionCocycleResidue
    (m E : ℕ) :
    Arithmetic.solveThreePow
        (m + 1)
        (E + 1)
        ((((2 ^ E : ℕ) :
            ZMod (Arithmetic.twoPowModulus (E + 1)))) - 1)
      =
    ((completionCocycleResidue m E : ℕ) :
      ZMod (Arithmetic.twoPowModulus (E + 1))) := by
  simpa only using
    (completionCocycleResidue_cast m E).symm

/--
actual lift step は canonical cocycle residue と
mod `2^(E+1)` で一致する。
-/
theorem endpointCompletionLiftStep_modEq_completionCocycleResidue
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u) :
    endpointCompletionLiftStep O m t u ≡
      (completionCocycleResidue m
        (O.endpointCompletionExtraDepth m) : ℤ)
      [ZMOD
        ((2 : ℤ) ^
          (O.endpointCompletionExtraDepth m + 1))] := by
  let E := O.endpointCompletionExtraDepth m
  let M := Arithmetic.twoPowModulus (E + 1)
  let q : ℤ := endpointCompletionLiftStep O m t u
  have hSolve :
      (q : ZMod M) =
        Arithmetic.solveThreePow
          (m + 1)
          (E + 1)
          ((((2 ^ E : ℕ) : ZMod M)) - 1) := by
    simpa only [q, E, M] using
      O.endpointCompletionLiftStep_zmod_eq_solveThreePow
        SInf hm hStartM hStartN
  have hResidue :
      Arithmetic.solveThreePow
          (m + 1)
          (E + 1)
          ((((2 ^ E : ℕ) : ZMod M)) - 1)
        =
      ((completionCocycleResidue m E : ℕ) : ZMod M) := by
    simpa only [M] using
      solveThreePow_eq_completionCocycleResidue m E
  have hCastEq :
      (q : ZMod M) =
        ((completionCocycleResidue m E : ℤ) : ZMod M) := by
    calc
      (q : ZMod M)
          =
          Arithmetic.solveThreePow
            (m + 1)
            (E + 1)
            ((((2 ^ E : ℕ) : ZMod M)) - 1) := hSolve
      _ =
          ((completionCocycleResidue m E : ℕ) : ZMod M) := hResidue
      _ =
          ((completionCocycleResidue m E : ℤ) : ZMod M) := by
            norm_num
  have hMod :
      q ≡ (completionCocycleResidue m E : ℤ)
        [ZMOD (M : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff
      q
      (completionCocycleResidue m E : ℤ)
      M).1 hCastEq
  simpa [q, E, M, Arithmetic.twoPowModulus] using hMod

/--
canonical residue class を survivor defect 座標で書いた形。

`E_m = δ_m+1` なので法は `2^(δ_m+2)`、residue は `r(m,δ_m+1)`。
-/
theorem endpointCompletionLiftStep_modEq_completionCocycleResidue_defect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u) :
    endpointCompletionLiftStep O m t u ≡
      (completionCocycleResidue
        m (infiniteSurvivorDefect O.exponent m + 1) : ℤ)
      [ZMOD ((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent m + 2))] := by
  have h :=
    O.endpointCompletionLiftStep_modEq_completionCocycleResidue
      SInf hm hStartM hStartN
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at h
  simpa [Nat.add_assoc] using h

/--
`e_m=1` の位置では signed cocycle `q_m` は canonical residue class の
5候補に必ず入る。

`E=E_m`, `M=2^(E+1)`, `r=r(m,E)` とすると

`q_m ∈ {r-M, r, r+M, r+2M, r+3M}`。

候補数が defect や `E` に依存しないことが重要。
-/
theorem endpointCompletionLiftStep_five_candidates_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (he : O.exponent m = 1)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let E := O.endpointCompletionExtraDepth m
    let M : ℤ := (2 : ℤ) ^ (E + 1)
    let r : ℤ := completionCocycleResidue m E
    endpointCompletionLiftStep O m t u = r - M ∨
      endpointCompletionLiftStep O m t u = r ∨
      endpointCompletionLiftStep O m t u = r + M ∨
      endpointCompletionLiftStep O m t u = r + 2 * M ∨
      endpointCompletionLiftStep O m t u = r + 3 * M := by
  dsimp
  let E := O.endpointCompletionExtraDepth m
  let M : ℤ := (2 : ℤ) ^ (E + 1)
  let r : ℤ := completionCocycleResidue m E
  let q : ℤ := endpointCompletionLiftStep O m t u
  have hMod : q ≡ r [ZMOD M] := by
    simpa [q, r, E, M] using
      O.endpointCompletionLiftStep_modEq_completionCocycleResidue
        SInf hm hStartM hStartN
  have hr0 : 0 ≤ r := by
    simp [r]
  have hrLtNat := completionCocycleResidue_lt_modulus m E
  have hrM : r < M := by
    dsimp [r, M]
    exact_mod_cast hrLtNat
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hBounds :=
    O.endpointCompletionLiftStep_bounds_of_exponent_eq_one SInf he ht hu
  have hLow : -M < q := by
    simpa [q, E, M] using hBounds.1
  have hPow :
      (2 : ℤ) ^ (E + 3) = 4 * M := by
    dsimp [M]
    rw [show E + 3 = (E + 1) + 2 by omega, pow_add]
    norm_num
    omega
  have hHigh : q < 4 * M := by
    have h := hBounds.2
    rw [hPow] at h
    simpa [q] using h
  exact Arithmetic.five_candidates_of_modEq_of_short_window
    hM hr0 hrM hMod hLow hHigh

/--
前定理を survivor defect 座標で読んだ形。

`E_m = δ_m+1` なので法は `2^(δ_m+2)`。
canonical residue 自身も `r(m,δ_m+1)` として defect だけで指定される。
-/
theorem endpointCompletionLiftStep_five_candidates_defect_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (he : O.exponent m = 1)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let δ := infiniteSurvivorDefect O.exponent m
    let M : ℤ := (2 : ℤ) ^ (δ + 2)
    let r : ℤ := completionCocycleResidue m (δ + 1)
    endpointCompletionLiftStep O m t u = r - M ∨
      endpointCompletionLiftStep O m t u = r ∨
      endpointCompletionLiftStep O m t u = r + M ∨
      endpointCompletionLiftStep O m t u = r + 2 * M ∨
      endpointCompletionLiftStep O m t u = r + 3 * M := by
  have h :=
    O.endpointCompletionLiftStep_five_candidates_of_exponent_eq_one
      SInf hm he hStartM hStartN ht hu
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at h
  simpa [Nat.add_assoc] using h

/--
任意に遠い actual future-minimum `e_n=1` anchor で、
exact residue class と5候補 finite branch が同時に成立する。

従って infinite survivor が存在するなら、任意の `start` より後ろで必ず
「一つの canonical residue class + 最大5本の signed integer branch」
という状態へ入る。
-/
theorem exists_futureMinimum_exactResidue_fiveCandidates_after
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ t u : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 ∧
      O.endpointCompletionStart SInf hn =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent n * t ∧
      O.endpointCompletionStart SInf (by omega : 0 < n + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (n + 1) * u ∧
      endpointCompletionLiftStep O n t u ≡
        (completionCocycleResidue n (O.endpointCompletionExtraDepth n) : ℤ)
        [ZMOD ((2 : ℤ) ^ (O.endpointCompletionExtraDepth n + 1))] ∧
      (let E := O.endpointCompletionExtraDepth n
       let M : ℤ := (2 : ℤ) ^ (E + 1)
       let r : ℤ := completionCocycleResidue n E
       endpointCompletionLiftStep O n t u = r - M ∨
         endpointCompletionLiftStep O n t u = r ∨
         endpointCompletionLiftStep O n t u = r + M ∨
         endpointCompletionLiftStep O n t u = r + 2 * M ∨
         endpointCompletionLiftStep O n t u = r + 3 * M) := by
  rcases O.exists_futureMinimum_consecutiveCompletionNatLifts_after SInf start with
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, htPos, htOdd, htBound, hEndT,
      hStartU, huPos, huOdd, huBound, hEndU⟩
  have hResidue :=
    O.endpointCompletionLiftStep_modEq_completionCocycleResidue
      SInf hn hStartT hStartU
  have hFive :=
    O.endpointCompletionLiftStep_five_candidates_of_exponent_eq_one
      SInf hn he hStartT hStartU htBound huBound
  exact
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, hStartU,
      hResidue, hFive⟩

/--
future-minimum 5候補 theorem の defect 座標版。

法は `2^(δ_n+2)`、canonical residue は `r(n,δ_n+1)`。
A 型で `δ_n` が大きくなっても候補数は5のまま増えない。
-/
theorem exists_futureMinimum_exactResidue_fiveCandidates_defect_after
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ t u : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 ∧
      O.endpointCompletionStart SInf hn =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent n * t ∧
      O.endpointCompletionStart SInf (by omega : 0 < n + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (n + 1) * u ∧
      endpointCompletionLiftStep O n t u ≡
        (completionCocycleResidue
          n (infiniteSurvivorDefect O.exponent n + 1) : ℤ)
        [ZMOD ((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent n + 2))] ∧
      (let δ := infiniteSurvivorDefect O.exponent n
       let M : ℤ := (2 : ℤ) ^ (δ + 2)
       let r : ℤ := completionCocycleResidue n (δ + 1)
       endpointCompletionLiftStep O n t u = r - M ∨
         endpointCompletionLiftStep O n t u = r ∨
         endpointCompletionLiftStep O n t u = r + M ∨
         endpointCompletionLiftStep O n t u = r + 2 * M ∨
         endpointCompletionLiftStep O n t u = r + 3 * M) := by
  rcases O.exists_futureMinimum_consecutiveCompletionNatLifts_after SInf start with
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, htPos, htOdd, htBound, hEndT,
      hStartU, huPos, huOdd, huBound, hEndU⟩
  have hResidue :=
    O.endpointCompletionLiftStep_modEq_completionCocycleResidue_defect
      SInf hn hStartT hStartU
  have hFive :=
    O.endpointCompletionLiftStep_five_candidates_defect_of_exponent_eq_one
      SInf hn he hStartT hStartU htBound huBound
  exact
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, hStartU,
      hResidue, hFive⟩

end OddOrbit
end Collatz3
