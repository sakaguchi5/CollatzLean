import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Collatz3 Arithmetic: `2` の `3` 冪法における exponent divisibility

source-one residual では

`3^k ∣ 2^m - 1`

が現れる。このとき必要なのは exact order を全面的に展開することではなく、

`2^m = 1 (mod 3^k)  ->  2 * 3^(k-1) ∣ m`

という後段向けの divisibility だけである。

証明は odd-prime LTE の `padicValNat.pow_sub_pow` を `4^(m/2)-1` に適用する。
-/

namespace Collatz3
namespace Arithmetic

/--
`k>0` で `2^m = 1 (mod 3^k)` なら、`2 * 3^(k-1)` が `m` を割る。

これは `ord_(3^k)(2)=2*3^(k-1)` の、後段で必要な divisibility 版。
-/
theorem two_mul_threePow_pred_dvd_exponent_of_twoPow_modEq_one
    {k m : ℕ}
    (hk : 0 < k)
    (h : 2 ^ m ≡ 1 [MOD 3 ^ k]) :
    2 * 3 ^ (k - 1) ∣ m := by
  by_cases hm0 : m = 0
  · subst m
    exact dvd_zero _
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hThreeDvd : 3 ∣ 3 ^ k := by
    exact pow_dvd_pow 3 (by omega : 1 ≤ k)
  have hMod3 : 2 ^ m ≡ 1 [MOD 3] :=
    h.of_dvd hThreeDvd
  have hPow3 : (2 : ZMod 3) ^ m = 1 := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hMod3
  have hPeriod : (2 : ZMod 3) ^ 2 = 1 := by
    decide
  have hmEven : m % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · exact h0
    · exfalso
      have hm : m = 2 * (m / 2) + 1 := by
        have hDecomp := Nat.mod_add_div m 2
        omega
      have hBad : (2 : ZMod 3) = 1 := by
        rw [hm, pow_add, pow_mul, hPeriod] at hPow3
        simpa using hPow3
      exact (by decide : (2 : ZMod 3) ≠ 1) hBad
  let t : ℕ := m / 2
  have hmEq : m = 2 * t := by
    have hDiv := Nat.mod_add_div m 2
    dsimp [t]
    omega
  have htPos : 0 < t := by
    dsimp [t]
    have hmPos : 0 < m := Nat.pos_of_ne_zero hm0
    omega
  have htNe : t ≠ 0 := Nat.ne_of_gt htPos
  have hOneLe : 1 ≤ 2 ^ m := by
    have hPos : 0 < 2 ^ m := by
      positivity
    omega
  have hDvdM : 3 ^ k ∣ 2 ^ m - 1 := by
    exact (Nat.modEq_iff_dvd' hOneLe).mp h.symm
  have hDvd4 : 3 ^ k ∣ 4 ^ t - 1 := by
    simpa [hmEq, pow_mul] using hDvdM
  have hVal :
      padicValNat 3 (4 ^ t - 1) = 1 + padicValNat 3 t := by
    have hLTE :=
      padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
        (by decide : Odd 3)
        (by norm_num) (by norm_num) (by norm_num) htNe
    simpa using hLTE
  have hDiffNe : 4 ^ t - 1 ≠ 0 := by
    have hOneLt : 1 < 4 ^ t :=
      one_lt_pow₀ (by norm_num : (1 : ℕ) < 4) htNe
    omega
  have hkVal : k ≤ padicValNat 3 (4 ^ t - 1) :=
    (padicValNat_dvd_iff_le hDiffNe).mp hDvd4
  have hPredVal : k - 1 ≤ padicValNat 3 t := by
    rw [hVal] at hkVal
    omega
  have hThreePredDvd : 3 ^ (k - 1) ∣ t :=
    (padicValNat_dvd_iff_le htNe).mpr hPredVal
  rcases hThreePredDvd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hmEq, hq]
  ring

end Arithmetic
end Collatz3
