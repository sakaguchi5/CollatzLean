import CollatzLean.Collatz4.Parametric.ReachabilityWord
import CollatzLean.Collatz4.Family.Branch

import Mathlib.Tactic.NormNum
--import Mathlib.Tactic

/-!
# Collatz4.Parametric.BranchTerminalMacro

標準 branch point へ入る最後の odd step を、target `M` に依存しない形で正規化する。

`P_{M,r} = 3^(r+1) * 2^(M-r) - 1`

へ `z` から1回で入るとする。最後の2指数は必ず奇数であり、ある `q>0` により

`e = 2*q - 1`

と書ける。さらに `A(z)=2*z+1` と

`S_q = 1 + 4 + ... + 4^(q-1)`

について exact identity

`A(z) + S_q = 3^r * 2^(M-r+2*q)`

が成り立つ。
-/

namespace Collatz4.Parametric

open Collatz4.Dynamics
open Collatz4.Family

/-- `S_q = 1+4+...+4^(q-1)`。除算を使わない再帰定義。 -/
def terminalGeom : ℕ → ℕ
  | 0 => 0
  | q + 1 => 4 * terminalGeom q + 1

/-- `3*S_q = 4^q-1`。 -/
theorem three_mul_terminalGeom (q : ℕ) :
    3 * terminalGeom q = 4 ^ q - 1 := by
  induction q with
  | zero => simp [terminalGeom]
  | succ q ih =>
      rw [terminalGeom, pow_succ]
      have hp : 0 < 4 ^ q := by positivity
      have hpow : 4 ^ q = 3 * terminalGeom q + 1 := by
        omega
      rw [hpow]
      omega

/-- `2^(2q)=4^q`。 -/
theorem two_pow_two_mul (q : ℕ) :
    2 ^ (2 * q) = 4 ^ q := by
  rw [pow_mul]
  norm_num

/-- 偶数指数の `2^n` は `1 mod 3`。 -/
theorem two_pow_even_mod_three (q : ℕ) :
    2 ^ (2 * q) % 3 = 1 := by
  rw [two_pow_two_mul]
  induction q with
  | zero => norm_num
  | succ q ih =>
      rw [pow_succ]
      simp [Nat.mul_mod, ih]

/-- 奇数指数の `2^n` は `2 mod 3`。 -/
theorem two_pow_odd_mod_three (q : ℕ) :
    2 ^ (2 * q + 1) % 3 = 2 := by
  rw [pow_add]
  calc
    (2 ^ (2 * q) * 2 ^ 1) % 3 =
        (((2 ^ (2 * q)) % 3) * ((2 ^ 1) % 3)) % 3 := by
      exact Nat.mul_mod _ _ _
    _ = 2 := by
      rw [two_pow_even_mod_three]
      norm_num

/-- `2^n = 1 mod 3` なら `n` は偶数で、`n = 2 * (n / 2)`。 -/
theorem two_pow_mod_three_eq_one_double_div
    {n : ℕ}
    (h : 2 ^ n % 3 = 1) :
    n = 2 * (n / 2) := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  by_cases hzero : n % 2 = 0
  · have hdecomp := Nat.mod_add_div n 2
    omega
  · have hone : n % 2 = 1 := by
      omega
    have hn : n = 2 * (n / 2) + 1 := by
      have hdecomp := Nat.mod_add_div n 2
      omega
    have hodd := two_pow_odd_mod_three (n / 2)
    rw [hn] at h
    omega

/-- `2^n = 1 mod 3` なら `n` は偶数。 -/
theorem exists_double_of_two_pow_mod_three_eq_one
    {n : ℕ}
    (h : 2 ^ n % 3 = 1) :
    ∃ q : ℕ, n = 2 * q := by
  refine ⟨n / 2, ?_⟩
  exact two_pow_mod_three_eq_one_double_div h

/-- branch point に `1` を戻した exact product。 -/
theorem branchPoint_add_one (M r : ℕ) :
    branchPoint M r + 1 =
      3 ^ (r + 1) * 2 ^ (M - r) := by
  unfold branchPoint
  have hp : 0 < 3 ^ (r + 1) * 2 ^ (M - r) := by positivity
  omega

/--
最後の exponent をまだ `q` に直さない段階の correction。

実際に branch point へ入る場合、後でこれは `terminalGeom q` と一致する。
-/
def terminalCorrection (M r z : ℕ) : ℕ :=
  3 ^ r * 2 ^ (M - r + stepExponent z + 1) - lifted z

/-- branch point へ入る1 step から得られる3倍した exact balance。 -/
private theorem terminal_three_balance
    {M r z : ℕ}
    (hhit : oddStep z = branchPoint M r) :
    3 * lifted z + (2 ^ (stepExponent z + 1) - 1) =
      3 * (3 ^ r * 2 ^ (M - r + stepExponent z + 1)) := by
  have hstep := step_exact z
  rw [hhit] at hstep
  have hp : 0 < 2 ^ (stepExponent z + 1) := by positivity
  calc
    3 * lifted z + (2 ^ (stepExponent z + 1) - 1) =
        2 * (3 * z + 1) + 2 ^ (stepExponent z + 1) := by
      unfold lifted
      omega
    _ = 2 * (2 ^ stepExponent z * branchPoint M r) +
          2 ^ (stepExponent z + 1) := by
      rw [← hstep]
    _ = 2 ^ (stepExponent z + 1) * (branchPoint M r + 1) := by
      rw [pow_succ]
      ring
    _ = 2 ^ (stepExponent z + 1) *
          (3 ^ (r + 1) * 2 ^ (M - r)) := by
      rw [branchPoint_add_one]
    _ = 3 ^ (r + 1) *
          2 ^ ((stepExponent z + 1) + (M - r)) := by
      have hpowAdd :
          2 ^ ((stepExponent z + 1) + (M - r)) =
            2 ^ (stepExponent z + 1) * 2 ^ (M - r) := by
        rw [pow_add]
      rw [hpowAdd]
      ring
    _ = 3 * (3 ^ r * 2 ^ (M - r + stepExponent z + 1)) := by
      have h3 : 3 ^ (r + 1) = 3 * 3 ^ r := by
        rw [pow_succ]
        ring
      have hexp :
          (stepExponent z + 1) + (M - r) =
            M - r + stepExponent z + 1 := by omega
      rw [h3, hexp]
      ring

/-- correction を足すと terminal target へ exact に一致する。 -/
theorem lifted_add_terminalCorrection
    {M r z : ℕ}
    (hhit : oddStep z = branchPoint M r) :
    lifted z + terminalCorrection M r z =
      3 ^ r * 2 ^ (M - r + stepExponent z + 1) := by
  have hbal := terminal_three_balance hhit
  let R : ℕ := 3 ^ r * 2 ^ (M - r + stepExponent z + 1)
  have hle : lifted z ≤ R := by
    dsimp [R]
    omega
  unfold terminalCorrection
  dsimp [R] at hle ⊢
  omega

/-- correction の3倍は `2^(e+1)-1`。 -/
theorem three_mul_terminalCorrection
    {M r z : ℕ}
    (hhit : oddStep z = branchPoint M r) :
    3 * terminalCorrection M r z =
      2 ^ (stepExponent z + 1) - 1 := by
  have hbal := terminal_three_balance hhit
  let R : ℕ := 3 ^ r * 2 ^ (M - r + stepExponent z + 1)
  have hle : lifted z ≤ R := by
    dsimp [R]
    omega
  unfold terminalCorrection
  dsimp [R] at hle ⊢
  omega

/-- branch terminal macro の正規化済みデータ。 -/
structure BranchTerminalMacroData (M r z : ℕ) where
  q : ℕ
  q_pos : 0 < q
  exponent_eq : stepExponent z = 2 * q - 1
  terminal_eq :
    lifted z + terminalGeom q =
      3 ^ r * 2 ^ (M - r + 2 * q)

/--
標準 branch point へ実際に1 step で入るなら terminal macro data が存在する。

最後の2指数が奇数であることも、この定理の中で導く。
-/
def branchTerminalMacroData_of_hit
    {M r z : ℕ}
    (hhit : oddStep z = branchPoint M r) :
    BranchTerminalMacroData M r z := by
  have hc := three_mul_terminalCorrection hhit
  have hp : 0 < 2 ^ (stepExponent z + 1) := by positivity
  have hpowEq :
      2 ^ (stepExponent z + 1) =
        3 * terminalCorrection M r z + 1 := by
    omega
  have hmod : 2 ^ (stepExponent z + 1) % 3 = 1 := by
    rw [hpowEq]
    simp [Nat.add_mod]
  let q : ℕ := (stepExponent z + 1) / 2
  have hqdouble :
      stepExponent z + 1 = 2 * q := by
    dsimp [q]
    exact two_pow_mod_three_eq_one_double_div hmod
  have hqpos : 0 < q := by omega
  have heq : stepExponent z = 2 * q - 1 := by omega
  have hpow2 :
      2 ^ (stepExponent z + 1) = 4 ^ q := by
    have hexp : stepExponent z + 1 = 2 * q := by omega
    rw [hexp, two_pow_two_mul]
  have hgeom : terminalCorrection M r z = terminalGeom q := by
    have h1 := three_mul_terminalCorrection hhit
    have h2 := three_mul_terminalGeom q
    rw [hpow2] at h1
    omega
  have hterm := lifted_add_terminalCorrection hhit
  have hexp :
      M - r + stepExponent z + 1 = M - r + 2 * q := by
    omega
  refine ⟨q, hqpos, heq, ?_⟩
  rw [← hgeom]
  rw [← hexp]
  exact hterm

end Collatz4.Parametric
