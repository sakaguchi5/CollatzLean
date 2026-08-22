import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerFiniteWidth112
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPrefixOstrowski

set_option linter.style.emptyLine false

/-!
# Pure B single-corner: exact defect recurrence

single-corner straight interval `[b,c)` の checkpoint は

  beta(b)-1,
  beta(b)-1+1,
  ...

と一段ずつ進む。一方 critical checkpoint は `beta(b+n)`。
そこで critical numerator から single-corner numerator へ落とした局所 defect を

  C_b(0) = 0,
  C_b(n+1)
    = 3*C_b(n)
      + (2^beta(b+n) - 2^(beta(b)-1+n))

で定義する。

この recurrence は telescope して

  C_b(n)
    = Psi(b+n)
      - 3^n Psi(b)
      - 2^(beta(b)-1) (3^n-2^n)

となる。

従って `b<=c<=m` では scanner が使っている exact single-corner affine expression は

  A(m,b,c) = Psi(m) - 3^(m-c) C_b(c-b)

へ縮約される。

さらに `b>0`, `n>0` では

  C_b(n) = 2^(beta(b)-1) * U_b(n)

かつ `U_b(n)` は odd。つまり single-corner correction の最初の nonzero 2-adic bit は
exact に `beta(b)-1` である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- Beatty index は `n` 回右へ進むと少なくとも `n` 増える。 -/
theorem beattyIndex_add_ge_add
    (b n : ℕ) :
    beattyIndex b + n ≤ beattyIndex (b + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hStep := beattyIndex_lt_succ (b + n)
      have hIdx : b + (n + 1) = (b + n) + 1 := by omega
      rw [hIdx]
      omega

/-- `beta(b)>0` なら straight line は各 critical checkpoint より strict に低い。 -/
theorem singleCornerLine_lt_beatty
    {b n : ℕ}
    (hb : 0 < beattyIndex b) :
    beattyIndex b - 1 + n < beattyIndex (b + n) := by
  have h := beattyIndex_add_ge_add b n
  omega

/-- `2^b-2^a` の exact common-power factorization。 -/
theorem twoPow_sub_twoPow_eq_factor
    {a b : ℕ}
    (hab : a ≤ b) :
    2 ^ b - 2 ^ a =
      2 ^ a * (2 ^ (b - a) - 1) := by
  have hbEq : b = a + (b - a) := by omega
  rw [hbEq, pow_add]
  calc
    2 ^ a * 2 ^ (b - a) - 2 ^ a
        = 2 ^ a * 2 ^ (b - a) - 2 ^ a * 1 := by simp
    _ = 2 ^ a * (2 ^ (b - a) - 1) := by
      rw [← Nat.mul_sub_left_distrib]
  simp

/-- single-corner straight block の critical-minus-line defect。 -/
def singleCornerDefect
    (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      3 * singleCornerDefect b n +
        (2 ^ beattyIndex (b + n) -
          2 ^ (beattyIndex b - 1 + n))

@[simp] theorem singleCornerDefect_zero
    (b : ℕ) :
    singleCornerDefect b 0 = 0 := rfl

/-- recurrence equation の名前付き wrapper。 -/
theorem singleCornerDefect_succ
    (b n : ℕ) :
    singleCornerDefect b (n + 1) =
      3 * singleCornerDefect b n +
        (2 ^ beattyIndex (b + n) -
          2 ^ (beattyIndex b - 1 + n)) := rfl

/--
`C_b(n)` から common `2^(beta(b)-1)` を除いた exact unit recurrence。
-/
def singleCornerDefectUnit
    (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      3 * singleCornerDefectUnit b n +
        2 ^ n *
          (2 ^
              (beattyIndex (b + n) -
                (beattyIndex b - 1 + n)) - 1)

@[simp] theorem singleCornerDefectUnit_zero
    (b : ℕ) :
    singleCornerDefectUnit b 0 = 0 := rfl

@[simp] theorem singleCornerDefectUnit_succ
    (b n : ℕ) :
    singleCornerDefectUnit b (n + 1) =
      3 * singleCornerDefectUnit b n +
        2 ^ n *
          (2 ^
              (beattyIndex (b + n) -
                (beattyIndex b - 1 + n)) - 1) := rfl

/-- defect は common dyadic factor と unit recurrence に exact 分解する。 -/
theorem singleCornerDefect_eq_pow_mul_unit
    {b : ℕ}
    (hb : 0 < beattyIndex b)
    (n : ℕ) :
    singleCornerDefect b n =
      2 ^ (beattyIndex b - 1) * singleCornerDefectUnit b n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [singleCornerDefect_succ, singleCornerDefectUnit_succ, ih]
      have hLine := singleCornerLine_lt_beatty (b := b) (n := n) hb
      have hPowLe :
          2 ^ (beattyIndex b - 1 + n) ≤
            2 ^ beattyIndex (b + n) :=
        Nat.pow_le_pow_right
          (by omega : 0 < (2 : ℕ)) (Nat.le_of_lt hLine)
      have hFactor :=
        twoPow_sub_twoPow_eq_factor
          (a := beattyIndex b - 1 + n)
          (b := beattyIndex (b + n))
          (Nat.le_of_lt hLine)
      rw [hFactor]
      have hPowAdd :
          2 ^ (beattyIndex b - 1 + n) =
            2 ^ (beattyIndex b - 1) * 2 ^ n := by
        rw [pow_add]
      rw [hPowAdd]
      ring

/-- positive-length unit は odd。 -/
theorem singleCornerDefectUnit_mod_two
    {b n : ℕ}
    (hb : 0 < beattyIndex b)
    (hn : 0 < n) :
    singleCornerDefectUnit b n % 2 = 1 := by
  revert hn
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst n
        have hDiff :
            beattyIndex b - (beattyIndex b - 1) = 1 := by
          omega
        simp [singleCornerDefectUnit, hDiff]
      · have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
        have hIH := ih hnPos
        have hPowEven : 2 ^ n % 2 = 0 := by
          obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
          simp [pow_succ]
        simp [
          singleCornerDefectUnit,
          Nat.add_mod,
          Nat.mul_mod,
          hIH,
          hPowEven
        ]

/-- critical prefix numerator の one-step recurrence。 -/
theorem criticalPrefixPhiZ_succ_local
    (n : ℕ) :
    criticalPrefixPhiZ (n + 1) =
      3 * criticalPrefixPhiZ n +
        (2 : ℤ) ^ beattyIndex n := by
  classical
  unfold criticalPrefixPhiZ
  rw [Finset.sum_range_succ]
  have hPrefix :
      Finset.sum (Finset.range n)
          (fun k =>
            (2 : ℤ) ^ beattyIndex k *
              (3 : ℤ) ^ (n + 1 - 1 - k)) =
        3 *
          Finset.sum (Finset.range n)
            (fun k =>
              (2 : ℤ) ^ beattyIndex k *
                (3 : ℤ) ^ (n - 1 - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < n := Finset.mem_range.mp hk
    have hExp :
        n + 1 - 1 - k = (n - 1 - k) + 1 := by
      omega
    rw [hExp, pow_succ]
    ring
  rw [hPrefix]
  have hLast : n + 1 - 1 - n = 0 := by omega
  rw [hLast, pow_zero, mul_one]

/--
recurrence defect の closed telescope identity。Int cast で subtraction を exact に保持する。
-/
theorem singleCornerDefect_cast_eq_closed
    {b : ℕ}
    (hb : 0 < beattyIndex b)
    (n : ℕ) :
    (singleCornerDefect b n : ℤ) =
      criticalPrefixPhiZ (b + n) -
        (3 : ℤ) ^ n * criticalPrefixPhiZ b -
        (2 : ℤ) ^ (beattyIndex b - 1) *
          ((3 : ℤ) ^ n - (2 : ℤ) ^ n) := by
  induction n with
  | zero =>
      simp [singleCornerDefect]
  | succ n ih =>
      rw [singleCornerDefect_succ]
      have hLine := singleCornerLine_lt_beatty (b := b) (n := n) hb
      have hPowLe :
          2 ^ (beattyIndex b - 1 + n) ≤
            2 ^ beattyIndex (b + n) :=
        Nat.pow_le_pow_right
          (by omega : 0 < (2 : ℕ)) (Nat.le_of_lt hLine)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hPowLe]
      push_cast
      rw [ih]
      have hIdx : b + (n + 1) = (b + n) + 1 := by omega
      rw [hIdx, criticalPrefixPhiZ_succ_local]
      have hLinePow :
          (2 : ℤ) ^ (beattyIndex b - 1 + n) =
            (2 : ℤ) ^ (beattyIndex b - 1) * (2 : ℤ) ^ n := by
        rw [pow_add]
      rw [hLinePow]
      have h3 : (3 : ℤ) ^ (n + 1) = (3 : ℤ) ^ n * 3 := by
        rw [pow_succ]
      have h2 : (2 : ℤ) ^ (n + 1) = (2 : ℤ) ^ n * 2 := by
        rw [pow_succ]
      rw [h3, h2]
      ring

/--
finite scanner の closed affine expression を、array table に依存しない mathematical Int form
として固定する。
-/
def singleCornerModelAffineZ
    (m b c : ℕ) : ℤ :=
  (3 : ℤ) ^ (m - b) * criticalPrefixPhiZ b +
    (2 : ℤ) ^ (beattyIndex b - 1) *
      (3 : ℤ) ^ (m - c) *
        ((3 : ℤ) ^ (c - b) - (2 : ℤ) ^ (c - b)) +
    (criticalPrefixPhiZ m -
      (3 : ℤ) ^ (m - c) * criticalPrefixPhiZ c)

/--
closed model affine numerator は critical numerator minus transported local defect。
-/
theorem singleCornerModelAffine_eq_critical_sub_defect
    {m b c : ℕ}
    (hb : 0 < beattyIndex b)
    (hbc : b ≤ c)
    (hcm : c ≤ m) :
    singleCornerModelAffineZ m b c =
      criticalPrefixPhiZ m -
        (3 : ℤ) ^ (m - c) *
          (singleCornerDefect b (c - b) : ℤ) := by
  rw [singleCornerDefect_cast_eq_closed hb (c - b)]
  have hBC : b + (c - b) = c := Nat.add_sub_of_le hbc
  rw [hBC]
  have hExp : (m - c) + (c - b) = m - b := by
    omega
  have hPow :
      (3 : ℤ) ^ (m - b) =
        (3 : ℤ) ^ (m - c) * (3 : ℤ) ^ (c - b) := by
    rw [← pow_add, hExp]
  unfold singleCornerModelAffineZ
  rw [hPow]
  ring

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/--
actual single-corner defect の exact 2-adic statement。

`C = 2^(beta(b)-1) * u` かつ `u` odd なので、最初の nonzero 2-adic bit は
exact に `beta(b)-1`。
-/
theorem v2_singleCornerDefect
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    ∃ u : ℕ,
      u % 2 = 1 ∧
      singleCornerDefect S.b S.width =
        2 ^ (beattyIndex S.b - 1) * u := by
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : S.b < P.m :=
    lt_of_lt_of_le S.b_lt_c hcLeM
  have hDepth := P.admissible.depth_le hbM
  rw [S.h_b_eq_one] at hDepth
  have hBetaPos : 0 < beattyIndex S.b := by omega
  have hWidthPos : 0 < S.width := S.width_pos
  let u := singleCornerDefectUnit S.b S.width
  refine ⟨u, ?_, ?_⟩
  · simpa [u] using
      singleCornerDefectUnit_mod_two
        (b := S.b) (n := S.width) hBetaPos hWidthPos
  · simpa [u] using
      singleCornerDefect_eq_pow_mul_unit hBetaPos S.width

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
