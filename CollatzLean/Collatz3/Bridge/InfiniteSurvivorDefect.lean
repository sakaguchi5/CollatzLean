import CollatzLean.Collatz3.Bridge.CriticalSurvivorParity
import CollatzLean.Collatz3.Bridge.FullCriticalRestrictedPartition

/-!
# Collatz3 Bridge: 無限 survivor と Sturmian defect walk

odd-only exponent stream `e 0, e 1, ...` の prefix depth を

`D_m = e 0 + ... + e (m-1)`

とする。無限 survivor は、すべての odd block endpoint で

`D_m ≤ beattyIndex m`

を満たす正の exponent stream として保存する。

roof defect

`δ_m = beattyIndex m - D_m`

と normalized Beatty step

`s_m = (beattyIndex (m+1) - (m+1)) - (beattyIndex m - m)`

を使うと、`s_m ∈ {0,1}` であり

`δ_(m+1) = δ_m + s_m - (e_m - 1)`

が exact に成り立つ。
-/

namespace Collatz3
namespace Bridge

/-- 無限 exponent stream の先頭 `m` block の total two-depth。 -/
def infinitePrefixDepth (e : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => infinitePrefixDepth e m + e m

@[simp] theorem infinitePrefixDepth_zero (e : ℕ → ℕ) :
    infinitePrefixDepth e 0 = 0 := rfl

@[simp] theorem infinitePrefixDepth_succ
    (e : ℕ → ℕ)
    (m : ℕ) :
    infinitePrefixDepth e (m + 1) = infinitePrefixDepth e m + e m := rfl

/--
すべての exponent が正で、全 odd block endpoint が coefficient expansion 側に残る stream。
-/
def IsInfiniteSurvivorExponentStream (e : ℕ → ℕ) : Prop :=
  (∀ m : ℕ, 0 < e m) ∧
    ∀ m : ℕ, infinitePrefixDepth e m ≤ Critical.beattyIndex m

namespace IsInfiniteSurvivorExponentStream

/-- exponent は常に正。 -/
theorem exponent_pos
    {e : ℕ → ℕ}
    (S : IsInfiniteSurvivorExponentStream e)
    (m : ℕ) :
    0 < e m := S.1 m

/-- 任意 prefix depth は Beatty roof 以下。 -/
theorem prefixDepth_le_beatty
    {e : ℕ → ℕ}
    (S : IsInfiniteSurvivorExponentStream e)
    (m : ℕ) :
    infinitePrefixDepth e m ≤ Critical.beattyIndex m :=
  S.2 m

end IsInfiniteSurvivorExponentStream

/-- Beatty index は常に幅以上。 -/
theorem index_le_beattyIndex (m : ℕ) :
    m ≤ Critical.beattyIndex m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h := Critical.beattyIndex_lt_succ m
      omega

/-- normalized Beatty roof `beattyIndex m - m`。 -/
def survivorRoofExcess (m : ℕ) : ℕ :=
  Critical.beattyIndex m - m

/-- normalized roof の一歩差。 -/
def survivorSturmianStep (m : ℕ) : ℕ :=
  survivorRoofExcess (m + 1) - survivorRoofExcess m

/-- Beatty index は一歩で高々 `2` 増える。 -/
theorem beattyIndex_succ_le_add_two (m : ℕ) :
    Critical.beattyIndex (m + 1) ≤ Critical.beattyIndex m + 2 := by
  let q := Critical.beattyIndex m
  have hUpper := Critical.beattyIndex_upper m
  have hMul :
      3 ^ (m + 1) ≤ 2 ^ ((q + 2) + 1) := by
    rw [pow_succ]
    have h := Nat.mul_le_mul hUpper (by norm_num : 3 ≤ 4)
    calc
      3 ^ m * 3 ≤ 2 ^ (q + 1) * 4 := h
      _ = 2 ^ ((q + 2) + 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  have hMin := Critical.beattyIndex_le_of_upper hMul
  simpa [q] using hMin

/-- normalized roof excess は一歩で `0` または `1` だけ増える。 -/
theorem survivorSturmianStep_eq_zero_or_one (m : ℕ) :
    survivorSturmianStep m = 0 ∨ survivorSturmianStep m = 1 := by
  have hLo := Critical.beattyIndex_lt_succ m
  have hHi := beattyIndex_succ_le_add_two m
  have hm := index_le_beattyIndex m
  have hms := index_le_beattyIndex (m + 1)
  unfold survivorSturmianStep survivorRoofExcess
  omega

/-- Sturmian step は高々 `1`。 -/
theorem survivorSturmianStep_le_one (m : ℕ) :
    survivorSturmianStep m ≤ 1 := by
  rcases survivorSturmianStep_eq_zero_or_one m with h | h <;> omega

/-- 無限 survivor の roof defect。 -/
def infiniteSurvivorDefect
    (e : ℕ → ℕ)
    (m : ℕ) : ℕ :=
  Critical.beattyIndex m - infinitePrefixDepth e m

/-- survivor defect は roof gap そのもの。 -/
theorem beattyIndex_eq_prefixDepth_add_defect
    {e : ℕ → ℕ}
    (S : IsInfiniteSurvivorExponentStream e)
    (m : ℕ) :
    Critical.beattyIndex m =
      infinitePrefixDepth e m + infiniteSurvivorDefect e m := by
  unfold infiniteSurvivorDefect
  exact (Nat.add_sub_of_le (S.prefixDepth_le_beatty m)).symm

/-- normalized roof excess は `D_m-m + δ_m` に分解される。 -/
theorem survivorRoofExcess_eq_prefixExcess_add_defect
    {e : ℕ → ℕ}
    (S : IsInfiniteSurvivorExponentStream e)
    (m : ℕ) :
    survivorRoofExcess m =
      (infinitePrefixDepth e m - m) + infiniteSurvivorDefect e m := by
  have hDepthLower : m ≤ infinitePrefixDepth e m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [infinitePrefixDepth_succ]
        have he := S.exponent_pos m
        omega
  have hEq := beattyIndex_eq_prefixDepth_add_defect S m
  unfold survivorRoofExcess
  omega

/--
無限 survivor defect の exact Sturmian walk。

`e m - 1` は次 odd block が最低 exponent `1` からどれだけ余分に深いかを表す。
-/
theorem infiniteSurvivorDefect_succ
    {e : ℕ → ℕ}
    (S : IsInfiniteSurvivorExponentStream e)
    (m : ℕ) :
    infiniteSurvivorDefect e (m + 1) =
      infiniteSurvivorDefect e m + survivorSturmianStep m - (e m - 1) := by
  have hDm := S.prefixDepth_le_beatty m
  have hDn := S.prefixDepth_le_beatty (m + 1)
  have he := S.exponent_pos m
  have hLo := Critical.beattyIndex_lt_succ m
  have hHi := beattyIndex_succ_le_add_two m
  have hm := index_le_beattyIndex m
  have hms := index_le_beattyIndex (m + 1)
  unfold infiniteSurvivorDefect survivorSturmianStep survivorRoofExcess
  rw [infinitePrefixDepth_succ]
  omega

/-- defect walk から次 exponent を逆に読む形。 -/
theorem exponent_eq_one_add_step_add_defect_sub
    {e : ℕ → ℕ}
    (S : IsInfiniteSurvivorExponentStream e)
    (m : ℕ) :
    e m =
      1 + survivorSturmianStep m + infiniteSurvivorDefect e m -
        infiniteSurvivorDefect e (m + 1) := by
  have hRec := infiniteSurvivorDefect_succ S m
  have he := S.exponent_pos m
  -- Beatty roof 自体の一歩差を normalized step で書き直す。
  have hBeattyStep :
      Critical.beattyIndex (m + 1) =
        Critical.beattyIndex m + 1 + survivorSturmianStep m := by
    have hm := index_le_beattyIndex m
    have hm1 := index_le_beattyIndex (m + 1)
    have hInc := Critical.beattyIndex_lt_succ m
    unfold survivorSturmianStep survivorRoofExcess
    omega
  -- 次の prefix も roof 以下なので、recurrence の Nat.sub は切り捨てられない。
  have hSafe := S.prefixDepth_le_beatty m
  have hSafeNext := S.prefixDepth_le_beatty (m + 1)
  rw [infinitePrefixDepth_succ, hBeattyStep] at hSafeNext
  have hNoTrunc :
      e m - 1 ≤
        infiniteSurvivorDefect e m + survivorSturmianStep m := by
    unfold infiniteSurvivorDefect
    omega
  omega

end Bridge
end Collatz3
