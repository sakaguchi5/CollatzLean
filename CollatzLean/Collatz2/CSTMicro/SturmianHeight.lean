import CollatzLean.Collatz2.CSTMicro.FirstPassagePreservation

/-!
# General CST: exact critical Sturmian height

実数 `log₃ 2` を Lean に直接導入せず、

  2^k < 3^m

を初めて満たす最小 `m` を時刻 `k` の critical height とする。
`k > 0` では数学的に `ceil (k * log₃ 2)` と同じ量である。

このファイルでは

* critical height の存在・最小性
* `SturmianBoundaryAt` との一意同定
* first-passage prefix は critical height 以上
* critical height は一 step で高々 1 だけ増える

を純自然数・冪だけで証明する。
-/

namespace Collatz2
namespace CSTMicro

/-- 任意の時刻には expanding height が存在する。 -/
theorem exists_expanding_height (k : ℕ) :
    ∃ m : ℕ, 2 ^ k < 3 ^ m := by
  have hle : 2 ^ k ≤ 3 ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ]
        exact Nat.mul_le_mul ih (by omega)
  refine ⟨k + 1, ?_⟩
  rw [pow_succ]
  have hpos : 0 < 3 ^ k := Nat.pow_pos (by omega)
  nlinarith

/-- `2^k < 3^m` を初めて満たす最小 height。 -/
noncomputable def criticalHeight (k : ℕ) : ℕ :=
  Nat.find (exists_expanding_height k)

/-- critical height 自身は expanding。 -/
theorem criticalHeight_expanding (k : ℕ) :
    2 ^ k < 3 ^ criticalHeight k := by
  exact Nat.find_spec (exists_expanding_height k)

/-- critical height より下では expanding ではない。 -/
theorem not_expanding_below_criticalHeight
    (k r : ℕ)
    (hr : r < criticalHeight k) :
    ¬ (2 ^ k < 3 ^ r) := by
  intro h
  have hmin : criticalHeight k ≤ r :=
    Nat.find_min' (exists_expanding_height k) h
  omega

/-- critical height は既存 `SturmianBoundaryAt` そのもの。 -/
theorem criticalHeight_sturmianBoundaryAt (k : ℕ) :
    FirstPassagePath.SturmianBoundaryAt k (criticalHeight k) := by
  constructor
  · exact criticalHeight_expanding k
  · intro r hr
    exact not_expanding_below_criticalHeight k r hr

/-- `SturmianBoundaryAt` の height は一意で、criticalHeight に等しい。 -/
theorem sturmianBoundaryAt_iff_eq_criticalHeight
    (k m : ℕ) :
    FirstPassagePath.SturmianBoundaryAt k m ↔
      m = criticalHeight k := by
  constructor
  · intro h
    have hcrit_le : criticalHeight k ≤ m :=
      Nat.find_min' (exists_expanding_height k) h.1
    have hm_le : m ≤ criticalHeight k := by
      by_contra hnot
      have hlt : criticalHeight k < m := by omega
      exact h.2 (criticalHeight k) hlt (criticalHeight_expanding k)
    omega
  · intro h
    subst m
    exact criticalHeight_sturmianBoundaryAt k

/-- expanding している任意の height は critical height 以上。 -/
theorem criticalHeight_le_of_expanding
    {k m : ℕ}
    (h : 2 ^ k < 3 ^ m) :
    criticalHeight k ≤ m := by
  exact Nat.find_min' (exists_expanding_height k) h

/-- critical height は時刻について単調。 -/
theorem criticalHeight_mono (k : ℕ) :
    criticalHeight k ≤ criticalHeight (k + 1) := by
  have hnext := criticalHeight_expanding (k + 1)
  have hpow : 2 ^ k < 3 ^ criticalHeight (k + 1) := by
    have htwo : 2 ^ k ≤ 2 ^ (k + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ k := Nat.pow_pos (by omega)
      nlinarith
    exact lt_of_le_of_lt htwo hnext
  exact criticalHeight_le_of_expanding hpow

/-- critical height は一 step で高々 1 だけ増える。 -/
theorem criticalHeight_succ_le (k : ℕ) :
    criticalHeight (k + 1) ≤ criticalHeight k + 1 := by
  have hk := criticalHeight_expanding k
  have hnext :
      2 ^ (k + 1) < 3 ^ (criticalHeight k + 1) := by
    rw [pow_succ, pow_succ]
    have hthree : 0 < 3 ^ criticalHeight k := Nat.pow_pos (by omega)
    nlinarith
  exact criticalHeight_le_of_expanding hnext

/-- mechanical prefix 用の height。時刻 0 だけ 0 に正規化する。 -/
noncomputable def criticalPrefixHeight : ℕ → ℕ
  | 0 => 0
  | k + 1 => criticalHeight (k + 1)

@[simp] theorem criticalPrefixHeight_zero :
    criticalPrefixHeight 0 = 0 := rfl

@[simp] theorem criticalPrefixHeight_succ (k : ℕ) :
    criticalPrefixHeight (k + 1) = criticalHeight (k + 1) := rfl

/-- 時刻 1 の critical height は 1。 -/
theorem criticalHeight_one : criticalHeight 1 = 1 := by
  have hBoundary : FirstPassagePath.SturmianBoundaryAt 1 1 := by
    constructor
    · norm_num
    · intro r hr
      have hr0 : r = 0 := by omega
      subst r
      norm_num
  exact
    ((sturmianBoundaryAt_iff_eq_criticalHeight 1 1).1 hBoundary).symm

/-- 正規化した mechanical height も単調。 -/
theorem criticalPrefixHeight_mono (k : ℕ) :
    criticalPrefixHeight k ≤ criticalPrefixHeight (k + 1) := by
  cases k with
  | zero =>
      simp [criticalHeight_one]
  | succ k =>
      simpa using criticalHeight_mono (k + 1)

/-- 正規化した mechanical height も一 step で高々 1 増える。 -/
theorem criticalPrefixHeight_succ_le (k : ℕ) :
    criticalPrefixHeight (k + 1) ≤ criticalPrefixHeight k + 1 := by
  cases k with
  | zero =>
      simp [criticalHeight_one]
  | succ k =>
      simpa using criticalHeight_succ_le (k + 1)

namespace FirstPassagePath

/-- first-passage proper prefix は critical Sturmian height 以上にある。 -/
theorem criticalHeight_le_prefixOddCount
    (P : FirstPassagePath)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < P.length) :
    criticalHeight k ≤ prefixOddCount P.word k := by
  have hExp := P.proper_expanding k hkPos hkLt
  unfold CoefficientExpandingAt at hExp
  exact CSTMicro.criticalHeight_le_of_expanding hExp

end FirstPassagePath

end CSTMicro
end Collatz2
