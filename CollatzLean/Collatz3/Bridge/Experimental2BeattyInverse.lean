import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog
import CollatzLean.Collatz3.Experimental2.MechanicalInverse

/-!
# Collatz3 Bridge: Beatty roof の離散逆と critical Sturmian height

`Experimental2.MechanicalInverse` では、full slope `σ` の lower mechanical roof

`β(n) = floor(n * σ)`

に対し、`1 ≤ σ` なら離散逆

`H(k) = min {m | k ≤ β(m)}`

が

`H(k) = ceil(k / σ)`

になることを generic に証明した。

このファイルではその定理を `Critical.beattyIndex` に特殊化する。
既存 bridge により Beatty roof の slope は exact に `log₂ 3` なので、
逆 slope は `log₃ 2` になる。

さらに正の時刻 `k` では

`2^k < 3^m  ↔  k ≤ beattyIndex m`

を power-form だけから証明する。したがって、旧 `SturmianHeight.criticalHeight` の

`Nat.find (∃ m, 2^k < 3^m)`

という定義は `k > 0` で generic mechanical inverse と exact に一致する。

注意: `k = 0` だけは旧 power-form critical height が `1`、
Beatty 離散逆が `0` なので一致しない。旧 `criticalPrefixHeight` が時刻 `0` を
`0` に正規化していたのは、まさにこの一点を吸収するためである。
-/

namespace Collatz3
namespace Bridge

/--
Beatty roof の full slope `log₂ 3` は `1` 以上。

`beattyIndex 1 = 1` と lower mechanical cell の下端だけから導く。
-/
theorem one_le_logb_two_three :
    (1 : ℝ) ≤ Real.logb 2 3 := by
  have h := (beattyIndex_isLowerMechanical_logb_two_three 1).1
  simpa [Critical.beattyIndex_one] using h

/--
Beatty roof の canonical 離散逆。

`k ≤ beattyIndex m` を初めて満たす最小 `m` である。
実体は `Experimental2.MechanicalInverse` の generic inverse そのもの。
-/
noncomputable def beattyInverseHeight (k : ℕ) : ℕ :=
  beattyIndex_isLowerMechanical_logb_two_three.inverse
    one_le_logb_two_three k

/-- Beatty 離散逆は threshold `k` に実際に到達する。 -/
theorem beattyInverseHeight_spec (k : ℕ) :
    k ≤ Critical.beattyIndex (beattyInverseHeight k) := by
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_spec
      one_le_logb_two_three k)

/-- Beatty 離散逆より前では threshold `k` にまだ到達しない。 -/
theorem beattyInverseHeight_min
    {k m : ℕ}
    (hm : m < beattyInverseHeight k) :
    Critical.beattyIndex m < k := by
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_min
      one_le_logb_two_three hm)

/-- threshold にすでに到達する任意の `m` は Beatty 離散逆以上。 -/
theorem beattyInverseHeight_le_of_reaches
    {k m : ℕ}
    (hReach : k ≤ Critical.beattyIndex m) :
    beattyInverseHeight k ≤ m := by
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_le_of_reaches
      one_le_logb_two_three hReach)

/-- Beatty 離散逆の closed form は `ceil(k / log₂ 3)`。 -/
theorem beattyInverseHeight_eq_natCeil_div_logb_two_three
    (k : ℕ) :
    beattyInverseHeight k =
      ⌈(k : ℝ) / Real.logb 2 3⌉₊ := by
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_eq_natCeil_div
      one_le_logb_two_three k)

/-- `log₂ 3` の逆数は exact に `log₃ 2`。 -/
theorem inv_logb_two_three_eq_logb_three_two :
    (Real.logb 2 3)⁻¹ = Real.logb 3 2 := by
  simpa using (Real.inv_logb (2 : ℝ) (3 : ℝ))

/--
Beatty 離散逆を old Sturmian slope の形へ書き換える。

`H(k) = ceil(k * log₃ 2)`。
-/
theorem beattyInverseHeight_eq_natCeil_mul_logb_three_two
    (k : ℕ) :
    beattyInverseHeight k =
      ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  rw [beattyInverseHeight_eq_natCeil_div_logb_two_three]
  rw [div_eq_mul_inv, inv_logb_two_three_eq_logb_three_two]

/-- Beatty 離散逆は threshold に対して単調。 -/
theorem beattyInverseHeight_mono
    {k l : ℕ}
    (hkl : k ≤ l) :
    beattyInverseHeight k ≤ beattyInverseHeight l := by
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_mono
      one_le_logb_two_three hkl)

/-- Beatty 離散逆は一 step で高々 `1` しか増えない。 -/
theorem beattyInverseHeight_succ_le (k : ℕ) :
    beattyInverseHeight (k + 1) ≤ beattyInverseHeight k + 1 := by
  simpa [beattyInverseHeight] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverse_succ_le_add_one
      one_le_logb_two_three k)

/-- Beatty 離散逆の一歩差分は `0` または `1`。 -/
theorem beattyInverseHeight_step_eq_zero_or_one (k : ℕ) :
    beattyInverseHeight (k + 1) - beattyInverseHeight k = 0 ∨
      beattyInverseHeight (k + 1) - beattyInverseHeight k = 1 := by
  simpa [beattyInverseHeight, Experimental2.IsLowerMechanicalRoof.inverseStep] using
    (beattyIndex_isLowerMechanical_logb_two_three.inverseStep_eq_zero_or_one
      one_le_logb_two_three k)

/--
正の時刻では power inequality と Beatty threshold は exact に同値。

`2^k < 3^m` なら、Beatty upper inequality
`3^m ≤ 2^(beattyIndex m + 1)` と合わせて `k ≤ beattyIndex m` が従う。
逆向きでは `k > 0` により `m > 0` が従い、
`2^beattyIndex(m) < 3^m` の strict lower inequality を使える。
-/
theorem twoPow_lt_threePow_iff_le_beattyIndex
    {k m : ℕ}
    (hk : 0 < k) :
    2 ^ k < 3 ^ m ↔ k ≤ Critical.beattyIndex m := by
  constructor
  · intro hPow
    by_contra hNot
    have hIndexLt : Critical.beattyIndex m < k := by omega
    have hExpLe : Critical.beattyIndex m + 1 ≤ k := by omega
    have hTwoLe :
        2 ^ (Critical.beattyIndex m + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hExpLe
    have hThreeLe : 3 ^ m ≤ 2 ^ k :=
      le_trans (Critical.beattyIndex_upper m) hTwoLe
    omega
  · intro hReach
    have hmPos : 0 < m := by
      by_contra hNot
      have hmZero : m = 0 := by omega
      subst m
      simp at hReach
      omega
    have hTwoLe :
        2 ^ k ≤ 2 ^ Critical.beattyIndex m :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hReach
    exact lt_of_le_of_lt hTwoLe
      (Critical.beattyIndex_lower_strict hmPos)

/--
power-form critical height の薄い specification。

`m` 自身で初めて `2^k < 3^m` が成立することだけを保存する。
-/
def IsPowerCriticalHeight (k m : ℕ) : Prop :=
  2 ^ k < 3 ^ m ∧
    ∀ r : ℕ, r < m → ¬ (2 ^ k < 3 ^ r)

/--
正の時刻では Beatty 離散逆が power-form critical height を実現する。
-/
theorem beattyInverseHeight_isPowerCriticalHeight
    {k : ℕ}
    (hk : 0 < k) :
    IsPowerCriticalHeight k (beattyInverseHeight k) := by
  constructor
  · exact (twoPow_lt_threePow_iff_le_beattyIndex hk).2
      (beattyInverseHeight_spec k)
  · intro r hr hPow
    have hReach :=
      (twoPow_lt_threePow_iff_le_beattyIndex hk).1 hPow
    have hLe := beattyInverseHeight_le_of_reaches hReach
    omega

/--
正の時刻では power-form critical height は一意で、Beatty 離散逆に等しい。

これは旧 `sturmianBoundaryAt_iff_eq_criticalHeight` のうち、
power 境界の一意性だけを generic inverse 側へ移した形でもある。
-/
theorem isPowerCriticalHeight_iff_eq_beattyInverseHeight
    {k m : ℕ}
    (hk : 0 < k) :
    IsPowerCriticalHeight k m ↔ m = beattyInverseHeight k := by
  constructor
  · intro H
    have hInvLe : beattyInverseHeight k ≤ m := by
      have hReach :=
        (twoPow_lt_threePow_iff_le_beattyIndex hk).1 H.1
      exact beattyInverseHeight_le_of_reaches hReach
    have hMLe : m ≤ beattyInverseHeight k := by
      by_contra hNot
      have hLt : beattyInverseHeight k < m := by omega
      exact H.2 (beattyInverseHeight k) hLt
        (beattyInverseHeight_isPowerCriticalHeight hk).1
    omega
  · intro hEq
    subst m
    exact beattyInverseHeight_isPowerCriticalHeight hk

/--
旧 `SturmianHeight.criticalHeight` の `Nat.find` 定義を直接回収する bridge。

`E : ∃ m, 2^k < 3^m` がどの存在証明であっても、`k > 0` なら
その `Nat.find E` は Beatty の generic mechanical inverse と一致する。

したがって凍結済み旧層を import しなくても、旧

`criticalHeight k := Nat.find (exists_expanding_height k)`

の数学的内容をそのまま再構成できる。
-/
theorem natFind_powerCriticalHeight_eq_beattyInverseHeight
    {k : ℕ}
    (hk : 0 < k)
    (E : ∃ m : ℕ, 2 ^ k < 3 ^ m) :
    Nat.find E = beattyInverseHeight k := by
  apply (isPowerCriticalHeight_iff_eq_beattyInverseHeight hk).1
  constructor
  · exact Nat.find_spec E
  · intro r hr hPow
    have hMin : Nat.find E ≤ r := Nat.find_min' E hPow
    omega

/--
旧 critical height の closed form を `Nat.find` の形のまま得る。

`k > 0` なら

`Nat.find (2^k < 3^m の存在証明) = ceil(k * log₃ 2)`。
-/
theorem natFind_powerCriticalHeight_eq_natCeil_mul_logb_three_two
    {k : ℕ}
    (hk : 0 < k)
    (E : ∃ m : ℕ, 2 ^ k < 3 ^ m) :
    Nat.find E = ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  rw [natFind_powerCriticalHeight_eq_beattyInverseHeight hk E]
  exact beattyInverseHeight_eq_natCeil_mul_logb_three_two k

end Bridge
end Collatz3
