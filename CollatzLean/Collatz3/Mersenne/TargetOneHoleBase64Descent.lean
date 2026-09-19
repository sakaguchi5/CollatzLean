import CollatzLean.Collatz3.Mersenne.TargetOneHolePrimitive
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: exceptional gcd-two branch の base-64 descent

`TargetOneHoleGcd` で残った唯一の non-primitive branch は

`n = 3`, `gcd(q,t) = 2`

である。この branch は独立な新しい residual ではない。

`q=2q'`, `t=2t'` と書き、

`G_(2m)(8) = G_2(8) G_m(8^2) = 9 G_m(64)`

を使うと、geometric equation 全体から 9 を exact に除ける。従って

`3^(k-2) + G_q'(64) = 2^r G_t'(64)`

となり、`gcd(q',t')=1` の primitive base-64 equation へ降りる。

最後に convenience theorem として、同じ equation を source width `6` の
`TargetOneHoleGeometricData` に再構成する。これにより descent 後も既存の
valuation / gcd / Beatty 層をそのまま再利用できる。
-/

namespace Collatz3
namespace Mersenne

/-- base 8 の長さ `2m` geometric sum は 9 を因子に持ち、base 64 へ降りる。 -/
theorem targetGeomSum_eight_two_mul
    (m : ℕ) :
    targetGeomSum 8 (2 * m) = 9 * targetGeomSum 64 m := by
  have hG2 : targetGeomSum 8 2 = 9 := by
    norm_num [targetGeomSum]
  have hPow : 8 ^ 2 = 64 := by norm_num
  calc
    targetGeomSum 8 (2 * m) =
        targetGeomSum 8 2 * targetGeomSum (8 ^ 2) m :=
      targetGeomSum_mul_length 8 2 m
    _ = 9 * targetGeomSum 64 m := by rw [hG2, hPow]

/--
`gcd(q,t)=2` なら半分にした lengths は互いに素。

この補題は gcd multiplication formula に依存せず、任意の共通因子 `d` に対し
`2d` が元の `q,t` の共通因子になることだけから示す。
-/
private theorem gcd_halves_eq_one
    {q t q' t' : ℕ}
    (hq : q = 2 * q')
    (ht : t = 2 * t')
    (hGcd : Nat.gcd q t = 2) :
    Nat.gcd q' t' = 1 := by
  let d : ℕ := Nat.gcd q' t'
  have hdq : d ∣ q' := by
    dsimp [d]
    exact Nat.gcd_dvd_left q' t'
  have hdt : d ∣ t' := by
    dsimp [d]
    exact Nat.gcd_dvd_right q' t'
  have h2dq : 2 * d ∣ q := by
    rw [hq]
    exact Nat.mul_dvd_mul_left 2 hdq
  have h2dt : 2 * d ∣ t := by
    rw [ht]
    exact Nat.mul_dvd_mul_left 2 hdt
  have h2dg : 2 * d ∣ Nat.gcd q t :=
    Nat.dvd_gcd h2dq h2dt
  rw [hGcd] at h2dg
  have hdOne : d ∣ 1 := by
    apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < (2 : ℕ))).mp
    simpa using h2dg
  have hd : d = 1 := Nat.dvd_one.mp hdOne
  simpa [d] using hd

/--
exceptional `n=3, gcd(q,t)=2` branch を primitive base-64 equation へ exact に降ろす。

`q<t` も半分にした後に保存される。
-/
theorem TargetOneHoleGeometricData.gcd_two_base64_descent
    {k r L b : ℕ}
    (h : TargetOneHoleGeometricData k 3 r L b)
    (hk : 2 ≤ k)
    (hqt : h.q < h.t)
    (hGcd : Nat.gcd h.q h.t = 2) :
    ∃ q' t' : ℕ,
      0 < q' ∧
      q' < t' ∧
      h.q = 2 * q' ∧
      h.t = 2 * t' ∧
      Nat.gcd q' t' = 1 ∧
      3 ^ (k - 2) + targetGeomSum 64 q' =
        2 ^ r * targetGeomSum 64 t' := by
  have hTwoQ : 2 ∣ h.q := by
    have hd := Nat.gcd_dvd_left h.q h.t
    rwa [hGcd] at hd
  have hTwoT : 2 ∣ h.t := by
    have hd := Nat.gcd_dvd_right h.q h.t
    rwa [hGcd] at hd
  let q' : ℕ := h.q / 2
  let t' : ℕ := h.t / 2
  have hqEq : h.q = 2 * q' := by
    dsimp [q']
    exact (Nat.mul_div_cancel' hTwoQ).symm
  have htEq : h.t = 2 * t' := by
    dsimp [t']
    exact (Nat.mul_div_cancel' hTwoT).symm
  have hqPos : 0 < q' := by
    have hqOriginalPos : 0 < h.q := h.q_pos
    rw [hqEq] at hqOriginalPos
    omega
  have hqt' : q' < t' := by
    rw [hqEq, htEq] at hqt
    omega
  have hGcd' : Nat.gcd q' t' = 1 :=
    gcd_halves_eq_one hqEq htEq hGcd
  have hEq := h.equation
  norm_num at hEq
  rw [hqEq, htEq, targetGeomSum_eight_two_mul, targetGeomSum_eight_two_mul] at hEq
  have hkEq : k = (k - 2) + 2 := by omega
  have hPowK : 3 ^ k = 9 * 3 ^ (k - 2) := by
    calc
      3 ^ k = 3 ^ ((k - 2) + 2) :=
        congrArg (fun e : ℕ => 3 ^ e) hkEq
      _ = 3 ^ (k - 2) * 3 ^ 2 := by rw [pow_add]
      _ = 9 * 3 ^ (k - 2) := by ring
  rw [hPowK] at hEq
  have hEqNine :
      9 * (3 ^ (k - 2) + targetGeomSum 64 q') =
        9 * (2 ^ r * targetGeomSum 64 t') := by
    calc
      9 * (3 ^ (k - 2) + targetGeomSum 64 q') =
          9 * 3 ^ (k - 2) + 9 * targetGeomSum 64 q' := by ring
      _ = 2 ^ r * (9 * targetGeomSum 64 t') := hEq
      _ = 9 * (2 ^ r * targetGeomSum 64 t') := by ring
  have hDesc :
      3 ^ (k - 2) + targetGeomSum 64 q' =
        2 ^ r * targetGeomSum 64 t' :=
    Nat.mul_left_cancel (by norm_num : 0 < (9 : ℕ)) hEqNine
  exact ⟨q', t', hqPos, hqt', hqEq, htEq, hGcd', hDesc⟩

/--
base-64 descent を既存 `TargetOneHoleGeometricData` の語彙へ戻す convenience theorem。

新しい source width は `6`。新しい auxiliary lengths は

`L' = 6 t'`, `b' = 6 q' - r`

と取る。これは actual target-one equation の存在を追加で主張するものではなく、
既存 geometric layer を再利用するための exact data reconstruction である。
-/
theorem TargetOneHoleGeometricData.gcd_two_base64_geometricData
    {k r L b : ℕ}
    (h : TargetOneHoleGeometricData k 3 r L b)
    (hk : 6 ≤ k)
    (hr : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hGcd : Nat.gcd h.q h.t = 2) :
    ∃ q' t' : ℕ,
      h.q = 2 * q' ∧
      h.t = 2 * t' ∧
      Nat.gcd q' t' = 1 ∧
      ∃ h' : TargetOneHoleGeometricData
          (k - 2) 6 r (6 * t') (6 * q' - r),
        h'.q = q' ∧
        h'.t = t' ∧
        h'.q < h'.t := by
  rcases h.gcd_two_base64_descent (by omega) hqt hGcd with
    ⟨q', t', hqPos, hqt', hqEq, htEq, hGcd', hDesc⟩
  have hrLe : r ≤ 2 := by
    rcases hr with rfl | rfl <;> omega
  have hrSixQ : r ≤ 6 * q' := by
    omega
  let h' : TargetOneHoleGeometricData
      (k - 2) 6 r (6 * t') (6 * q' - r) :=
    { q := q'
      t := t'
      q_pos := hqPos
      q_le_t := Nat.le_of_lt hqt'
      b_add_r_eq := by
        omega
      length_eq := by
        rfl
      equation := by
        norm_num
        exact hDesc }
  refine ⟨q', t', hqEq, htEq, hGcd', h', rfl, rfl, ?_⟩
  exact hqt'

end Mersenne
end Collatz3
