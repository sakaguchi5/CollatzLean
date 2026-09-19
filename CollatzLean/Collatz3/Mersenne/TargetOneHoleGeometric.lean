import CollatzLean.Collatz3.Mersenne.OneHoleThreeTailLargeDepth
import CollatzLean.Collatz3.Mersenne.NoHoleMersenneQuotientProof
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: target-one の幾何和 reduction

large-depth target-one の残りを、元の五変数 exponential equation のまま扱わず、
Mersenne modulus `2^n-1` による剰余剛性から二つの幾何和の差へ落とす。

このファイルで追加する primitive definition は `TargetOneHoleGeometricData` だけに留める。
そのほかは既存 `TargetOneHoleEquation` から導く theorem とする。

主な結論は次の通り。

* `n ≥ 3`, `r ∈ {1,2}` なら `n ∣ b+r` と `n ∣ L`。
* `b+r=nq`, `L=nt` と書くと `1 ≤ q ≤ t`。
* `G_j(x)=1+x+...+x^(j-1)` として
  `3^k + G_q(2^n) = 2^r G_t(2^n)`。
* `q=t` は既存 no-hole 完全分類へ戻り、`k≥6` では不可能。
-/

namespace Collatz3
namespace Mersenne

open scoped BigOperators

/-- この層で使う通常の幾何和。 -/
def targetGeomSum (x t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, x ^ i

/-- `G_(a+b)(x) = G_a(x) + x^a G_b(x)`。 -/
theorem targetGeomSum_add (x a b : ℕ) :
    targetGeomSum x (a + b) =
      targetGeomSum x a + x ^ a * targetGeomSum x b := by
  unfold targetGeomSum
  rw [Finset.sum_range_add]
  congr 1
  simp_rw [pow_add]
  rw [Finset.mul_sum]

/-- 正の長さの幾何和は `1 + x * (...)` の形を持つ。 -/
theorem targetGeomSum_succ (x t : ℕ) :
    targetGeomSum x (t + 1) = x * targetGeomSum x t + 1 := by
  unfold targetGeomSum
  exact geom_sum_succ

/-- 長さの積に対する block factorization。 -/
theorem targetGeomSum_mul_length (x d m : ℕ) :
    targetGeomSum x (d * m) =
      targetGeomSum x d * targetGeomSum (x ^ d) m := by
  induction m with
  | zero =>
      simp [targetGeomSum]
  | succ m ih =>
      rw [Nat.mul_succ]
      rw [targetGeomSum_add, ih]
      unfold targetGeomSum
      rw [geom_sum_succ']
      rw [pow_mul]
      ring

/-- `d ∣ m` なら `G_d(x) ∣ G_m(x)`。 -/
theorem targetGeomSum_dvd_of_dvd (x : ℕ) {d m : ℕ} (h : d ∣ m) :
    targetGeomSum x d ∣ targetGeomSum x m := by
  rcases h with ⟨q, rfl⟩
  refine ⟨targetGeomSum (x ^ d) q, ?_⟩
  simpa [Nat.mul_comm] using targetGeomSum_mul_length x d q

/--
幾何和化した target-one data。

`equation` は subtraction を避けて
`3^k + G_q = 2^r G_t`
の加法形を canonical form とする。
-/
structure TargetOneHoleGeometricData
    (k n r L b : ℕ) : Type where
  q : ℕ
  t : ℕ
  q_pos : 0 < q
  q_le_t : q ≤ t
  b_add_r_eq : b + r = n * q
  length_eq : L = n * t
  equation :
    3 ^ k + targetGeomSum (2 ^ n) q =
      2 ^ r * targetGeomSum (2 ^ n) t

namespace TargetOneHoleGeometricData

/-- 加法形を通常の差の形へ戻す。 -/
theorem equation_sub
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b) :
    3 ^ k =
      2 ^ r * targetGeomSum (2 ^ n) h.t -
        targetGeomSum (2 ^ n) h.q := by
  have hle :
      targetGeomSum (2 ^ n) h.q ≤
        2 ^ r * targetGeomSum (2 ^ n) h.t := by
    calc
      targetGeomSum (2 ^ n) h.q ≤
          3 ^ k + targetGeomSum (2 ^ n) h.q := Nat.le_add_left _ _
      _ = 2 ^ r * targetGeomSum (2 ^ n) h.t := h.equation
  symm
  exact (Nat.sub_eq_iff_eq_add hle).2 h.equation.symm

/-- `b<L` と geometric data から `q<t` または `q=t`。 -/
theorem q_lt_or_eq_t
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b) :
    h.q < h.t ∨ h.q = h.t :=
  lt_or_eq_of_le h.q_le_t

end TargetOneHoleGeometricData

/-! ## Mersenne modulus 上の residue uniqueness -/

/-- `n≥4` で使う単純な半分冪下界。 -/
private theorem eight_le_twoPow_pred
    {n : ℕ} (hn : 4 ≤ n) :
    8 ≤ 2 ^ (n - 1) := by
  have hExp : 3 ≤ n - 1 := by omega
  have h := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExp
  norm_num at h ⊢
  exact h

/--
`n = 3` の有限ケース。

`A,B < 3`, `r = 1 or 2` の全組合せを直接閉じる。
-/
private theorem mersenneResidue_pair_unique_n3
    {r A B : ℕ}
    (hr : r = 1 ∨ r = 2)
    (hA : A < 3)
    (hB : B < 3)
    (hEq :
      (2 : ZMod (2 ^ 3 - 1)) ^ A + 1 =
        (2 : ZMod (2 ^ 3 - 1)) ^ B +
          (2 : ZMod (2 ^ 3 - 1)) ^ r) :
    A = r ∧ B = 0 := by
  have hAcases : A = 0 ∨ A = 1 ∨ A = 2 := by
    omega
  have hBcases : B = 0 ∨ B = 1 ∨ B = 2 := by
    omega
  rcases hr with rfl | rfl <;>
    rcases hAcases with rfl | rfl | rfl <;>
    rcases hBcases with rfl | rfl | rfl
  all_goals
    first
    | exact ⟨rfl, rfl⟩
    | exfalso
      revert hEq
      decide

/--
`n ≥ 4` では両辺が `2^n - 1` より小さいので、
ZMod 上の等式を通常の自然数等式へ持ち上げられる。
-/
private theorem mersenneResidue_pair_eq_nat
    {n r A B : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hA : A < n)
    (hB : B < n)
    (hEq :
      (2 : ZMod (2 ^ n - 1)) ^ A + 1 =
        (2 : ZMod (2 ^ n - 1)) ^ B +
          (2 : ZMod (2 ^ n - 1)) ^ r) :
    2 ^ A + 1 = 2 ^ B + 2 ^ r := by
  have hPowA : 2 ^ A ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ))
      (by omega)
  have hPowB : 2 ^ B ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ))
      (by omega)
  have hEight : 8 ≤ 2 ^ (n - 1) :=
    eight_le_twoPow_pred hn4
  have hPowN : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    simp
  have hPowR : 2 ^ r ≤ 4 := by
    rcases hr with rfl | rfl <;>
      norm_num
  have hLeftLt :
      2 ^ A + 1 < 2 ^ n - 1 := by
    rw [hPowN]
    omega
  have hRightLt :
      2 ^ B + 2 ^ r < 2 ^ n - 1 := by
    rw [hPowN]
    omega
  have hCastEq :
      ((2 ^ A + 1 : ℕ) : ZMod (2 ^ n - 1)) =
        ((2 ^ B + 2 ^ r : ℕ) : ZMod (2 ^ n - 1)) := by
    simpa using hEq
  have hNatEq :=
    (ZMod.natCast_eq_natCast_iff'
      (2 ^ A + 1)
      (2 ^ B + 2 ^ r)
      (2 ^ n - 1)).mp hCastEq
  rw [
    Nat.mod_eq_of_lt hLeftLt,
    Nat.mod_eq_of_lt hRightLt
  ] at hNatEq
  exact hNatEq


/--
純粋な 2 冪の一意性。

`r = 1 or 2` かつ

`2^A + 1 = 2^B + 2^r`

なら `B = 0` であり、その後 `A = r` が従う。
-/
private theorem twoPow_pair_unique
    {r A B : ℕ}
    (hr : r = 1 ∨ r = 2)
    (hEq : 2 ^ A + 1 = 2 ^ B + 2 ^ r) :
    A = r ∧ B = 0 := by
  have hApos : 0 < A := by
    by_contra hNot
    have hA0 : A = 0 := by
      omega
    subst A
    have hOneLe : 1 ≤ 2 ^ B := by
      have hPos : 0 < 2 ^ B :=
        Nat.pow_pos (by norm_num)
      omega
    rcases hr with rfl | rfl <;>
      norm_num at hEq
  have hBzero : B = 0 := by
    by_contra hBne
    have hBpos : 0 < B := by
      omega
    have hRpos : 0 < r := by
      rcases hr with rfl | rfl <;>
        norm_num
    -- `A,B,r > 0` なら三つの冪はすべて偶数。
    -- しかし左辺は `even + 1` なので奇数となり矛盾。
    rcases dvd_pow_self 2 (Nat.ne_of_gt hApos) with
      ⟨u, hu⟩
    rcases dvd_pow_self 2 (Nat.ne_of_gt hBpos) with
      ⟨v, hv⟩
    rcases dvd_pow_self 2 (Nat.ne_of_gt hRpos) with
      ⟨w, hw⟩
    omega
  subst B
  have hPowEq : 2 ^ A = 2 ^ r := by
    norm_num at hEq
    omega
  have hAr : A = r :=
    Nat.pow_right_injective
      (by norm_num : 2 ≤ (2 : ℕ))
      hPowEq
  exact ⟨hAr, rfl⟩


/--
`mod (2^n-1)` で

`2^A + 1 = 2^B + 2^r`,

`A,B<n`, `n≥3`, `r=1 or 2` なら、必ず `A=r`, `B=0`。
-/
private theorem mersenneResidue_pair_unique
    {n r A B : ℕ}
    (hn : 3 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hA : A < n)
    (hB : B < n)
    (hEq :
      (2 : ZMod (2 ^ n - 1)) ^ A + 1 =
        (2 : ZMod (2 ^ n - 1)) ^ B +
          (2 : ZMod (2 ^ n - 1)) ^ r) :
    A = r ∧ B = 0 := by
  by_cases hn3 : n = 3
  · subst n
    exact mersenneResidue_pair_unique_n3
      hr hA hB hEq
  · have hn4 : 4 ≤ n := by
      omega
    have hNatEq :
        2 ^ A + 1 = 2 ^ B + 2 ^ r :=
      mersenneResidue_pair_eq_nat
        hn4 hr hA hB hEq
    exact twoPow_pair_unique hr hNatEq

/-- `2` は `mod (2^n-1)` で period `n` を持つ。 -/
private theorem twoPow_period_mersenne
    (n : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ n = 1 := by
  have hPos : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  have hEq : 2 ^ n = (2 ^ n - 1) + 1 := by omega
  have hCast :
      ((2 ^ n : ℕ) : ZMod (2 ^ n - 1)) = 1 := by
    rw [hEq, Nat.cast_add, ZMod.natCast_self]
    simp
  simpa [Nat.cast_pow] using hCast

/--
残存 target-one では Mersenne modulus が `L` と `b+r` の位相を同時に固定する。
-/
theorem TargetOneHoleEquation.mersenne_divisibility
    {k n r L b : ℕ}
    (hn : 3 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hEq : TargetOneHoleEquation k n r L b) :
    n ∣ b + r ∧ n ∣ L := by
  let M : ℕ := 2 ^ n - 1
  have hPeriod : (2 : ZMod M) ^ n = 1 := by
    simpa [M] using twoPow_period_mersenne n
  have hMod := hEq.to_mod M
  unfold TargetOneHoleModEquation at hMod
  have hMod0 :
      (0 : ZMod M) =
        (2 : ZMod M) ^ r *
          ((2 : ZMod M) ^ L - 1 - (2 : ZMod M) ^ b) + 1 := by
    simpa [hPeriod] using hMod
  have hCore :
      (2 : ZMod M) ^ (L + r) + 1 =
        (2 : ZMod M) ^ (b + r) + (2 : ZMod M) ^ r := by
    rw [pow_add, pow_add]
    linear_combination -hMod0
  let A : ℕ := (L + r) % n
  let B : ℕ := (b + r) % n
  have hAred :=
    pow_eq_pow_mod_of_pow_eq_one
      (2 : ZMod M) (p := n) (e := L + r) hPeriod
  have hBred :=
    pow_eq_pow_mod_of_pow_eq_one
      (2 : ZMod M) (p := n) (e := b + r) hPeriod
  rw [hAred, hBred] at hCore
  have hnPos : 0 < n := by omega
  have hAlt : A < n := by
    dsimp [A]
    exact Nat.mod_lt _ hnPos
  have hBlt : B < n := by
    dsimp [B]
    exact Nat.mod_lt _ hnPos
  have hUnique :=
    mersenneResidue_pair_unique hn hr hAlt hBlt (by simpa [A, B, M] using hCore)
  rcases hUnique with ⟨hAeq, hBeq⟩
  have hrlt : r < n := by
    rcases hr with rfl | rfl <;> omega
  have hBR : n ∣ b + r := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    simpa [B] using hBeq
  have hLRMod : L + r ≡ r [MOD n] := by
    change (L + r) % n = r % n
    simpa [A, Nat.mod_eq_of_lt hrlt] using hAeq
  have hLMod : L ≡ 0 [MOD n] := by
    apply Nat.ModEq.add_right_cancel' r
    simpa using hLRMod
  exact ⟨hBR, Nat.modEq_zero_iff_dvd.mp hLMod⟩

/-! ## exact geometric data -/

/--
元の target-one equation と二つの divisibility から geometric data を作る。
-/
def TargetOneHoleEquation.exists_geometricData
    {k n r L b : ℕ}
    (hn : 3 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hb : 0 < b)
    (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    TargetOneHoleGeometricData k n r L b := by
  have hDiv := hEq.mersenne_divisibility hn hr
  have hBR : n ∣ b + r := hDiv.1
  have hL : n ∣ L := hDiv.2
  let q : ℕ := (b + r) / n
  let t : ℕ := L / n
  have hnPos : 0 < n := by omega
  have hrlt : r < n := by
    have hrLe : r ≤ 2 := by
      rcases hr with hr1 | hr2 <;> omega
    omega
  have hq : b + r = n * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hBR).symm
  have ht : L = n * t := by
    dsimp [t]
    exact (Nat.mul_div_cancel' hL).symm
  have hqPos : 0 < q := by
    by_contra hNot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hq0, Nat.mul_zero] at hq
    omega
  have hqLe : q ≤ t := by
    have hlt : b + r < L + n := by omega
    rw [hq, ht] at hlt
    have hlt' : n * q < n * (t + 1) := by
      simpa [Nat.mul_succ] using hlt
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_left hnPos).mp hlt')
  refine ⟨q, t, hqPos, hqLe, hq, ht, ?_⟩
  let x : ℕ := 2 ^ n
  have hxTwo : 2 ≤ x := by
    dsimp [x]
    have h := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ n)
    norm_num at h ⊢
    exact h
  have hGeomTNat :
      targetGeomSum x t * (x - 1) = x ^ t - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le (by omega : 1 ≤ x) t
  have hGeomQNat :
      targetGeomSum x q * (x - 1) = x ^ q - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le (by omega : 1 ≤ x) q
  have hxPos : 0 < x := by omega
  have hxOne : 1 ≤ x := by omega
  have hxtOne : 1 ≤ x ^ t := Nat.one_le_pow t x hxPos
  have hxqOne : 1 ≤ x ^ q := Nat.one_le_pow q x hxPos
  have hGeomT :
      ((targetGeomSum x t : ℕ) : ℤ) * ((x : ℤ) - 1) =
        (x : ℤ) ^ t - 1 := by
    have hCast := congrArg (fun z : ℕ => (z : ℤ)) hGeomTNat
    simp only [Nat.cast_mul, Nat.cast_sub hxOne, Nat.cast_one,
      Nat.cast_pow, Nat.cast_sub hxtOne] at hCast
    exact hCast
  have hGeomQ :
      ((targetGeomSum x q : ℕ) : ℤ) * ((x : ℤ) - 1) =
        (x : ℤ) ^ q - 1 := by
    have hCast := congrArg (fun z : ℕ => (z : ℤ)) hGeomQNat
    simp only [Nat.cast_mul, Nat.cast_sub hxOne, Nat.cast_one,
      Nat.cast_pow, Nat.cast_sub hxqOne] at hCast
    exact hCast
  have hEqZ := hEq
  unfold TargetOneHoleEquation at hEqZ
  have hPowL : (2 : ℤ) ^ L = (x : ℤ) ^ t := by
    rw [ht]
    dsimp [x]
    rw [pow_mul]
  have hPowBR : (2 : ℤ) ^ r * (2 : ℤ) ^ b = (x : ℤ) ^ q := by
    calc
      (2 : ℤ) ^ r * (2 : ℤ) ^ b = (2 : ℤ) ^ (r + b) := by rw [pow_add]
      _ = (2 : ℤ) ^ (b + r) := by rw [Nat.add_comm]
      _ = (2 : ℤ) ^ (n * q) := by rw [hq]
      _ = ((2 : ℤ) ^ n) ^ q := by rw [pow_mul]
      _ = (x : ℤ) ^ q := by rfl
  change
      (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ b) + 1 at hEqZ
  rw [hPowL] at hEqZ
  have hEqExpanded :
      (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r * ((x : ℤ) ^ t - 1) - (x : ℤ) ^ q + 1 := by
    rw [← hPowBR]
    linear_combination hEqZ
  have hMain :
      ((3 : ℤ) ^ k + (targetGeomSum x q : ℕ)) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r * (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) := by
    rw [add_mul, hGeomQ, mul_assoc, hGeomT]
    linear_combination hEqExpanded
  have hxNe : (x : ℤ) - 1 ≠ 0 := by
    have hxGt : (1 : ℤ) < x := by exact_mod_cast hxTwo
    omega
  have hCancel :
      ((3 : ℤ) ^ k + (targetGeomSum x q : ℕ)) =
        (2 : ℤ) ^ r * (targetGeomSum x t : ℕ) := by
    apply mul_right_cancel₀ hxNe
    simpa [mul_assoc] using hMain
  exact_mod_cast hCancel

/--
large-depth target-one から geometric data を直接取り出す convenience theorem。
-/
def TargetOneHoleEquation.exists_geometricData_of_largeDepth
    {k n r L b : ℕ}
    (hk : 6 ≤ k)
    (hn : 0 < n)
    (hr : 0 < r)
    (hb : 0 < b)
    (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    TargetOneHoleGeometricData k n r L b := by
  have hShape := hEq.largeDepth_shape hk hn hr hb hbL
  have hn3 : 3 ≤ n := hShape.1
  have hr12 : r = 1 ∨ r = 2 := by
    rcases hShape.2 with hEven | hOdd
    · exact Or.inl hEven.2
    · exact Or.inr hOdd.2
  exact hEq.exists_geometricData hn3 hr12 hb hbL

/-! ## q=t branch は no-hole へ戻る -/

/-- geometric sum が 3 冪なら no-hole equation を構成できる。 -/
theorem noHole_of_targetGeomSum_eq_threePow
    {a n t : ℕ}
    (hn : 2 ≤ n)
    (ht : 0 < t)
    (hSum : targetGeomSum (2 ^ n) t = 3 ^ a) :
    NoHoleEquation a n 1 (n * t - 1) := by
  let x : ℕ := 2 ^ n
  have hx : 1 ≤ x := by
    have hxPos : 0 < x := by
      dsimp [x]
      exact Nat.pow_pos (by norm_num)
    omega
  have hGeomNat :
      targetGeomSum x t * (x - 1) = x ^ t - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le hx t
  have hntPos : 0 < n * t := Nat.mul_pos (by omega) ht
  unfold NoHoleEquation
  have hPow : (x : ℤ) ^ t = (2 : ℤ) ^ (n * t) := by
    dsimp [x]
    rw [pow_mul]
  have hPowPos : 0 < x ^ t := Nat.pow_pos (by omega)
  have hPowOne : 1 ≤ x ^ t := by omega
  have hCastGeom :
      ((targetGeomSum x t : ℕ) : ℤ) * ((x : ℤ) - 1) =
        (x : ℤ) ^ t - 1 := by
    calc
      ((targetGeomSum x t : ℕ) : ℤ) * ((x : ℤ) - 1)
          = ((targetGeomSum x t * (x - 1) : ℕ) : ℤ) := by
              rw [Nat.cast_mul, Nat.cast_sub hx, Nat.cast_one]
      _ = ((x ^ t - 1 : ℕ) : ℤ) := by rw [hGeomNat]
      _ = (x : ℤ) ^ t - 1 := by
              rw [Nat.cast_sub hPowOne, Nat.cast_pow, Nat.cast_one]
  rw [hSum] at hCastGeom
  rw [hPow] at hCastGeom
  rw [show n * t = (n * t - 1) + 1 by omega, pow_succ] at hCastGeom
  dsimp [x] at hCastGeom
  linear_combination hCastGeom

/--
`q=t` なら target-one は no-hole 完全分類へ戻るため、`k≥6` では不可能。
-/
theorem TargetOneHoleEquation.largeDepth_geometric_q_eq_t_impossible
    {k n r L b : ℕ}
    (hk : 6 ≤ k)
    (hn : 3 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hEq : TargetOneHoleEquation k n r L b)
    (hData : TargetOneHoleGeometricData k n r L b)
    (hqt : hData.q = hData.t) :
    False := by
  have htPos : 0 < hData.t := by
    rw [← hqt]
    exact hData.q_pos
  have hNoHoleLPos : 0 < n * hData.t - 1 := by
    have hnLe : n ≤ n * hData.t := Nat.le_mul_of_pos_right n htPos
    omega
  rcases hr with rfl | rfl
  · have hSum :
        targetGeomSum (2 ^ n) hData.t = 3 ^ k := by
      have h := hData.equation
      rw [hqt] at h
      norm_num at h
      omega
    have hNo :=
      noHole_of_targetGeomSum_eq_threePow (a := k) (n := n)
        (t := hData.t) (by omega) htPos hSum
    have hkLe :=
      NoHoleCompleteClassification.depth_le_two
        noHoleCompleteClassification
        (by omega) (by omega) (by norm_num)
        hNoHoleLPos
        hNo
    omega
  · have hEqData := hData.equation
    rw [hqt] at hEqData
    norm_num at hEqData
    have hkPos : 0 < k := by omega
    have hkDecomp : k = (k - 1) + 1 := by omega
    have hPowK : 3 ^ k = 3 ^ (k - 1) * 3 := by
      calc
        3 ^ k = 3 ^ ((k - 1) + 1) :=
          congrArg (fun e : ℕ => 3 ^ e) hkDecomp
        _ = 3 ^ (k - 1) * 3 := by rw [pow_succ]
    have hSum :
        targetGeomSum (2 ^ n) hData.t = 3 ^ (k - 1) := by
      rw [hPowK] at hEqData
      nlinarith
    have hNo :=
      noHole_of_targetGeomSum_eq_threePow (a := k - 1) (n := n)
        (t := hData.t) (by omega) htPos hSum
    have hkPredLe :=
      NoHoleCompleteClassification.depth_le_two
        noHoleCompleteClassification
        (by omega) (by omega) (by norm_num)
        hNoHoleLPos
        hNo
    omega

/--
large-depth target-one の geometric data では `q=t` branch が消えるため、必ず `q<t`。
-/
theorem TargetOneHoleEquation.largeDepth_geometric_q_lt
    {k n r L b : ℕ}
    (hk : 6 ≤ k)
    (hn : 3 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hEq : TargetOneHoleEquation k n r L b)
    (hData : TargetOneHoleGeometricData k n r L b) :
    hData.q < hData.t := by
  rcases hData.q_lt_or_eq_t with hlt | heq
  · exact hlt
  · exact (TargetOneHoleEquation.largeDepth_geometric_q_eq_t_impossible
      hk hn hr hEq hData heq).elim

/--
large-depth target-one から、後段が直接使える `q<t` geometric data を取り出す。
-/
theorem TargetOneHoleEquation.exists_geometricData_q_lt_of_largeDepth
    {k n r L b : ℕ}
    (hk : 6 ≤ k)
    (hn : 0 < n)
    (hr : 0 < r)
    (hb : 0 < b)
    (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    ∃ hData : TargetOneHoleGeometricData k n r L b,
      hData.q < hData.t := by
  rcases hEq.largeDepth_shape hk hn hr hb hbL with
    ⟨hn3, hExit⟩
  have hr12 : r = 1 ∨ r = 2 := by
    rcases hExit with ⟨_, hr1⟩ | ⟨_, hr2⟩
    · exact Or.inl hr1
    · exact Or.inr hr2
  let hData : TargetOneHoleGeometricData k n r L b :=
    hEq.exists_geometricData hn3 hr12 hb hbL
  refine ⟨hData, ?_⟩
  exact TargetOneHoleEquation.largeDepth_geometric_q_lt
    hk hn3 hr12 hEq hData

end Mersenne
end Collatz3
