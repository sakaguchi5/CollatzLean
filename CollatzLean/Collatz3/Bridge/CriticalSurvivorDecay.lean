import CollatzLean.Collatz3.Bridge.CriticalFirstCrossingKraft
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: survivor mass の指数減衰

first-crossing Kraft 恒等式を無限和へ送るには、残余の survivor mass が 0 へ落ちることを
示す必要がある。

ここでは対数や実数の大偏差論を使わず、composition の有限重みだけで減衰を得る。

physical depth `n` の composition `c` に

`2^(c.length - 1)`

という整数重みを付ける。positive depth では末尾 bit `0` は block 数を保存し、
末尾 bit `1` は block 数を 1 増やすので、全 composition の重み総和は一段ごとに
正確に 3 倍になる。したがって

`sum_c 2^(c.length - 1) = 3^(n - 1)`。

一方 depth `5r` の survivor は terminal 条件 `2^(5r) ≤ 3^m` を満たす。
`3^3 = 27 < 32 = 2^5` なので、`r > 0` なら必ず `3r < m`。
よって survivor 一個あたりの重みは少なくとも `2^(3r)` である。

これらを合わせると

`2^(3r) * S_(5r) ≤ 3^(5r-1)`

を得る。実数へ移すと、十分な形として

`S_(5r) / 2^(5r) ≤ (243/256)^r`

が従い、右辺は幾何級数的に 0 へ収束する。
-/

namespace Collatz3
namespace Bridge

open scoped BigOperators
open scoped Topology
open Filter

/-- depth `n` の全 parity compositions に対する整数重み総和。 -/
noncomputable def parityCompositionWeightSum (n : ℕ) : ℕ :=
  ∑ c : ParityComposition n, 2 ^ (c.length - 1)

/-- positive depth の composition は block 数も positive。 -/
theorem parityComposition_length_pos
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    0 < c.length := by
  exact c.length_pos_iff.mpr hn

/-- depth `1` の全重み総和は `1`。 -/
theorem parityCompositionWeightSum_one :
    parityCompositionWeightSum 1 = 1 := by
  classical
  unfold parityCompositionWeightSum
  have hlen : ∀ c : ParityComposition 1, c.length = 1 := by
    intro c
    have hp : 0 < c.length := parityComposition_length_pos (by omega) c
    have hle : c.length ≤ 1 := c.length_le
    omega
  simp_rw [hlen]
  simp [parityComposition_card]

/--
末尾 bit の二分岐により、全 composition の重み総和は一段ごとに正確に 3 倍になる。
-/
theorem parityCompositionWeightSum_succ
    {n : ℕ}
    (hn : 0 < n) :
    parityCompositionWeightSum (n + 1) =
      3 * parityCompositionWeightSum n := by
  classical
  unfold parityCompositionWeightSum
  calc
    (∑ c : ParityComposition (n + 1), 2 ^ (c.length - 1)) =
        ∑ p : ParityComposition n × Bool,
          2 ^ (((parityCompositionBranchEquiv n hn) p).length - 1) := by
      symm
      exact
        Fintype.sum_equiv
          (parityCompositionBranchEquiv n hn)
          (fun p : ParityComposition n × Bool =>
            2 ^ (((parityCompositionBranchEquiv n hn) p).length - 1))
          (fun c : ParityComposition (n + 1) => 2 ^ (c.length - 1))
          (fun _ => rfl)
    _ = ∑ c : ParityComposition n,
          (2 ^ (c.length - 1) + 2 ^ c.length) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c hc
      have hlen : 0 < c.length := parityComposition_length_pos hn c
      simp only [parityCompositionBranchEquiv]
      simp [parityAppendZero_length, parityAppendOne_length]
      omega
    _ = ∑ c : ParityComposition n, 3 * 2 ^ (c.length - 1) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hlen : 0 < c.length := parityComposition_length_pos hn c
      have hpow :
          2 ^ c.length = 2 ^ (c.length - 1) * 2 := by
        have hsplit :
            (c.length - 1) + 1 = c.length := by
          omega
        calc
          2 ^ c.length
              = 2 ^ ((c.length - 1) + 1) := by
                  exact congrArg (fun k : ℕ => 2 ^ k) hsplit.symm
          _ = 2 ^ (c.length - 1) * 2 := by
                  rw [pow_succ]
      rw [hpow]
      ring
    _ = 3 * ∑ c : ParityComposition n, 2 ^ (c.length - 1) := by
      rw [Finset.mul_sum]

/-- positive depth `n` の全重み総和は正確に `3^(n-1)`。 -/
theorem parityCompositionWeightSum_eq_threePow
    {n : ℕ}
    (hn : 0 < n) :
    parityCompositionWeightSum n = 3 ^ (n - 1) := by
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction r with
  | zero =>
      simpa using parityCompositionWeightSum_one
  | succ r ih =>
      have hstep :=
        parityCompositionWeightSum_succ
          (n := r + 1) (by omega)
      rw [hstep, ih (by omega)]
      have h₁ : r.succ - 1 = r := by omega
      have h₂ : (r + 1).succ - 1 = r + 1 := by omega
      rw [h₁, h₂, pow_succ]
      simp [Nat.mul_comm]

/-- survivor 部分だけに制限した同じ整数重み。 -/
noncomputable def survivorParityWeightSum (n : ℕ) : ℕ := by
  classical
  letI : Fintype (SurvivorParityCode n) := Fintype.ofFinite _
  exact
    ∑ c : SurvivorParityCode n,
      2 ^ (c.1.length - 1)

/-- survivor の重み総和は全 composition の重み総和以下。 -/
theorem survivorParityWeightSum_le_all
    (n : ℕ) :
    survivorParityWeightSum n ≤ parityCompositionWeightSum n := by
  classical
  unfold survivorParityWeightSum parityCompositionWeightSum
  let p : ParityComposition n → Prop :=
    IsSurvivorParityComposition
  let instFinite :
      Fintype {x : ParityComposition n // p x} :=
    Fintype.ofFinite _
  let instSubtype :
      Fintype {x : ParityComposition n // p x} :=
    Subtype.fintype p
  have huniv :
      @Finset.univ {x : ParityComposition n // p x} instFinite =
        @Finset.univ {x : ParityComposition n // p x} instSubtype := by
    ext x
    simp
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      p
      (fun c : ParityComposition n => 2 ^ (c.length - 1))
  have hnonneg :
      0 ≤ ∑ c : {x : ParityComposition n // ¬ p x},
        2 ^ (c.1.length - 1) := by
    exact Nat.zero_le _
  have hle :
      (∑ c : {x : ParityComposition n // p x},
          2 ^ (c.1.length - 1)) ≤
        ∑ c : ParityComposition n,
          2 ^ (c.length - 1) := by
    omega
  rw [huniv]
  exact hle

/-- `3^3 < 2^5` を任意の positive 冪へ持ち上げた形。 -/
theorem threePow_three_mul_lt_twoPow_five_mul
    {r : ℕ}
    (hr : 0 < r) :
    3 ^ (3 * r) < 2 ^ (5 * r) := by
  have hbase : (3 : ℕ) ^ 3 < 2 ^ 5 := by norm_num
  have hp := Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hr)
  simpa only [← pow_mul] using hp

/--
depth `5r` の survivor は、`r > 0` なら block 数が必ず `3r` より大きい。
-/
theorem survivorParity_length_gt_three_mul
    {r : ℕ}
    (hr : 0 < r)
    (S : SurvivorParityCode (5 * r)) :
    3 * r < S.1.length := by
  by_contra hnot
  have hlen : S.1.length ≤ 3 * r := by omega
  have hpowLen : 3 ^ S.1.length ≤ 3 ^ (3 * r) :=
    Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hlen
  have hterminal : 2 ^ (5 * r) ≤ 3 ^ S.1.length := S.2.terminal_safe
  have hstrict := threePow_three_mul_lt_twoPow_five_mul hr
  have : 2 ^ (5 * r) < 2 ^ (5 * r) :=
    lt_of_le_of_lt (le_trans hterminal hpowLen) hstrict
  exact (Nat.lt_irrefl _ this)

/--
各 survivor の重みが `2^(3r)` 以上なので、cardinal に同じ係数を掛けても
survivor 重み総和以下になる。
-/
theorem twoPow_three_mul_mul_survivorCount_le_weight
    {r : ℕ}
    (hr : 0 < r) :
    2 ^ (3 * r) * survivorParityCount (5 * r) ≤
      survivorParityWeightSum (5 * r) := by
  classical
  unfold survivorParityCount
  rw [Nat.card_eq_fintype_card]
  calc
    2 ^ (3 * r) * Fintype.card (SurvivorParityCode (5 * r)) =
        ∑ S : SurvivorParityCode (5 * r), 2 ^ (3 * r) := by
      simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ S : SurvivorParityCode (5 * r),
          2 ^ (S.1.length - 1) := by
      apply Finset.sum_le_sum
      intro S hS
      have hlen := survivorParity_length_gt_three_mul hr S
      have hexp : 3 * r ≤ S.1.length - 1 := by
        omega
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp
    _ = survivorParityWeightSum (5 * r) := by
      unfold survivorParityWeightSum
      have huniv :
          @Finset.univ
              (SurvivorParityCode (5 * r))
              (Subtype.fintype IsSurvivorParityComposition) =
            @Finset.univ
              (SurvivorParityCode (5 * r))
              (Fintype.ofFinite (SurvivorParityCode (5 * r))) := by
        ext S
        simp
      rw [huniv]

/--
整数だけで書いた coarse survivor bound。

`2^(3r) * S_(5r) ≤ 3^(5r-1)`。
-/
theorem survivorParityCount_five_mul_weighted_bound
    {r : ℕ}
    (hr : 0 < r) :
    2 ^ (3 * r) * survivorParityCount (5 * r) ≤
      3 ^ (5 * r - 1) := by
  calc
    2 ^ (3 * r) * survivorParityCount (5 * r) ≤
        survivorParityWeightSum (5 * r) :=
      twoPow_three_mul_mul_survivorCount_le_weight hr
    _ ≤ parityCompositionWeightSum (5 * r) :=
      survivorParityWeightSum_le_all (5 * r)
    _ = 3 ^ (5 * r - 1) :=
      parityCompositionWeightSum_eq_threePow (by omega)

/-- survivor mass は常に非負。 -/
theorem survivorParityRatio_nonneg
    (n : ℕ) :
    0 ≤ survivorParityRatio n := by
  unfold survivorParityRatio
  positivity

/--
5段ごとの survivor mass に対する幾何減衰。

`243 / 256 = 3^5 / 2^8 < 1` が coarse contraction ratio になる。
-/
theorem survivorParityRatio_five_mul_le_geometric
    {r : ℕ}
    (hr : 0 < r) :
    survivorParityRatio (5 * r) ≤
      ((243 : ℝ) / 256) ^ r := by
  have hNat := survivorParityCount_five_mul_weighted_bound hr
  have hReal :
      (2 ^ (3 * r) : ℝ) * (survivorParityCount (5 * r) : ℝ) ≤
        (3 ^ (5 * r - 1) : ℝ) := by
    exact_mod_cast hNat
  unfold survivorParityRatio
  have h2 : (0 : ℝ) < 2 ^ (5 * r) := by positivity
  have h23 : (0 : ℝ) < 2 ^ (3 * r) := by positivity
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hPowRewrite :
      ((243 : ℝ) / 256) ^ r =
        (3 ^ (5 * r) : ℝ) / (2 ^ (8 * r) : ℝ) := by
    calc
      ((243 : ℝ) / 256) ^ r =
          (((3 : ℝ) ^ 5) / ((2 : ℝ) ^ 8)) ^ r := by norm_num
      _ = (((3 : ℝ) ^ 5) ^ r) / (((2 : ℝ) ^ 8) ^ r) := by
        rw [div_pow]
      _ = (3 ^ (5 * r) : ℝ) / (2 ^ (8 * r) : ℝ) := by
        rw [← pow_mul, ← pow_mul]
  rw [hPowRewrite]
  have hR :
      (survivorParityCount (5 * r) : ℝ) ≤
        (3 ^ (5 * r - 1) : ℝ) / (2 ^ (3 * r) : ℝ) := by
    exact (le_div_iff₀ h23).2 (by simpa [mul_comm] using hReal)
  calc
    (survivorParityCount (5 * r) : ℝ) / (2 ^ (5 * r) : ℝ) ≤
        ((3 ^ (5 * r - 1) : ℝ) / (2 ^ (3 * r) : ℝ)) /
          (2 ^ (5 * r) : ℝ) := by
      exact div_le_div_of_nonneg_right hR h2.le
    _ =
        (3 ^ (5 * r - 1) : ℝ) / (2 ^ (8 * r) : ℝ) := by
      rw [div_div, ← pow_add]
      congr 2
      omega
    _ ≤
        (3 ^ (5 * r) : ℝ) / (2 ^ (8 * r) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hExp : 5 * r - 1 ≤ 5 * r := by omega
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hExp

/-- `243/256` は `0` 以上 `1` 未満。 -/
theorem coarseSurvivorRatio_mem_unitInterval :
    (0 : ℝ) ≤ (243 : ℝ) / 256 ∧ (243 : ℝ) / 256 < 1 := by
  norm_num

/-- 5段ごとの survivor mass は 0 へ収束する。 -/
theorem tendsto_survivorParityRatio_five_mul_zero :
    Tendsto
      (fun r : ℕ => survivorParityRatio (5 * (r + 1)))
      atTop
      (𝓝 0) := by
  have hgeom :
      Tendsto (fun r : ℕ => ((243 : ℝ) / 256) ^ (r + 1)) atTop (𝓝 0) := by
    exact
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        coarseSurvivorRatio_mem_unitInterval.1
        coarseSurvivorRatio_mem_unitInterval.2).comp
        (tendsto_add_atTop_nat 1)
  apply squeeze_zero
  · intro r
    exact survivorParityRatio_nonneg _
  · intro r
    exact survivorParityRatio_five_mul_le_geometric (r := r + 1) (by omega)
  · exact hgeom

/-- positive depths で survivor mass は nonincreasing。 -/
theorem survivorParityRatio_succ_le
    {n : ℕ}
    (hn : 0 < n) :
    survivorParityRatio (n + 1) ≤ survivorParityRatio n := by
  have hstep := survivorParityRatio_step (n := n) hn
  have hmass : 0 ≤ firstCrossingParityMass (n + 1) := by
    unfold firstCrossingParityMass
    positivity
  linarith

/-- `n ↦ survivorParityRatio (n+1)` は単調減少。 -/
theorem survivorParityRatio_succ_antitone :
    Antitone (fun n : ℕ => survivorParityRatio (n + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  simpa [Nat.add_assoc] using
    survivorParityRatio_succ_le (n := n + 1) (by omega)

/-- survivor mass 全体も 0 へ収束する。 -/
theorem tendsto_survivorParityRatio_zero :
    Tendsto (fun n : ℕ => survivorParityRatio (n + 1)) atTop (𝓝 0) := by
  have hSub := tendsto_survivorParityRatio_five_mul_zero
  have hAnti := survivorParityRatio_succ_antitone
  have hNonneg :
      ∀ n : ℕ, 0 ≤ survivorParityRatio (n + 1) :=
    fun n => survivorParityRatio_nonneg _
  -- 単調減少列が cofinal な部分列で 0 へ行くので、列全体も 0 へ行く。
  rw [Metric.tendsto_atTop] at hSub ⊢
  intro ε hε
  rcases hSub ε hε with ⟨R, hR⟩
  let M := 5 * (R + 1)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  -- 部分列の R 番目、すなわち depth M では既に ε 未満。
  have hSmallDist :
      dist (survivorParityRatio M) 0 < ε := by
    dsimp [M]
    exact hR R le_rfl
  have hSmallAbs :
      |survivorParityRatio M| < ε := by
    simpa [Real.dist_eq] using hSmallDist
  refine ⟨M, ?_⟩
  intro n hn
  -- `survivorParityRatio M` を antitone 列
  -- `k ↦ survivorParityRatio (k + 1)` の項として読むための添字。
  let k := M - 1
  have hkSucc : k + 1 = M := by
    dsimp [k]
    omega
  have hkn : k ≤ n := by
    dsimp [k]
    omega
  -- antitone 性より、M 以降の項は M 番目以下。
  have hUpper :
      survivorParityRatio (n + 1) ≤
        survivorParityRatio M := by
    have h := hAnti hkn
    change
      survivorParityRatio (n + 1) ≤
        survivorParityRatio (k + 1) at h
    rw [hkSucc] at h
    exact h
  -- 両辺は非負なので、絶対値を付けても大小関係はそのまま。
  have hAbs :
      |survivorParityRatio (n + 1)| ≤
        |survivorParityRatio M| := by
    rw [
      abs_of_nonneg (hNonneg n),
      abs_of_nonneg (survivorParityRatio_nonneg M)
    ]
    exact hUpper
  have hGoal :
      |survivorParityRatio (n + 1)| < ε :=
    lt_of_le_of_lt hAbs hSmallAbs
  simpa [Real.dist_eq] using hGoal

end Bridge
end Collatz3
