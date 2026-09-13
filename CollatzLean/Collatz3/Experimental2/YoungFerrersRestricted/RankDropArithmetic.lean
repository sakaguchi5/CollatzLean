import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RecordFerrersDiagonalBoundary
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.OstrowskiRankFerrersBridge
import CollatzLean.Collatz3.Experimental2.Normalization
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: rank drop の算術正規形

F8 で canonical width boundary と rank-drop height boundary の衝突を
RecordFerrers の plateau 座標へ戻した。
本ファイルでは、その縦落差 `rankDropInt` 自体を算術的に展開する。

中心は

`rankDropInt β m r
  = m * β(r) - r * β(m) + m - r`

である。

さらに整数線形成分を `normalizeRoof` で除くと、その線形成分は完全に相殺される。
従って rank drop は fractional / normalized roof 側だけで決まり、
終端対 `(m, criticalDepth β m)` の最大公約数はすべての rank drop を割る。

この gcd divisibility は後段で boundary collision の候補 level を制限する。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
rank drop を roof 値だけで書いた基本公式。
`criticalDepth β n = β n + 1` を展開しただけだが、
後段の floor / Ostrowski / Collatz 特殊化の標準入口になる。
-/
theorem rankDropInt_eq_roofFormula
    (β : ℕ → ℕ)
    (m r : ℕ) :
    rankDropInt β m r =
      (m : ℤ) * (β r : ℤ) -
        (r : ℤ) * (β m : ℤ) +
          (m : ℤ) - (r : ℤ) := by
  unfold rankDropInt criticalDepth
  push_cast
  ring

/--
unit-carry roof では正幅 `r` の rank drop は常に幅 `m` より小さい。
完成 RecordFerrers の canonical block では rank drop はさらに正なので、
`1,...,m-1` の有限範囲に入る。
-/
theorem rankDropInt_lt_width_of_unitCarry
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m r : ℕ}
    (hr : 0 < r) :
    rankDropInt β m r < (m : ℤ) := by
  have hChord := U.below_criticalChord (m := m) (r := r) hr
  have hChordZ :
      (m : ℤ) * (β r : ℤ) <
        (criticalDepth β m : ℤ) * (r : ℤ) := by
    exact_mod_cast hChord
  unfold rankDropInt criticalDepth at hChordZ ⊢
  push_cast at hChordZ ⊢
  ring_nf at hChordZ ⊢
  omega

/--
幅 `m` と terminal critical depth の最大公約数。
すべての local rank drop に共通する算術 modulus として使う。
-/
def rankDropGcd
    (β : ℕ → ℕ)
    (m : ℕ) : ℕ :=
  Nat.gcd m (criticalDepth β m)

/-- `criticalDepth β m` は必ず正なので `rankDropGcd` も正。 -/
theorem rankDropGcd_pos
    (β : ℕ → ℕ)
    (m : ℕ) :
    0 < rankDropGcd β m := by
  unfold rankDropGcd
  by_contra h
  have hg0 : Nat.gcd m (criticalDepth β m) = 0 :=
    Nat.eq_zero_of_not_pos h
  have hdiv := Nat.gcd_dvd_right m (criticalDepth β m)
  rw [hg0] at hdiv
  have hdepth0 : criticalDepth β m = 0 := by
    simpa using hdiv
  unfold criticalDepth at hdepth0
  omega

/-- terminal gcd による幅・深さの共通因数分解は常に存在する。 -/
theorem exists_rankDropGcd_factorization
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∃ q p : ℕ,
      m = rankDropGcd β m * q ∧
        criticalDepth β m = rankDropGcd β m * p := by
  have hm := Nat.gcd_dvd_left m (criticalDepth β m)
  have hH := Nat.gcd_dvd_right m (criticalDepth β m)
  rcases hm with ⟨q, hq⟩
  rcases hH with ⟨p, hp⟩
  exact ⟨q, p, hq, hp⟩

/-- 正幅なら上の reduced width `q` も正に取れる。 -/
theorem exists_rankDropGcd_factorization_of_posWidth
    (β : ℕ → ℕ)
    {m : ℕ}
    (hmPos : 0 < m) :
    ∃ q p : ℕ,
      0 < q ∧
        m = rankDropGcd β m * q ∧
          criticalDepth β m = rankDropGcd β m * p := by
  rcases exists_rankDropGcd_factorization β m with ⟨q, p, hq, hp⟩
  have hqPos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0, Nat.mul_zero] at hq
    omega
  exact ⟨q, p, hqPos, hq, hp⟩

/--
`gcd(m, criticalDepth β m)` は任意の rank drop を整数として割る。
これは rank drop が終端ベクトルとの 2x2 determinant であることの直接の系。
-/
theorem rankDropGcd_dvd_rankDropInt
    (β : ℕ → ℕ)
    (m r : ℕ) :
    (rankDropGcd β m : ℤ) ∣ rankDropInt β m r := by
  have hm : Nat.gcd m (criticalDepth β m) ∣ m :=
    Nat.gcd_dvd_left m (criticalDepth β m)
  have hH :
      Nat.gcd m (criticalDepth β m) ∣ criticalDepth β m :=
    Nat.gcd_dvd_right m (criticalDepth β m)
  rcases hm with ⟨a, ha⟩
  rcases hH with ⟨b, hb⟩
  have haZ :
      (m : ℤ) =
        (Nat.gcd m (criticalDepth β m) : ℤ) * (a : ℤ) := by
    exact_mod_cast ha
  have hbZ :
      (criticalDepth β m : ℤ) =
        (Nat.gcd m (criticalDepth β m) : ℤ) * (b : ℤ) := by
    exact_mod_cast hb
  refine ⟨
    (a : ℤ) * (criticalDepth β r : ℤ) -
      (b : ℤ) * (r : ℤ),
    ?_
  ⟩
  unfold rankDropGcd rankDropInt
  rw [haZ, hbZ]
  ring

/-- positive rank drop は `toNat` してから `ℤ` に戻しても失われない。 -/
theorem rankDropNat_cast_eq_rankDropInt_of_pos
    {β : ℕ → ℕ}
    {m r : ℕ}
    (hpos : 0 < rankDropInt β m r) :
    (rankDropNat β m r : ℤ) = rankDropInt β m r := by
  unfold rankDropNat
  exact Int.toNat_of_nonneg (le_of_lt hpos)

/--
正の rank drop の自然数表示も同じ gcd modulus を保つ。
完成 RecordFerrers の canonical block にはこの形を使う。
-/
theorem rankDropGcd_dvd_rankDropNat_cast_of_pos
    {β : ℕ → ℕ}
    {m r : ℕ}
    (hpos : 0 < rankDropInt β m r) :
    (rankDropGcd β m : ℤ) ∣ (rankDropNat β m r : ℤ) := by
  rw [rankDropNat_cast_eq_rankDropInt_of_pos hpos]
  exact rankDropGcd_dvd_rankDropInt β m r

/--
terminal pair を `m = g*q`, `criticalDepth β m = g*p` と因数分解する。
block width `r` が reduced width `q` の倍数なら、rank drop は幅 `m` 自身の倍数になる。

正の rank drop が `m` 未満であることと組み合わせると、canonical block は `q` の倍数になれない。
-/
theorem width_dvd_rankDropInt_of_terminalFactorization
    {β : ℕ → ℕ}
    {m r g p q : ℕ}
    (hm : m = g * q)
    (hH : criticalDepth β m = g * p)
    (hr : q ∣ r) :
    (m : ℤ) ∣ rankDropInt β m r := by
  rcases hr with ⟨k, hk⟩
  refine ⟨
    (criticalDepth β r : ℤ) - (p : ℤ) * (k : ℤ),
    ?_
  ⟩
  unfold rankDropInt
  rw [hH, hm, hk]
  push_cast
  ring

/--
unit-carry roof の正の rank drop block は、terminal pair の reduced width `q` の倍数になれない。
ここでは quotient を primitive にせず、`m=g*q`, `H=g*p` という thin factorization を入力にする。
-/
theorem reducedWidth_not_dvd_of_positiveRankDrop
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m r g p q : ℕ}
    (hm : m = g * q)
    (hH : criticalDepth β m = g * p)
    (hrPos : 0 < r)
    (hDropPos : 0 < rankDropInt β m r) :
    ¬ q ∣ r := by
  intro hqr
  have hmDvdInt : (m : ℤ) ∣ rankDropInt β m r :=
    width_dvd_rankDropInt_of_terminalFactorization hm hH hqr
  have hCast := rankDropNat_cast_eq_rankDropInt_of_pos hDropPos
  have hmDvdNatCast : (m : ℤ) ∣ (rankDropNat β m r : ℤ) := by
    rw [hCast]
    exact hmDvdInt
  have hmDvdNat : m ∣ rankDropNat β m r := by
    exact_mod_cast hmDvdNatCast
  have hNatPosZ : (0 : ℤ) < (rankDropNat β m r : ℤ) := by
    rw [hCast]
    exact hDropPos
  have hNatPos : 0 < rankDropNat β m r := by
    exact_mod_cast hNatPosZ
  have hLtInt := rankDropInt_lt_width_of_unitCarry (m := m) (r := r) U hrPos
  have hLtNatCast : (rankDropNat β m r : ℤ) < (m : ℤ) := by
    rw [hCast]
    exact hLtInt
  have hLtNat : rankDropNat β m r < m := by
    exact_mod_cast hLtNatCast
  have hLe : m ≤ rankDropNat β m r := Nat.le_of_dvd hNatPos hmDvdNat
  omega

/--
rank drop は整数線形 gauge を除いた正規化 roof だけで決まる。
`β n = n*β(1) + normalizeRoof β n` の線形成分は determinant 内で相殺される。
-/
theorem rankDropInt_eq_normalizedRoofFormula
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (m r : ℕ) :
    rankDropInt β m r =
      (m : ℤ) * (normalizeRoof β r : ℤ) -
        (r : ℤ) * (normalizeRoof β m : ℤ) +
          (m : ℤ) - (r : ℤ) := by
  rw [rankDropInt_eq_roofFormula]
  have hr := U.eq_linear_add_normalizeRoof r
  have hm := U.eq_linear_add_normalizeRoof m
  rw [hr, hm]
  push_cast
  ring

/-- rank drop 自体も normalization で不変。 -/
theorem rankDropInt_normalizeRoof_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (m r : ℕ) :
    rankDropInt (normalizeRoof β) m r = rankDropInt β m r := by
  calc
    rankDropInt (normalizeRoof β) m r =
        (m : ℤ) * (normalizeRoof β r : ℤ) -
          (r : ℤ) * (normalizeRoof β m : ℤ) +
            (m : ℤ) - (r : ℤ) :=
      rankDropInt_eq_roofFormula (normalizeRoof β) m r
    _ = rankDropInt β m r :=
      (rankDropInt_eq_normalizedRoofFormula U m r).symm

/-- 自然数 rank-drop sum は map 後の通常の list sum と同じ。 -/
theorem rankDropNatSum_eq_map_sum
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ rs : List ℕ,
      rankDropNatSum β m rs = (rs.map (rankDropNat β m)).sum
  | [] => by rfl
  | r :: rs => by
      simp [rankDropNatSum, rankDropNatSum_eq_map_sum β m rs]

/-- 整数 rank-drop sum も map 後の通常の list sum と同じ。 -/
theorem rankDropIntSum_eq_map_sum
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ rs : List ℕ,
      rankDropIntSum β m rs = (rs.map (rankDropInt β m)).sum
  | [] => by rfl
  | r :: rs => by
      simp [rankDropIntSum, rankDropIntSum_eq_map_sum β m rs]

/--
rank drop の list 和を terminal critical depth との線形式へまとめる。
collision equation の suffix 側を一括展開するときの基本式。
-/
theorem rankDropIntSum_eq_criticalDepthFormula
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ rs : List ℕ,
      rankDropIntSum β m rs =
        (m : ℤ) * (rs.map (fun r => (criticalDepth β r : ℤ))).sum -
          (criticalDepth β m : ℤ) * (rs.sum : ℤ)
  | [] => by simp [rankDropIntSum]
  | r :: rs => by
      rw [rankDropIntSum]
      rw [rankDropIntSum_eq_criticalDepthFormula β m rs]
      simp only [List.map_cons, List.sum_cons]
      push_cast
      unfold rankDropInt
      ring

/-- 各要素ごとの正値条件から `PositiveRankDrops` を組み立てる。 -/
theorem positiveRankDrops_of_forall_mem
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ rs : List ℕ,
      (∀ r ∈ rs, 0 < rankDropInt β m r) →
      PositiveRankDrops β m rs
  | [], _h => by trivial
  | r :: rs, h => by
      simp only [PositiveRankDrops]
      refine ⟨h r (by simp), ?_⟩
      apply positiveRankDrops_of_forall_mem β m rs
      intro q hq
      exact h q (by simp [hq])

/--
すべての block rank drop が正なら、自然数 suffix sum を `ℤ` に上げた値は
整数 rank-drop sum と exact に一致する。
-/
theorem rankDropNatSum_cast_eq_rankDropIntSum_of_positive
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ (rs : List ℕ),
      PositiveRankDrops β m rs →
      (rankDropNatSum β m rs : ℤ) =
        rankDropIntSum β m rs
  | [], _h => by
      simp [rankDropNatSum, rankDropIntSum]
  | r :: rs, h => by
      simp only [PositiveRankDrops] at h
      simp only [rankDropNatSum, rankDropIntSum]
      push_cast
      rw [rankDropNat_cast_eq_rankDropInt_of_pos h.1]
      rw [
        rankDropNatSum_cast_eq_rankDropIntSum_of_positive
          β m rs h.2
      ]

namespace RecordFerrers

/--
unit carry のもとで正の rank drop は自然数化しても terminal width 未満。
-/
theorem rankDropNat_lt_width_of_unitCarry_of_pos
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m r : ℕ}
    (hr : 0 < r)
    (hDropPos : 0 < rankDropInt β m r) :
    rankDropNat β m r < m := by
  have hCast :
      (rankDropNat β m r : ℤ) =
        rankDropInt β m r :=
    rankDropNat_cast_eq_rankDropInt_of_pos hDropPos
  have hLtInt :
      rankDropInt β m r < (m : ℤ) :=
    rankDropInt_lt_width_of_unitCarry
      (m := m) (r := r) U hr
  have hLtCast :
      (rankDropNat β m r : ℤ) < (m : ℤ) := by
    rw [hCast]
    exact hLtInt
  exact_mod_cast hLtCast

/--
正の rank drop は `rankDropGcd` の正の倍数として表せる。
-/
theorem exists_positive_reducedRankDropFactor
    (β : ℕ → ℕ)
    (m r : ℕ)
    (hDropPos : 0 < rankDropInt β m r) :
    ∃ δ : ℕ,
      0 < δ ∧
        rankDropNat β m r = rankDropGcd β m * δ := by
  have hCast :
      (rankDropNat β m r : ℤ) =
        rankDropInt β m r :=
    rankDropNat_cast_eq_rankDropInt_of_pos hDropPos
  have hGdvdZ :
      (rankDropGcd β m : ℤ) ∣
        (rankDropNat β m r : ℤ) :=
    rankDropGcd_dvd_rankDropNat_cast_of_pos hDropPos
  have hGdvdNat :
      rankDropGcd β m ∣ rankDropNat β m r := by
    exact_mod_cast hGdvdZ
  rcases hGdvdNat with ⟨δ, hδ⟩
  have hδPos : 0 < δ := by
    by_contra h
    have hδ0 : δ = 0 :=
      Nat.eq_zero_of_not_pos h
    rw [hδ0, Nat.mul_zero] at hδ
    have hDropNat0 :
        rankDropNat β m r = 0 :=
      hδ
    have hDropInt0 :
        rankDropInt β m r = 0 := by
      rw [← hCast, hDropNat0]
      simp
    omega
  exact ⟨δ, hδPos, hδ⟩

/--
同じ正の gcd 因子 `g` で

`rankDropNat = g*δ`, `m = g*q`

と書け、rank drop が `m` 未満なら `δ < q`。
-/
theorem reducedRankDrop_lt_terminalQuotient
    {β : ℕ → ℕ}
    {m r q δ : ℕ}
    (hm :
      m = rankDropGcd β m * q)
    (hδ :
      rankDropNat β m r = rankDropGcd β m * δ)
    (hLt :
      rankDropNat β m r < m) :
    δ < q := by
  have hgPos :
      0 < rankDropGcd β m :=
    rankDropGcd_pos β m
  have hMul :
      rankDropGcd β m * δ <
        rankDropGcd β m * q := by
    calc
      rankDropGcd β m * δ =
          rankDropNat β m r := hδ.symm
      _ < m := hLt
      _ = rankDropGcd β m * q := hm
  have hMulZ :
      (rankDropGcd β m : ℤ) * (δ : ℤ) <
        (rankDropGcd β m : ℤ) * (q : ℤ) := by
    exact_mod_cast hMul
  have hgZpos :
      (0 : ℤ) < (rankDropGcd β m : ℤ) := by
    exact_mod_cast hgPos
  have hδLtZ :
      (δ : ℤ) < (q : ℤ) := by
    nlinarith
  exact_mod_cast hδLtZ

/--
terminal pair と rank drop が共通因子 `g` を持つなら、
共通因子を除いた rank drop は exact determinant

`δ = q * criticalDepth β r - p * r`

になる。
-/
theorem reducedRankDrop_formula_of_factorizations
    {β : ℕ → ℕ}
    {m r g p q δ : ℕ}
    (hgPos : 0 < g)
    (hm : m = g * q)
    (hH : criticalDepth β m = g * p)
    (hδ : rankDropNat β m r = g * δ)
    (hDropPos : 0 < rankDropInt β m r) :
    (δ : ℤ) =
      (q : ℤ) * (criticalDepth β r : ℤ) -
        (p : ℤ) * (r : ℤ) := by
  have hCast :
      (rankDropNat β m r : ℤ) =
        rankDropInt β m r :=
    rankDropNat_cast_eq_rankDropInt_of_pos hDropPos
  have hmZ :
      (m : ℤ) =
        (g : ℤ) * (q : ℤ) := by
    exact_mod_cast hm
  have hHZ :
      (criticalDepth β m : ℤ) =
        (g : ℤ) * (p : ℤ) := by
    exact_mod_cast hH
  have hDet :
      (g : ℤ) * (δ : ℤ) =
        (g : ℤ) *
          ((q : ℤ) * (criticalDepth β r : ℤ) -
            (p : ℤ) * (r : ℤ)) := by
    calc
      (g : ℤ) * (δ : ℤ) =
          (rankDropNat β m r : ℤ) := by
        exact_mod_cast hδ.symm
      _ = rankDropInt β m r := hCast
      _ =
          (g : ℤ) *
            ((q : ℤ) * (criticalDepth β r : ℤ) -
              (p : ℤ) * (r : ℤ)) := by
        unfold rankDropInt
        rw [hmZ, hHZ]
        ring
  have hgZpos :
      (0 : ℤ) < (g : ℤ) := by
    exact_mod_cast hgPos
  nlinarith [hDet, hgZpos]

/--
完成 RecordFerrers の canonical block について terminal pair を

`m = g*q`, `criticalDepth β m = g*p`

と gcd で因数分解すると、rank drop も `g*δ` と因数分解できる。
しかも canonical block では rank drop が正かつ `m` 未満なので

`0 < δ < q`

であり、整数として

`δ = q * criticalDepth β r - p * r`

を満たす。

従って各 canonical block の normalized vertical drop は
有限集合 `1,...,q-1` に入る。
-/
theorem exists_reducedRankDropData_canonicalBlock
    {β : ℕ → ℕ}
    {m r : ℕ}
    (R : RecordFerrers β m)
    (hr : r ∈ canonicalRecordLengths β m R.height) :
    ∃ q p δ : ℕ,
      0 < q ∧
        0 < δ ∧
        δ < q ∧
        m = rankDropGcd β m * q ∧
        criticalDepth β m = rankDropGcd β m * p ∧
        rankDropNat β m r = rankDropGcd β m * δ ∧
        (δ : ℤ) =
          (q : ℤ) * (criticalDepth β r : ℤ) -
            (p : ℤ) * (r : ℤ) := by
  have hmPos : 0 < m :=
    lt_trans (by omega) R.one_lt_width
  rcases
      exists_rankDropGcd_factorization_of_posWidth
        β hmPos with
    ⟨q, p, hqPos, hm, hH⟩
  have hrPos : 0 < r :=
    canonicalRecordLengths_pos
      R.one_lt_width r hr
  have hDropPos :
      0 < rankDropInt β m r :=
    positiveRankDrop_of_mem
      R.positiveRankDrops hr
  rcases
      exists_positive_reducedRankDropFactor
        β m r hDropPos with
    ⟨δ, hδPos, hδ⟩
  have hLt :
      rankDropNat β m r < m :=
    rankDropNat_lt_width_of_unitCarry_of_pos
      R.unitCarry hrPos hDropPos
  have hδLt : δ < q :=
    reducedRankDrop_lt_terminalQuotient
      hm hδ hLt
  have hδFormula :
      (δ : ℤ) =
        (q : ℤ) * (criticalDepth β r : ℤ) -
          (p : ℤ) * (r : ℤ) :=
    reducedRankDrop_formula_of_factorizations
      (g := rankDropGcd β m)
      (p := p)
      (q := q)
      (δ := δ)
      (rankDropGcd_pos β m)
      hm
      hH
      hδ
      hDropPos
  exact
    ⟨q, p, δ,
      hqPos,
      hδPos,
      hδLt,
      hm,
      hH,
      hδ,
      hδFormula⟩

/--
上の reduced drop `δ` の exact formula から、`δ` は modulo `q` で `-p*r` と同じ剰余を持つ。
有限状態探索ではこちらの合同形を使える。
-/
theorem exists_reducedRankDropResidue_canonicalBlock
    {β : ℕ → ℕ}
    {m r : ℕ}
    (R : RecordFerrers β m)
    (hr : r ∈ canonicalRecordLengths β m R.height) :
    ∃ q p δ : ℕ,
      0 < q ∧
        0 < δ ∧
        δ < q ∧
        m = rankDropGcd β m * q ∧
        criticalDepth β m = rankDropGcd β m * p ∧
        rankDropNat β m r = rankDropGcd β m * δ ∧
        ((δ : ℤ) % (q : ℤ)) =
          ((-((p : ℤ) * (r : ℤ))) % (q : ℤ)) := by
  rcases R.exists_reducedRankDropData_canonicalBlock hr with
    ⟨q, p, δ, hq, hδ, hδq, hm, hH, hDrop, hFormula⟩
  refine ⟨q, p, δ, hq, hδ, hδq, hm, hH, hDrop, ?_⟩
  rw [hFormula]
  have hqZ : (q : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  calc
    (((q : ℤ) * (criticalDepth β r : ℤ) - (p : ℤ) * (r : ℤ)) % (q : ℤ)) =
        ((-((p : ℤ) * (r : ℤ))) % (q : ℤ)) := by
      rw [Int.sub_emod]
      simp only [Int.mul_emod_right, zero_sub]
      simpa only [zero_sub] using
        (Int.sub_emod_emod
          (0 : ℤ)
          ((p : ℤ) * (r : ℤ))
          (q : ℤ))

/--
完成 RecordFerrers の canonical block は、terminal gcd で既約化した horizontal width `q`
の倍数にはなれない。`q` は quotient を primitive にせず factorization witness として返す。
-/
theorem exists_terminalReduction_not_dvd_canonicalBlock
    {β : ℕ → ℕ}
    {m r : ℕ}
    (R : RecordFerrers β m)
    (hr : r ∈ canonicalRecordLengths β m R.height) :
    ∃ q p : ℕ,
      0 < q ∧
        m = rankDropGcd β m * q ∧
          criticalDepth β m = rankDropGcd β m * p ∧
            ¬ q ∣ r := by
  have hmPos : 0 < m := lt_trans (by omega) R.one_lt_width
  rcases exists_rankDropGcd_factorization_of_posWidth β hmPos with
    ⟨q, p, hqPos, hm, hH⟩
  have hrPos : 0 < r :=
    canonicalRecordLengths_pos R.one_lt_width r hr
  have hDropPos : 0 < rankDropInt β m r :=
    positiveRankDrop_of_mem R.positiveRankDrops hr
  have hNot : ¬ q ∣ r :=
    reducedWidth_not_dvd_of_positiveRankDrop
      R.unitCarry hm hH hrPos hDropPos
  exact ⟨q, p, hqPos, hm, hH, hNot⟩

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
