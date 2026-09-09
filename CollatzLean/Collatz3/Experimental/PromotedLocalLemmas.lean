import CollatzLean.Collatz3.Experimental.UnitCarryMechanicalCharacterization
import CollatzLean.Collatz3.Experimental.RoofPathExact

/-!
# Collatz3 experimental: 長い証明から昇格した局所補題

`Experimental` を凍結する前に、後の `Experimental2` で基礎部品として再利用すべき
局所算術を名前付き theorem として取り出す。

ここでは新しい強い仮定を追加しない。
既存の長い theorem の内部で繰り返し使われていた等式・有限算術・正規化則を
独立した derived theorem として公開する。
-/

namespace Collatz3
namespace Experimental

/--
点 `k` における屋根からの未達量。

`height k ≤ β k` の下では `0` であることと roof 上にいることが同値になる。
-/
def roofSlack
    (β height : ℕ → ℕ)
    (k : ℕ) : ℕ :=
  β k - height k

/-- roof bound の下では slack `0` と exact roof return は同値。 -/
theorem roofSlack_eq_zero_iff_of_le
    {β height : ℕ → ℕ}
    {k : ℕ}
    (hLe : height k ≤ β k) :
    roofSlack β height k = 0 ↔ height k = β k := by
  unfold roofSlack
  omega

namespace HasUnitCarry

/--
線形成分を除いた residual 自身も unit-carry roof である。

したがって residual 用の反復上下界を別に帰納証明する必要はなく、
元の unit-carry 理論をそのまま再利用できる。
-/
theorem residual_hasUnitCarry
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    HasUnitCarry (roofResidual β) := by
  intro a b
  have hAdd := U.residual_add_eq a b
  have hCarryLe := U.carry_le_one a b
  constructor <;> omega

/--
residual 化しても二項 carry は変わらない。

線形成分 `n * β(1)` は加法的なので、carry は正規化前後で完全に保存される。
-/
theorem roofCarry_residual_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofCarry (roofResidual β) a b = roofCarry β a b := by
  have hAdd := U.residual_add_eq a b
  unfold roofCarry at hAdd ⊢
  omega

/--
start が roof 上にあり、endpoint が proper 範囲にあるときの局所保存式。

`localDepth + endpoint roofSlack = block roof + carry`。

local failure theorem の本体は、この等式と `carry ≤ 1` だけで読める。
-/
theorem localDepth_add_roofSlack_eq_blockDepth_add_carry
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a j : ℕ}
    (hStartRoof : height a = β a)
    (hEndLt : a + j < m) :
    localDepth height a j + roofSlack β height (a + j) =
      β j + roofCarry β a j := by
  have hDepthAdd :=
    IsAdmissibleRoofPath.height_add_localDepth
      A (Nat.le_of_lt hEndLt)
  have hEndLe : height (a + j) ≤ β (a + j) :=
    A.1 (a + j) hEndLt
  have hCarry := U.add_eq a j
  rw [hStartRoof] at hDepthAdd
  unfold roofSlack
  omega

/--
terminal block の局所深さを直接数値化する exact law。

`localDepth = criticalDepth(block) + terminal carry`。

従って terminal minimality は carry `0` と即座に同値になる。
-/
theorem terminalLocalDepth_eq_criticalDepth_add_carry
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ}
    (hStartRoof : IsRoofCut β m height a)
    (hTerminal : a + r = m) :
    localDepth height a r =
      criticalDepth β r + roofCarry β a r := by
  have hDepthAdd :=
    IsAdmissibleRoofPath.height_add_localDepth
      A (Nat.le_of_eq hTerminal)
  have hStart := hStartRoof.2.2
  have hTerminalHeight :
      height (a + r) = criticalDepth β m := by
    rw [hTerminal]
    exact A.2.2
  have hCarry := U.add_eq a r
  rw [hStart, hTerminalHeight] at hDepthAdd
  rw [hTerminal] at hCarry
  unfold criticalDepth at hDepthAdd ⊢
  omega

/--
一般 anchor `a` の factorization が `β(a)` を明示的に含むなら、
余剰 `K` は carry 総和そのもの。
-/
theorem factorization_carryBudget
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a m K : ℕ}
    (rs : List ℕ)
    (hCover : m = a + rs.sum)
    (hFactor :
      β m = β a + (rs.map β).sum + K) :
    (carryListFrom β a rs).sum = K := by
  have hExact := U.roof_add_sum_eq_blockRoofs_add_carries a rs
  rw [← hCover] at hExact
  omega

/--
anchor を右辺に含めない factorization の一般形。

`β(m) = Σβ(rᵢ) + K` なら
`β(a) + Σcarry = K`。
Record 型 normalized budget はこの一行の corollary になる。
-/
theorem factorization_anchor_add_carrySum_eq_budget
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a m K : ℕ}
    (rs : List ℕ)
    (hCover : m = a + rs.sum)
    (hFactor :
      β m = (rs.map β).sum + K) :
    β a + (carryListFrom β a rs).sum = K := by
  have hExact := U.roof_add_sum_eq_blockRoofs_add_carries a rs
  rw [← hCover] at hExact
  omega

end HasUnitCarry

namespace WidthRefinement

/--
有限二分 refinement tree では、内部 split 数 + 1 = leaf 数。

最大 internal defect を `leaf数 - 1` と読み替えるための基本木算術。
-/
@[simp] theorem internalCount_add_one_eq_leaves_length :
    ∀ t : WidthRefinement,
      t.internalCount + 1 = t.leaves.length
  | .leaf r => by
      simp [internalCount, leaves]
  | .node l r => by
      have hL := internalCount_add_one_eq_leaves_length l
      have hR := internalCount_add_one_eq_leaves_length r
      simp only [internalCount, leaves, List.length_append]
      omega

end WidthRefinement

/--
二つの homogenized slope は、各正幅 `n` で互いに `1/n` 以内にある。

一意性 theorem の Archimedean 部分から有限幅の定量評価を切り出した形。
-/
theorem homogenizedSlope_distance_le_inv
    {β : ℕ → ℕ}
    {ρ σ : ℝ}
    (Sρ : IsHomogenizedSlope β ρ)
    (Sσ : IsHomogenizedSlope β σ)
    {n : ℕ}
    (hn : 0 < n) :
    ρ ≤ σ + 1 / (n : ℝ) ∧
      σ ≤ ρ + 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hρ := Sρ n hn
  have hσ := Sσ n hn
  have hRS : ρ - σ ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    nlinarith [hρ.2, hσ.1]
  have hSR : σ - ρ ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    nlinarith [hσ.2, hρ.1]
  constructor <;> linarith

/--
任意の正整数幅で相互距離が `1/n` 以下なら二実数は一致する。

homogenized slope 一意性の純粋 Archimedean 終了補題。
-/
theorem eq_of_mutual_le_add_inv_nat
    {ρ σ : ℝ}
    (H : ∀ n : ℕ, 0 < n →
      ρ ≤ σ + 1 / (n : ℝ) ∧
        σ ≤ ρ + 1 / (n : ℝ)) :
    ρ = σ := by
  apply le_antisymm
  · by_contra hNot
    have hlt : σ < ρ := lt_of_not_ge hNot
    have hgap : 0 < ρ - σ := sub_pos.mpr hlt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    let n : ℕ := k + 1
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hClose := (H n hn).1
    have hk' : 1 / (n : ℝ) < ρ - σ := by
      simpa [n] using hk
    linarith
  · by_contra hNot
    have hlt : ρ < σ := lt_of_not_ge hNot
    have hgap : 0 < σ - ρ := sub_pos.mpr hlt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    let n : ℕ := k + 1
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hClose := (H n hn).2
    have hk' : 1 / (n : ℝ) < σ - ρ := by
      simpa [n] using hk
    linarith

/--
既約 rational slope では scaled boundary 条件 `q ∣ n*p` は index boundary `q ∣ n` と同値。

既存補題を、後段で意味が読みやすい名前へ昇格した wrapper。
-/
theorem scaledBoundary_dvd_index_iff_of_coprime
    {p q n : ℕ}
    (hCoprime : Nat.Coprime p q) :
    q ∣ n * p ↔ q ∣ n := by
  exact dvd_mul_right_iff_dvd_of_coprime hCoprime

/--
scaled lower cell `k*q ≤ x < (k+1)*q` から Nat 除算を exact に復元する。
-/
theorem natDiv_eq_of_scaledLowerCell
    {k q x : ℕ}
    (hLower : k * q ≤ x)
    (hUpper : x < (k + 1) * q) :
    x / q = k := by
  exact Nat.div_eq_of_lt_le hLower hUpper

/--
scaled upper cell `k*q < x ≤ (k+1)*q` から `(x-1)/q = k` を exact に復元する。

rational upper mechanical closed form の純粋 Nat 算術部分。
-/
theorem natSubOneDiv_eq_of_scaledUpperCell
    {k q x : ℕ}
    (hLower : k * q < x)
    (hUpper : x ≤ (k + 1) * q) :
    (x - 1) / q = k := by
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

end Experimental
end Collatz3
