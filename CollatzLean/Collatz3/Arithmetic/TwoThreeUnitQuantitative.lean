import CollatzLean.Collatz3.Arithmetic.TwoThreeUnit

/-!
# Collatz3 Arithmetic: `{2,3}`-unit certificate の項数下界

以前の定量化では、固定項数 `N` から exponent 上界を返す関数

`F : ℕ → ℕ`

を classical choice で取り出していた。

しかし Collatz 側で本当に必要なのは逆向きである。
深さ `k` を実現する nondegenerate certificate が、最低何項を必要とするかを直接測る。

このファイルでは

* fixed card なら `k` は一様有界、という qualitative escape
* `G k ≤ card` という quantitative lower-bound interface

だけを置く。
`G(k)` の具体的な成長率はここでは仮定しない。
-/

namespace Collatz3
namespace Arithmetic

/--
深さ `k` の nondegenerate `{2,3}`-unit certificate は、
固定 cardinality `D` のまま arbitrarily deep にはできない。

これは既存の exponent-bound interface を、定量化に向いた逆向きに読み直したもの。
-/
def NondegenerateTwoThreeUnitCardEscape : Prop :=
  ∀ D : ℕ,
    ∃ K : ℕ,
      ∀ {ι : Type} [DecidableEq ι],
        ∀ (term : ι → SignedTwoThreeUnit)
          (s : Finset ι)
          (k : ℕ),
          K ≤ k →
          NondegenerateSumOne
            (fun i => (term i).value) s →
          (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
          D < s.card

/--
既存の `NondegenerateTwoThreeUnitExponentBound` から、
cardinality 版の qualitative escape が従う。
-/
theorem nondegenerateTwoThreeUnitCardEscape_of_exponentBound
    (h : NondegenerateTwoThreeUnitExponentBound) :
    NondegenerateTwoThreeUnitCardEscape := by
  intro D
  rcases h D with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro ι inst term s k hk hNondegenerate hThree
  by_contra hNot
  have hCard : s.card ≤ D := by
    omega
  have hkLt : k < K :=
    hK term s k hCard hNondegenerate hThree
  omega

/--
自然数値 complexity lower bound `G` が無限へ発散する、という最小 interface。

実際に狙う候補は概念的には

`G(k) ≍ log k / log log k`

だが、ここでは具体式を固定しない。
-/
def NatTendsToInfinity (G : ℕ → ℕ) : Prop :=
  ∀ D : ℕ,
    ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → D < G k

/--
深さ `k` を含む任意の nondegenerate certificate は、
少なくとも `G k` 項を必要とする、という直接の定量 target。
-/
def NondegenerateTwoThreeUnitCardLowerBound
    (G : ℕ → ℕ) : Prop :=
  ∀ {ι : Type} [DecidableEq ι],
    ∀ (term : ι → SignedTwoThreeUnit)
      (s : Finset ι)
      (k : ℕ),
      NondegenerateSumOne
        (fun i => (term i).value) s →
      (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
      G k ≤ s.card

/--
定量 card lower bound `G` が発散するなら、fixed-card escape が従う。
-/
theorem NondegenerateTwoThreeUnitCardLowerBound.to_cardEscape
    {G : ℕ → ℕ}
    (hLower : NondegenerateTwoThreeUnitCardLowerBound G)
    (hGrowth : NatTendsToInfinity G) :
    NondegenerateTwoThreeUnitCardEscape := by
  intro D
  rcases hGrowth D with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro ι inst term s k hk hNondegenerate hThree
  have hComplexity : G k ≤ s.card :=
    hLower term s k hNondegenerate hThree
  have hLarge : D < G k := hK k hk
  omega

end Arithmetic
end Collatz3
