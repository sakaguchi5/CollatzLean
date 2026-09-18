import CollatzLean.Collatz3.Arithmetic.TwoThreeUnitQuantitative

/-!
# Collatz3 Arithmetic: two-layer `{2,3}`-unit complexity

Collatz の sparse block equation から得られる unit は、3-exponent が

`0` または同じ `k`

の二層に限られる。

以前はここで

`k < exp(O(D log D))`

型の exponent 上界を直接 target にしていたが、定量化の向きとしては
「深さ `k` を実現するには最低何項必要か」を直接扱う方が自然である。

このファイルは一般 two-layer certificate に対する card lower bound を置く。
実際の Collatz 定量化では、さらに特殊な exact block-sparse equation を使う。
-/

namespace Collatz3
namespace Arithmetic

/-- 3-exponent が `0` または指定した `k` のどちらかだけにある。 -/
def IsTwoLayerAt (k : ℕ) (t : SignedTwoThreeUnit) : Prop :=
  t.threeExp = 0 ∨ t.threeExp = k

/--
固定 cardinality `D` の two-layer nondegenerate certificate は、
深さを arbitrarily large にできない。
-/
def TwoSidedSignedSparsePow3CardEscape : Prop :=
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
          (∀ i ∈ s, IsTwoLayerAt k (term i)) →
          D < s.card

/--
既存の一般 `{2,3}`-unit exponent bound から、
two-layer certificate の fixed-card escape が従う。
-/
theorem twoSidedSignedSparsePow3CardEscape_of_twoThreeUnitBound
    (h : NondegenerateTwoThreeUnitExponentBound) :
    TwoSidedSignedSparsePow3CardEscape := by
  have hGeneral : NondegenerateTwoThreeUnitCardEscape :=
    nondegenerateTwoThreeUnitCardEscape_of_exponentBound h
  intro D
  rcases hGeneral D with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro ι inst term s k hk hNondegenerate hThree hTwoLayer
  exact hK term s k hk hNondegenerate hThree

/--
深さ `k` の two-layer certificate は最低 `G k` 項必要、という定量 target。

一般 two-layer 版は Collatz の exact equation より広い。
後段では block 固有の符号・top term・hole 構造を保持した、より狭い target を使う。
-/
def TwoSidedSignedSparsePow3CardLowerBound
    (G : ℕ → ℕ) : Prop :=
  ∀ {ι : Type} [DecidableEq ι],
    ∀ (term : ι → SignedTwoThreeUnit)
      (s : Finset ι)
      (k : ℕ),
      NondegenerateSumOne
        (fun i => (term i).value) s →
      (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
      (∀ i ∈ s, IsTwoLayerAt k (term i)) →
      G k ≤ s.card

/--
quantitative lower bound が無限へ発散するなら、two-layer fixed-card escape が従う。
-/
theorem TwoSidedSignedSparsePow3CardLowerBound.to_cardEscape
    {G : ℕ → ℕ}
    (hLower : TwoSidedSignedSparsePow3CardLowerBound G)
    (hGrowth : NatTendsToInfinity G) :
    TwoSidedSignedSparsePow3CardEscape := by
  intro D
  rcases hGrowth D with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro ι inst term s k hk hNondegenerate hThree hTwoLayer
  have hComplexity : G k ≤ s.card :=
    hLower term s k hNondegenerate hThree hTwoLayer
  have hLarge : D < G k := hK k hk
  omega

end Arithmetic
end Collatz3
