import CollatzLean.Collatz3.Arithmetic.TwoThreeUnitQuantitative

/-!
# Collatz3 Arithmetic: two-sided signed sparse `3^k` target

Collatz 側の sparse certificate では、各 `{2,3}`-unit の 3-adic exponent は
`0` または同じ `k` の二層しか現れない。

この二層をまとめると整数方程式は概念的に

`3^k * A = C`

となり、`A`, `C` はともに少数の符号付き 2 冪の和になる。

このファイルではその構造を S-unit certificate のまま保持し、

`k < (D+2)^(C0*D)`

という定量 target を定義する。右辺は
`exp(C0 * D * log(D+2))`
の整数版 envelope である。

重要:
この `exp(O(D log D))` 評価そのものは既存 ESS の存在版からは従わない。
したがって `TwoSidedSignedSparsePow3` は深い定量数論 target を表す `Prop` であり、
このファイルでは axiom / sorry として導入しない。
代わりに、任意の定量 exponent bound `F` がこの envelope 以下なら target が従うことを証明する。
-/

namespace Collatz3
namespace Arithmetic

/-- 3-adic exponent が `0` または指定した `k` のどちらかだけにある。 -/
def IsTwoLayerAt (k : ℕ) (t : SignedTwoThreeUnit) : Prop :=
  t.threeExp = 0 ∨ t.threeExp = k

/--
`exp(C0 * D * log(D+2))` に対応する自然数 envelope。
実数 `exp/log` を primitive にせず、同値な冪型を直接使う。
-/
def twoSidedSparseEnvelope (C0 D : ℕ) : ℕ :=
  (D + 2) ^ (C0 * D)


/--
指数関数形の growth rate を忘れた qualitative 版。

固定項数 `D` ごとに何らかの `K(D)` が存在する、という内容だけを保持する。
-/
def TwoSidedSignedSparsePow3Qualitative : Prop :=
  ∀ D : ℕ,
    ∃ K : ℕ,
      ∀ {ι : Type} [DecidableEq ι],
        ∀ (term : ι → SignedTwoThreeUnit)
          (s : Finset ι)
          (k : ℕ),
          s.card ≤ D →
          NondegenerateSumOne
            (fun i => (term i).value) s →
          (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
          (∀ i ∈ s, IsTwoLayerAt k (term i)) →
          k < K

/--
既存 ESS 型存在 bound から qualitative two-sided bound は無条件に得られる。
二層条件は一般 S-unit bound より弱い追加条件なので、そのまま忘れてよい。
-/
theorem twoSidedSignedSparsePow3Qualitative_of_twoThreeUnitBound
    (h : NondegenerateTwoThreeUnitExponentBound) :
    TwoSidedSignedSparsePow3Qualitative := by
  intro D
  rcases h D with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro ι inst term s k hCard hNondegenerate hThree hTwoLayer
  exact hK term s k hCard hNondegenerate hThree

/--
定数 `C0` を固定した two-sided signed sparse `3^k` bound。

nondegenerate certificate の全項が 3-exponent `0` または `k` の二層にあり、
項数が `D` 以下で `-3^k` anchor を含むなら、
`k` は `(D+2)^(C0*D)` 未満である。

二層をまとめれば `3^k A = C` で、`A,C` は合計 `D+O(1)` 個以下の
符号付き 2 冪からなる、という形に対応する。
-/
def TwoSidedSignedSparsePow3WithConstant (C0 : ℕ) : Prop :=
  ∀ D : ℕ,
    ∀ {ι : Type} [DecidableEq ι],
      ∀ (term : ι → SignedTwoThreeUnit)
        (s : Finset ι)
        (k : ℕ),
        s.card ≤ D →
        NondegenerateSumOne
          (fun i => (term i).value) s →
        (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
        (∀ i ∈ s, IsTwoLayerAt k (term i)) →
        k < twoSidedSparseEnvelope C0 D

/--
求める定量 target: ある絶対定数 `C0` で two-sided sparse bound が成立する。
-/
def TwoSidedSignedSparsePow3 : Prop :=
  ∃ C0 : ℕ, TwoSidedSignedSparsePow3WithConstant C0

/--
一般の定量 exponent bound `F` が冪型 envelope 以下なら、
two-sided signed sparse target が従う。

この定理により、今後の深い数論部分は
`F D ≤ (D+2)^(C0*D)` の証明だけに局所化できる。
-/
theorem twoSidedSignedSparsePow3WithConstant_of_exponentBoundBy
    {F : ℕ → ℕ} {C0 : ℕ}
    (hF : NondegenerateTwoThreeUnitExponentBoundBy F)
    (hEnvelope : ∀ D : ℕ, F D ≤ twoSidedSparseEnvelope C0 D) :
    TwoSidedSignedSparsePow3WithConstant C0 := by
  intro D ι inst term s k hCard hNondegenerate hThree hTwoLayer
  exact lt_of_lt_of_le
    (hF D term s k hCard hNondegenerate hThree)
    (hEnvelope D)

/--
上の条件を満たす `C0` が存在すれば `TwoSidedSignedSparsePow3` が成立する。
-/
theorem twoSidedSignedSparsePow3_of_exponentBoundBy
    {F : ℕ → ℕ}
    (hF : NondegenerateTwoThreeUnitExponentBoundBy F)
    (hEnvelope : ∃ C0 : ℕ,
      ∀ D : ℕ, F D ≤ twoSidedSparseEnvelope C0 D) :
    TwoSidedSignedSparsePow3 := by
  rcases hEnvelope with ⟨C0, hC0⟩
  exact ⟨C0,
    twoSidedSignedSparsePow3WithConstant_of_exponentBoundBy hF hC0⟩

/--
定量 target は特に、項数 `D` ごとの qualitative な exponent bound を与える。
-/
theorem TwoSidedSignedSparsePow3WithConstant.to_boundBy
    {C0 : ℕ}
    (h : TwoSidedSignedSparsePow3WithConstant C0) :
    ∀ D : ℕ,
      ∀ {ι : Type} [DecidableEq ι],
        ∀ (term : ι → SignedTwoThreeUnit)
          (s : Finset ι)
          (k : ℕ),
          s.card ≤ D →
          NondegenerateSumOne
            (fun i => (term i).value) s →
          (∃ i ∈ s, term i = SignedTwoThreeUnit.negThree k) →
          (∀ i ∈ s, IsTwoLayerAt k (term i)) →
          k < twoSidedSparseEnvelope C0 D := by
  exact h

end Arithmetic
end Collatz3
