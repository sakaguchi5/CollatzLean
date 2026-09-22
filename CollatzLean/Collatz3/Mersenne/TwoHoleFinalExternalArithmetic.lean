import CollatzLean.Collatz3.Mersenne.TwoHoleFinalInternal
import CollatzLean.Collatz3.Mersenne.TwoHoleFullExternalDerived

/-!
# Collatz3 Mersenne: A2 の最終外部算術 interface

研究途中で使っていた `...Escape → False` / `...ResidualArithmetic → False` を、
A1 (`TargetOneHoleExternalArithmetic`) と同じ証明分業へ置き換える。

最終 interface では、各 genuinely deep branch に対して

1. 外部の explicit/effective 数論が depth `k` を有限上界 `K` 未満へ落とす。
2. 同じ `K` 未満の bounded residual を finite certificate が排除する。

という二段だけを仮定する。

`K` の具体値をこの repository が先回りして捏造しないため、split / target では
「ある自然数 `K` と、その `K` に対する bound + finite sieve」を一組として受け取る。
Chim / Gouillon / Stephan の特殊化で数値上界が確定した時点で、その witness を
より具体的な定数へ置き換えられる。

source-even だけは内部 theorem `2^392 ∣ k` が既にあるので、外部側は
`k < 2^392` の特殊 corollary 一本で閉じる。

このファイルの public API は `ResidualArithmetic` を要求しない。
旧 interface への変換は互換性のための derived theorem としてのみ残す。
-/

namespace Collatz3
namespace Mersenne

/-! ## 共通: effective bound + bounded finite sieve -/

/--
自然数 depth で添字付けされた branch `P` を閉じる A1 型 package。

witness `K` に対して

* 第1成分が explicit/effective depth bound `P k → k<K`,
* 第2成分が bounded residual の finite sieve `P k → k<K → False`

を表す。
-/
def EffectiveDepthBoundAndFiniteSieve (P : ℕ → Prop) : Prop :=
  ∃ K : ℕ,
    (∀ {k : ℕ}, P k → k < K) ∧
    (∀ {k : ℕ}, P k → k < K → False)

namespace EffectiveDepthBoundAndFiniteSieve

/-- bound と bounded finite sieve を合成すれば branch 自体は不可能。 -/
theorem impossible
    {P : ℕ → Prop}
    (A : EffectiveDepthBoundAndFiniteSieve P)
    {k : ℕ}
    (h : P k) :
    False := by
  rcases A with ⟨K, hBound, hFinite⟩
  exact hFinite h (hBound h)

end EffectiveDepthBoundAndFiniteSieve

/-! ## 外部 theorem が受け取る exact branch predicate -/

/--
split odd `a=2` の finite internalization 後に残る exact branch。

`r=4`, `k≡1 (mod 1944)` と三 residue family はすべて内部証明済みなので、
外部二対数定理はこの predicate だけを処理すればよい。
-/
def SplitOddA2FinalCase (k : ℕ) : Prop :=
  ∃ n L b : ℕ,
    7 ≤ k ∧
    k % 2 = 1 ∧
    k % 1944 = 1 ∧
    SplitOddA2ResidueClass n L b ∧
    SplitTwoHoleEquation k n 4 L 2 b

/-- even split regular (`r=1`) の exact final branch。 -/
def SplitRegularEvenFinalCase (k : ℕ) : Prop :=
  ∃ n L a b : ℕ,
    7 ≤ k ∧
    k % 2 = 0 ∧
    2 ≤ a ∧ a < n ∧
    0 < b ∧ b < L ∧
    SplitTwoHoleEquation k n 1 L a b

/-- odd split regular (`r=2`) の exact final branch。 -/
def SplitRegularOddFinalCase (k : ℕ) : Prop :=
  ∃ n L a b : ℕ,
    7 ≤ k ∧
    k % 2 = 1 ∧
    3 ≤ a ∧ a < n ∧
    0 < b ∧ b < L ∧
    SplitTwoHoleEquation k n 2 L a b

/-- target-two `n=1` の genuinely interior branch。 -/
def TargetTwoSourceOneFinalCase (k : ℕ) : Prop :=
  ∃ r L a b : ℕ,
    7 ≤ k ∧
    0 < r ∧
    0 < a ∧ a < b ∧
    b + 1 < L ∧
    TargetTwoHoleEquation k 1 r L a b

/-- target-two `n≥4`, even depth (`r=1`) branch。 -/
def TargetTwoLargeEvenFinalCase (k : ℕ) : Prop :=
  ∃ n L a b : ℕ,
    7 ≤ k ∧
    k % 2 = 0 ∧
    4 ≤ n ∧
    0 < a ∧ a < b ∧
    b + 1 < L ∧
    TargetTwoHoleEquation k n 1 L a b

/-- target-two `n≥4`, odd depth (`r=2`) branch。 -/
def TargetTwoLargeOddFinalCase (k : ℕ) : Prop :=
  ∃ n L a b : ℕ,
    7 ≤ k ∧
    k % 2 = 1 ∧
    4 ≤ n ∧
    0 < a ∧ a < b ∧
    b + 1 < L ∧
    TargetTwoHoleEquation k n 2 L a b

/-! ## source / split / target ごとの A1 型 package -/

/--
source-two で外部に残るのは even resonance の explicit bound 一本だけ。

内部で `2^392 ∣ k` が証明済みなので、Chim 型特殊 corollaryとして
`k < 2^392` を受け取れば finite sieve なしで矛盾する。
source-odd resonance は `TwoHoleFiniteInternal` で完全に内部排除済み。
-/
structure SourceTwoFinalExternalArithmetic : Prop where
  even_resonance_bound :
    ∀ {k n r L : ℕ},
      7 ≤ k →
      SourceTwoHoleEquation k n r L 1 2 →
      k < 2 ^ 392

/--
split-two の外部算術 package。

* odd `a=2`: M₅ finite classification 後の三 residue family。
* regular even: `r=1`, `a≥2`。
* regular odd: `r=2`, `a≥3`。

各 field は同じ witness `K` に対する「depth bound + bounded finite sieve」である。
`regularEven_secondCut` / `regularOdd_secondCut` の三分岐は bound を証明する側の
内部事情なので、最終 interface には露出させない。
-/
structure SplitTwoFinalExternalArithmetic : Prop where
  odd_a_two :
    EffectiveDepthBoundAndFiniteSieve SplitOddA2FinalCase
  regular_even :
    EffectiveDepthBoundAndFiniteSieve SplitRegularEvenFinalCase
  regular_odd :
    EffectiveDepthBoundAndFiniteSieve SplitRegularOddFinalCase

/--
target-two の最終外部算術 package。

* `n=1`: 内部で `period-break≤6` まで証明済み。
* `n≥4`: 内部で geometric/gcd/valuation と `period-break≤5` まで証明済み。

`n=2` は `n=1,k+1` へ exact shift、`n=3` は純有限 M₅ certificate で内部排除済み。
従って残る三枝だけを A1 型 bound+sieve で受け取る。
-/
structure TargetTwoFinalExternalArithmetic : Prop where
  source_one :
    EffectiveDepthBoundAndFiniteSieve TargetTwoSourceOneFinalCase
  large_even :
    EffectiveDepthBoundAndFiniteSieve TargetTwoLargeEvenFinalCase
  large_odd :
    EffectiveDepthBoundAndFiniteSieve TargetTwoLargeOddFinalCase

/--
A2 の最終外部算術 package。

この structure 自体には generic six-term S-unit 仮定や direct residual-impossible field は無い。
外部 theorem の役割は source/split/target の具体的 branch に対する
explicit/effective depth bound と bounded finite sieve だけである。
-/
structure TwoHoleFinalExternalArithmetic : Prop where
  source : SourceTwoFinalExternalArithmetic
  split : SplitTwoFinalExternalArithmetic
  target : TargetTwoFinalExternalArithmetic

/-! ## source-even: external bound + internal divisibility -/

/-- source-even resonance は `k<2^392` と内部 `2^392∣k` の衝突で排除される。 -/
theorem SourceTwoFinalExternalArithmetic.even_resonance_impossible
    (A : SourceTwoFinalExternalArithmetic)
    {k n r L : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 1 2) :
    False := by
  have hDvd :=
    hEq.evenLowResonance_twoPow392_dvd_depth hk7
  have hLt := A.even_resonance_bound hk7 hEq
  have hLe : 2 ^ 392 ≤ k :=
    Nat.le_of_dvd (by omega : 0 < k) hDvd
  omega

/-! ## 新しい最終 package から旧 deep/residual API を derived theorem として回収 -/

/--
最終 A2 package から、互換用の旧 `TwoHoleDeepKnownArithmetic` を構成する。

旧 interface の3本の split odd-a2 `Escape` は、最終 package では一つの
A1 型 bound+sieve に統合される。
-/
theorem TwoHoleFinalExternalArithmetic.toDeepKnownArithmetic
    (A : TwoHoleFinalExternalArithmetic) :
    TwoHoleDeepKnownArithmetic where
  source_even_chim := by
    intro k n r L hk7 _hK _hN _hR _hT hEq
    exact A.source.even_resonance_impossible hk7 hEq
  split_source_chim := by
    intro k n L b hk7 hkOdd hk1944 hResidue _hlt hEq
    exact EffectiveDepthBoundAndFiniteSieve.impossible
      A.split.odd_a_two
      ⟨n, L, b, hk7, hkOdd, hk1944, hResidue, hEq⟩
  split_target_chim := by
    intro k n L b hk7 hkOdd hk1944 hResidue _heq hEq
    exact EffectiveDepthBoundAndFiniteSieve.impossible
      A.split.odd_a_two
      ⟨n, L, b, hk7, hkOdd, hk1944, hResidue, hEq⟩
  split_three_two_gouillon := by
    intro k n L b hk7 hkOdd hk1944 hResidue _hgt hEq
    exact EffectiveDepthBoundAndFiniteSieve.impossible
      A.split.odd_a_two
      ⟨n, L, b, hk7, hkOdd, hk1944, hResidue, hEq⟩

/--
最終 split package から旧 regular residual package を回収する。
旧 direct-`False` field は最終的には bound+sieve の合成 theorem に過ぎない。
-/
theorem SplitTwoFinalExternalArithmetic.toRegularResidualArithmetic
    (A : SplitTwoFinalExternalArithmetic) :
    SplitTwoRegularResidualArithmetic where
  even_impossible := by
    intro k n L a b hk7 hkEven ha2 han hb0 hbL hEq
    exact EffectiveDepthBoundAndFiniteSieve.impossible
      A.regular_even
      ⟨n, L, a, b, hk7, hkEven, ha2, han, hb0, hbL, hEq⟩
  odd_impossible := by
    intro k n L a b hk7 hkOdd ha3 han hb0 hbL hEq
    exact EffectiveDepthBoundAndFiniteSieve.impossible
      A.regular_odd
      ⟨n, L, a, b, hk7, hkOdd, ha3, han, hb0, hbL, hEq⟩

/--
最終 target package から、finite 内部化後の旧 target residual package を回収する。

large-source は既存 low-bit theorem で `r=1/2` を内部的に固定してから、
even/odd の A1 型 package へ送る。
-/
theorem TargetTwoFinalExternalArithmetic.toReducedResidualArithmetic
    (A : TargetTwoFinalExternalArithmetic) :
    TargetTwoResidualArithmeticReduced where
  source_one_impossible := by
    intro k r L a b hk7 hr ha0 hab hbDeep hEq
    exact EffectiveDepthBoundAndFiniteSieve.impossible
      A.source_one
      ⟨r, L, a, b, hk7, hr, ha0, hab, hbDeep, hEq⟩
  large_source_impossible := by
    intro k n r L a b hk7 hn4 hr ha0 hab hbDeep hEq
    rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
    · have hr1 :=
        hEq.exitDepth_eq_one_of_largeSource_even
          hkEven (by omega : 3 ≤ n) hr
      subst r
      exact EffectiveDepthBoundAndFiniteSieve.impossible
        A.large_even
        ⟨n, L, a, b, hk7, hkEven, hn4, ha0, hab, hbDeep, hEq⟩
    · have hr2 :=
        hEq.exitDepth_eq_two_of_largeSource_odd
          hkOdd (by omega : 3 ≤ n) hr ha0 hab (by omega : b < L)
      subst r
      exact EffectiveDepthBoundAndFiniteSieve.impossible
        A.large_odd
        ⟨n, L, a, b, hk7, hkOdd, hn4, ha0, hab, hbDeep, hEq⟩

/--
最終 A2 package から互換用 `TwoHoleResidualArithmeticReduced` を構成する。
ここで residual は外部仮定ではなく、A1 型 package からの derived theorem である。
-/
theorem TwoHoleFinalExternalArithmetic.toResidualArithmeticReduced
    (A : TwoHoleFinalExternalArithmetic) :
    TwoHoleResidualArithmeticReduced where
  split_regular := A.split.toRegularResidualArithmetic
  target := A.target.toReducedResidualArithmetic

/-! ## A1 + final A2 arithmetic から従来 A2 / 最終 lower bound へ -/

/--
A1 と最終 A2 算術 package から、従来の `TwoHoleFullExternalArithmetic` を構成する。

この theorem が最終証明で使う A2 bridge。
`ResidualArithmetic` や old `...Escape` をユーザーが直接与える必要はない。
-/
theorem twoHoleFullExternalArithmetic_of_A1_finalA2
    (A1 : TargetOneHoleExternalArithmetic)
    (A2 : TwoHoleFinalExternalArithmetic) :
    TwoHoleFullExternalArithmetic := by
  exact twoHoleFullExternalArithmetic_of_reduced
    A1 A2.toDeepKnownArithmetic A2.toResidualArithmeticReduced

/-- A1 + final A2 算術から `AtMostTwoHoleDepthBound` を得る。 -/
theorem atMostTwoHoleDepthBound_of_A1_finalA2
    (A1 : TargetOneHoleExternalArithmetic)
    (A2 : TwoHoleFinalExternalArithmetic) :
    AtMostTwoHoleDepthBound := by
  exact atMostTwoHoleDepthBound_of_external
    A1 (twoHoleFullExternalArithmetic_of_A1_finalA2 A1 A2)

/-- A1 + final A2 算術を small-hole lower bound へ直接接続する。 -/
theorem blockSparsePow3LowerBound_smallHole_of_A1_finalA2
    (A1 : TargetOneHoleExternalArithmetic)
    (A2 : TwoHoleFinalExternalArithmetic) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole
    noHoleCompleteClassification
    (atMostOneHoleDepthBound_of_external A1)
    (atMostTwoHoleDepthBound_of_A1_finalA2 A1 A2)

end Mersenne
end Collatz3
