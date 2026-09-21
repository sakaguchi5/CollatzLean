import CollatzLean.Collatz3.Mersenne.TwoHoleDeepArithmeticInterfaces
import CollatzLean.Collatz3.Mersenne.TargetOneHoleFourBranchClosure

/-!
# Collatz3 Mersenne: source / split / target two-hole 深部 closure

`TwoHoleDeepArithmeticInterfaces` で分離した入力から、Collatz 固有の case split と
既存内部 theorem を組み合わせて large-depth branch を閉じる。

このファイルの derived theorem 自身は新しい外部仮定を追加しない。
-/

namespace Collatz3
namespace Mersenne

/--
source-two は、既存の low-resonance reduction の後では

* even `(a,b)=(1,2)` → Chim corollary,
* odd `a=2` → `M₄*2593` finite certificate

の二本だけで `k≥7` を完全排除できる。
-/
theorem SourceTwoHoleEquation.largeDepth_impossible_of_knownArithmetic
    (K : TwoHoleKnownArithmetic)
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    False := by
  have hRed :=
    hEq.largeDepth_lowResonance_m4_reduction
      hk7 ha0 hab hbn hr hL
  rcases hRed.2 with hEven | hOdd
  · rcases hEven with
      ⟨_hkEven, ha1, hb2, hK, hN, hR, hT⟩
    subst a
    subst b
    exact K.source_even_chim hk7 hK hN hR hT hEq
  · rcases hOdd with
      ⟨hkOdd, ha2, _J, _N, _R, _T, _B,
        _hJ, _hN, _hR, _hT, _hB, _hState⟩
    subst a
    exact K.source_odd_m5 hk7 hkOdd (by omega) hbn hr hL hEq

/--
split odd `a=2` resonance は M₅ finite reduction の後、`n` と `b+4` の三分岐を
Chim / Gouillon の特殊 corollary へ送れば `k≥7` を排除できる。
-/
theorem SplitTwoHoleEquation.oddA2_largeDepth_impossible_of_knownArithmetic
    (K : TwoHoleKnownArithmetic)
    {k n r L b : ℕ}
    (hk7 : 7 ≤ k)
    (hkOdd : k % 2 = 1)
    (hn2 : 2 < n)
    (hr : 0 < r)
    (hb0 : 0 < b)
    (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L 2 b) :
    False := by
  have hRed :=
    K.split_odd_a_two_m5
      hk7 hkOdd hn2 hr hb0 hbL hEq
  rcases hRed with ⟨hr4, hk1944, hResidue⟩
  subst r
  rcases lt_trichotomy n (b + 4) with hlt | heq | hgt
  · exact K.split_source_chim
      hk7 hkOdd hk1944 hResidue hlt hEq
  · exact K.split_target_chim
      hk7 hkOdd hk1944 hResidue heq hEq
  · exact K.split_three_two_gouillon
      hk7 hkOdd hk1944 hResidue hgt hEq

/--
split-two の `k≥7` を、既知/有限部分と二本の regular residual だけへ縮約する。

`a=1,n=2` は target-one へ peel して既存 A1 で閉じる。
`a=1,n≥3` は M₄ finite certificate、odd `a=2` は M₅ + two-log で閉じる。
従って genuinely residual なのは even `a≥2,r=1` と odd `a≥3,r=2` の二本だけ。
-/
theorem SplitTwoHoleEquation.largeDepth_impossible_of_known_and_residual
    (A1 : TargetOneHoleExternalArithmetic)
    (K : TwoHoleKnownArithmetic)
    (R : SplitTwoRegularResidualArithmetic)
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (han : a < n)
    (hr : 0 < r)
    (hb0 : 0 < b)
    (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L a b) :
    False := by
  rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
  · by_cases ha1 : a = 1
    · subst a
      by_cases hn2 : n = 2
      · subst n
        have hOne := hEq.source_two_hole_one_to_targetOne
        have hkLe :=
          hOne.depth_le_five_of_external
            A1 (by omega) hr hb0 hbL
        omega
      · have hn3 : 3 ≤ n := by omega
        have hr2 :=
          hEq.exitDepth_eq_two_of_even_sourceHole_one
            hkEven hn3 hr hb0 hbL
        subst r
        exact K.split_a_one_m4.even_impossible
          hk7 hkEven hn3 hb0 hbL hEq
    · have ha2 : 2 ≤ a := by omega
      have hr1 :=
        hEq.exitDepth_eq_one_of_even_of_two_le_sourceHole
          hkEven ha2 han hr
      subst r
      exact R.even_impossible
        hk7 hkEven ha2 han hb0 hbL hEq
  · by_cases ha1 : a = 1
    · subst a
      by_cases hn2 : n = 2
      · subst n
        have hOne := hEq.source_two_hole_one_to_targetOne
        have hkLe :=
          hOne.depth_le_five_of_external
            A1 (by omega) hr hb0 hbL
        omega
      · have hn3 : 3 ≤ n := by omega
        have hr1 :=
          hEq.exitDepth_eq_one_of_odd_sourceHole_one
            hkOdd (by omega) hr
        subst r
        exact K.split_a_one_m4.odd_impossible
          hk7 hkOdd hn3 hb0 hbL hEq
    · by_cases ha2 : a = 2
      · subst a
        exact hEq.oddA2_largeDepth_impossible_of_knownArithmetic
          K hk7 hkOdd (by omega) hr hb0 hbL
      · have ha3 : 3 ≤ a := by omega
        have hr2 :=
          hEq.exitDepth_eq_two_of_odd_of_three_le_sourceHole
            hkOdd ha3 han hr hb0 hbL
        subst r
        exact R.odd_impossible
          hk7 hkOdd ha3 han hb0 hbL hEq

/--
target-two では top target hole を A1 へ peel し、それ以外だけを residual package に残す。

したがって target residual は `b+1<L` の interior case に限定される。
-/
theorem TargetTwoHoleEquation.largeDepth_impossible_of_residual
    (A1 : TargetOneHoleExternalArithmetic)
    (R : TargetTwoResidualArithmetic)
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hn : 0 < n)
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    False := by
  by_cases hTop : b = L - 1
  · subst b
    have hOne := hEq.second_top_hole_to_targetOne (by omega)
    have hkLe :=
      hOne.depth_le_five_of_external
        A1 hn hr ha0 (by omega)
    omega
  · have hbInterior : L - 1 ≠ b := by
      intro h
      exact hTop h.symm
    have hbDeep : b + 1 < L := by omega
    by_cases hnSmall : n ≤ 3
    · exact R.small_source_impossible
        hk7 hn hnSmall hr ha0 hab hbDeep hEq
    · have hn4 : 4 ≤ n := by omega
      exact R.large_source_impossible
        hk7 hn4 hr ha0 hab hbDeep hEq

end Mersenne
end Collatz3
