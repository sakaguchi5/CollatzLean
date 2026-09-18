import CollatzLean.Collatz3.Mersenne.NoHoleMersenneQuotientProof
import CollatzLean.Collatz3.Mersenne.SmallHoleModular
import CollatzLean.Collatz3.Arithmetic.ModTwoPow
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: small-hole exit-depth rigidity

hole 1/2 の exact normal form について、低位 bit だけで決まる `r` を先に固定する。

狙いは全ケースをここで解くことではない。mod 4 / mod 8 で即座に決まる
non-resonant branch を exact に閉じ、有限 modular lifting が本当に必要な
低位 resonance だけを残す。
-/

namespace Collatz3
namespace Mersenne

/-! ## 小さい 2冪法の helper -/

/--
`ZMod 4` では `4k = 0`。
-/
@[simp]
theorem four_mul_intCast_eq_zero_zmod4
    (k : ℤ) :
    (4 : ZMod 4) * (k : ZMod 4) = 0 := by
  have h4 : (4 : ZMod 4) = 0 := by
    decide
  rw [h4]
  simp

/--
4 の整数倍に 2 を足したものは `ZMod 4` で 2。
-/
@[simp]
theorem four_mul_add_two_eq_two_zmod4
    (k : ℤ) :
    ((4 * k + 2 : ℤ) : ZMod 4) = 2 := by
  push_cast
  simp

/-- `ZMod 4` では `-2 = 2`。一般補題の simp 用標準形。 -/
@[simp]
theorem neg_two_eq_two_zmod4 :
    -(2 : ZMod 4) = 2 := by
  decide

/-- `ZMod 4` では `-6 = 2`。一般補題の simp 用標準形。 -/
@[simp]
theorem neg_six_eq_two_zmod4 :
    -(6 : ZMod 4) = 2 := by
  decide

/-- `ZMod 4` では `-1 ≠ 1`。mod 4 contradiction の標準形。 -/
private theorem neg_one_ne_one_zmod4 :
    (-1 : ZMod 4) ≠ 1 := by
  decide

/-- `ZMod 4` では `-3 ≠ 3`。mod 4 contradiction の標準形。 -/
private theorem neg_three_ne_three_zmod4 :
    (-3 : ZMod 4) ≠ 3 := by
  decide

/-- `ZMod 4` では `-9 ≠ 1`。mod 4 contradiction の標準形。 -/
private theorem neg_nine_ne_one_zmod4 :
    (-9 : ZMod 4) ≠ 1 := by
  decide

/-- `ZMod 8` では `-3 ≠ 1`。mod 8 contradiction の標準形。 -/
private theorem neg_three_ne_one_zmod8 :
    (-3 : ZMod 8) ≠ 1 := by
  decide

private theorem two_pow_zmod4_eq_zero_of_two_le
    {e : ℕ} (h : 2 ≤ e) :
    (2 : ZMod 4) ^ e = 0 := by
  simpa using ZMod.natCast_pow_eq_zero_of_le 2 h

private theorem two_pow_zmod8_eq_zero_of_three_le
    {e : ℕ} (h : 3 ≤ e) :
    (2 : ZMod 8) ^ e = 0 := by
  simpa using ZMod.natCast_pow_eq_zero_of_le 2 h

private theorem three_pow_zmod4_of_even
    {k : ℕ} (hk : k % 2 = 0) :
    (3 : ZMod 4) ^ k = 1 := by
  have hp : (3 : ZMod 4) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 4) (e := k) hp]
  simp [hk]

private theorem three_pow_zmod4_of_odd
    {k : ℕ} (hk : k % 2 = 1) :
    (3 : ZMod 4) ^ k = 3 := by
  have hp : (3 : ZMod 4) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 4) (e := k) hp]
  simp [hk]

private theorem three_pow_zmod8_of_even
    {k : ℕ} (hk : k % 2 = 0) :
    (3 : ZMod 8) ^ k = 1 := by
  have hp : (3 : ZMod 8) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := k) hp]
  simp [hk]

private theorem three_pow_zmod8_of_odd
    {k : ℕ} (hk : k % 2 = 1) :
    (3 : ZMod 8) ^ k = 3 := by
  have hp : (3 : ZMod 8) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := k) hp]
  simp [hk]

/-- `L>0` なら `2*(2^L-1)=2 mod 4`。 -/
private theorem two_mul_mersenne_zmod4
    {L : ℕ} (hL : 0 < L) :
    (2 : ZMod 4) * ((2 : ZMod 4) ^ L - 1) = 2 := by
  by_cases hL1 : L = 1
  · subst L
    norm_num
  · have hL2 : 2 ≤ L := by omega
    have hPow : (2 : ZMod 4) ^ L = 0 := by
      simpa using
        (ZMod.natCast_pow_eq_zero_of_le 2 hL2 :
          (2 : ZMod 4) ^ L = 0)
    rw [hPow]
    simp



/-- one-hole target factor も bit 0 が欠けないので、2倍すると mod 4 で常に2。 -/
private theorem two_mul_targetOne_zmod4
    {L b : ℕ}
    (hb : 0 < b) (hbL : b < L) :
    (2 : ZMod 4) *
      ((2 : ZMod 4) ^ L - 1 - (2 : ZMod 4) ^ b) = 2 := by
  have hL2 : 2 ≤ L := by omega
  rw [two_pow_zmod4_eq_zero_of_two_le hL2]
  by_cases hb1 : b = 1
  · subst b
    norm_num
    simp
  · have hb2 : 2 ≤ b := by omega
    rw [two_pow_zmod4_eq_zero_of_two_le hb2]
    norm_num
    simp

/-- two-hole target factorも odd なので、2倍すると mod 4 で2。 -/
private theorem two_mul_targetTwo_zmod4
    {L a b : ℕ}
    (ha : 0 < a) (hab : a < b) (hbL : b < L) :
    (2 : ZMod 4) *
      ((2 : ZMod 4) ^ L - 1 -
        (2 : ZMod 4) ^ a - (2 : ZMod 4) ^ b) = 2 := by
  have hL2 : 2 ≤ L := by omega
  have hb2 : 2 ≤ b := by omega
  rw [two_pow_zmod4_eq_zero_of_two_le hL2,
      two_pow_zmod4_eq_zero_of_two_le hb2]
  by_cases ha1 : a = 1
  · subst a
    norm_num
    simp
  · have ha2 : 2 ≤ a := by omega
    rw [two_pow_zmod4_eq_zero_of_two_le ha2]
    norm_num
    simp

/-! ## source one-hole / split two-hole -/

/-- even `k`, source hole `a≥2` では exit depth は exact に1。 -/
theorem SourceOneHoleEquation.exitDepth_eq_one_of_even_of_two_le_hole
    {k n r L a : ℕ}
    (hk : k % 2 = 0)
    (ha : 2 ≤ a) (han : a < n)
    (hr : 0 < r)
    (hEq : SourceOneHoleEquation k n r L a) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hn2 : 2 ≤ n := by omega
  have hMod := hEq.to_mod 4
  unfold SourceOneHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_even hk,
      two_pow_zmod4_eq_zero_of_two_le hn2,
      two_pow_zmod4_eq_zero_of_two_le ha,
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_one_ne_one_zmod4 hMod).elim

/-- even `k`, `a=1`, `n≥3` では exit depth は exact に2。 -/
theorem SourceOneHoleEquation.exitDepth_eq_two_of_even_hole_one
    {k n r L : ℕ}
    (hk : k % 2 = 0)
    (hn : 3 ≤ n) (hr : 0 < r) (hL : 0 < L)
    (hEq : SourceOneHoleEquation k n r L 1) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold SourceOneHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_even hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_mul_mersenne_zmod4 hL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold SourceOneHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_even hk,
        two_pow_zmod8_eq_zero_of_three_le hn,
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/-- odd `k`, source hole `a=1` では exit depth は1。 -/
theorem SourceOneHoleEquation.exitDepth_eq_one_of_odd_hole_one
    {k n r L : ℕ}
    (hk : k % 2 = 1)
    (hn : 2 ≤ n) (hr : 0 < r)
    (hEq : SourceOneHoleEquation k n r L 1) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hMod := hEq.to_mod 4
  unfold SourceOneHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_odd hk,
      two_pow_zmod4_eq_zero_of_two_le hn,
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_nine_ne_one_zmod4 hMod).elim

/-- odd `k`, source hole `a≥3` では exit depth は2。 -/
theorem SourceOneHoleEquation.exitDepth_eq_two_of_odd_of_three_le_hole
    {k n r L a : ℕ}
    (hk : k % 2 = 1)
    (ha : 3 ≤ a) (han : a < n)
    (hr : 0 < r) (hL : 0 < L)
    (hEq : SourceOneHoleEquation k n r L a) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold SourceOneHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_odd hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ a),
        two_mul_mersenne_zmod4 hL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold SourceOneHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_odd hk,
        two_pow_zmod8_eq_zero_of_three_le (by omega : 3 ≤ n),
        two_pow_zmod8_eq_zero_of_three_le ha,
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/-- `n=2,a=1` は no-hole source-one equation そのもの。 -/
theorem SourceOneHoleEquation.source_two_hole_one_to_noHole
    {k r L : ℕ}
    (hEq : SourceOneHoleEquation k 2 r L 1) :
    NoHoleEquation k 1 r L := by
  unfold SourceOneHoleEquation at hEq
  unfold NoHoleEquation
  norm_num at hEq ⊢
  exact hEq

/-- `n=2,a=1` の source-one-hole は既知 no-hole 四解から二解に完全分類される。 -/
theorem SourceOneHoleEquation.source_two_hole_one_classification
    {k r L : ℕ}
    (hk : 0 < k) (hr : 0 < r) (hL : 0 < L)
    (hEq : SourceOneHoleEquation k 2 r L 1) :
    (k = 1 ∧ r = 1 ∧ L = 1) ∨
    (k = 2 ∧ r = 3 ∧ L = 1) := by
  have hNo : NoHoleEquation k 1 r L :=
    hEq.source_two_hole_one_to_noHole
  rcases noHoleCompleteClassification k 1 r L hk (by omega) hr hL hNo with
    h | h | h | h
  · exact Or.inl ⟨h.1, h.2.2.1, h.2.2.2⟩
  · omega
  · exact Or.inr ⟨h.1, h.2.2.1, h.2.2.2⟩
  · omega

/-- target-one-hole の `n=2` は depth を一つ増やした `n=1` 型。 -/
theorem TargetOneHoleEquation.source_two_to_source_one
    {k r L b : ℕ}
    (hEq : TargetOneHoleEquation k 2 r L b) :
    TargetOneHoleEquation (k + 1) 1 r L b := by
  unfold TargetOneHoleEquation at hEq ⊢
  norm_num at hEq ⊢
  rw [pow_succ]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hEq

/-- split-two-hole の `n=2,a=1` は target-one-hole の `n=1` 型へ落ちる。 -/
theorem SplitTwoHoleEquation.source_two_hole_one_to_targetOne
    {k r L b : ℕ}
    (hEq : SplitTwoHoleEquation k 2 r L 1 b) :
    TargetOneHoleEquation k 1 r L b := by
  unfold SplitTwoHoleEquation at hEq
  unfold TargetOneHoleEquation
  norm_num at hEq ⊢
  exact hEq

/-- split-two-hole の exit depth は source hole 側だけで同じ非共鳴分類を持つ。 -/
theorem SplitTwoHoleEquation.exitDepth_eq_one_of_even_of_two_le_sourceHole
    {k n r L a b : ℕ}
    (hk : k % 2 = 0)
    (ha : 2 ≤ a) (han : a < n)
    (hr : 0 < r)
    (hEq : SplitTwoHoleEquation k n r L a b) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hMod := hEq.to_mod 4
  unfold SplitTwoHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_even hk,
      two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
      two_pow_zmod4_eq_zero_of_two_le ha,
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_one_ne_one_zmod4 hMod).elim

/-- odd `k`, split source hole `a=1` では `r=1`。 -/
theorem SplitTwoHoleEquation.exitDepth_eq_one_of_odd_sourceHole_one
    {k n r L b : ℕ}
    (hk : k % 2 = 1)
    (hn : 2 ≤ n) (hr : 0 < r)
    (hEq : SplitTwoHoleEquation k n r L 1 b) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hMod := hEq.to_mod 4
  unfold SplitTwoHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_odd hk,
      two_pow_zmod4_eq_zero_of_two_le hn,
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_nine_ne_one_zmod4 hMod).elim

/-- even `k`, split source hole `a=1`, `n≥3` では `r=2`。 -/
theorem SplitTwoHoleEquation.exitDepth_eq_two_of_even_sourceHole_one
    {k n r L b : ℕ}
    (hk : k % 2 = 0)
    (hn : 3 ≤ n) (hr : 0 < r)
    (hb : 0 < b) (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L 1 b) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold SplitTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_even hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_mul_targetOne_zmod4 hb hbL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold SplitTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_even hk,
        two_pow_zmod8_eq_zero_of_three_le hn,
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/-- odd `k`, split source hole `a≥3` では `r=2`。 -/
theorem SplitTwoHoleEquation.exitDepth_eq_two_of_odd_of_three_le_sourceHole
    {k n r L a b : ℕ}
    (hk : k % 2 = 1)
    (ha : 3 ≤ a) (han : a < n)
    (hr : 0 < r)
    (hb : 0 < b) (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L a b) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold SplitTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_odd hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ a),
        two_mul_targetOne_zmod4 hb hbL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold SplitTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_odd hk,
        two_pow_zmod8_eq_zero_of_three_le (by omega : 3 ≤ n),
        two_pow_zmod8_eq_zero_of_three_le ha,
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/-! ## target one/two-hole: large source では source 側だけで r が決まる -/

/-- target one-hole, `n≥3`, even `k` なら `r=1`。 -/
theorem TargetOneHoleEquation.exitDepth_eq_one_of_largeSource_even
    {k n r L b : ℕ}
    (hk : k % 2 = 0)
    (hn : 3 ≤ n) (hr : 0 < r)
    (hEq : TargetOneHoleEquation k n r L b) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hMod := hEq.to_mod 4
  unfold TargetOneHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_even hk,
      two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_one_ne_one_zmod4 hMod).elim

/-- target one-hole, `n≥3`, odd `k` なら `r=2`。 -/
theorem TargetOneHoleEquation.exitDepth_eq_two_of_largeSource_odd
    {k n r L b : ℕ}
    (hk : k % 2 = 1)
    (hn : 3 ≤ n) (hr : 0 < r)
    (hb : 0 < b) (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold TargetOneHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_odd hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_mul_targetOne_zmod4 hb hbL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold TargetOneHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_odd hk,
        two_pow_zmod8_eq_zero_of_three_le hn,
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/-- target two-hole, `n≥3`, even `k` なら `r=1`。 -/
theorem TargetTwoHoleEquation.exitDepth_eq_one_of_largeSource_even
    {k n r L a b : ℕ}
    (hk : k % 2 = 0)
    (hn : 3 ≤ n) (hr : 0 < r)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hMod := hEq.to_mod 4
  unfold TargetTwoHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_even hk,
      two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_one_ne_one_zmod4 hMod).elim

/-- target two-hole, `n≥3`, odd `k` なら `r=2`。 -/
theorem TargetTwoHoleEquation.exitDepth_eq_two_of_largeSource_odd
    {k n r L a b : ℕ}
    (hk : k % 2 = 1)
    (hn : 3 ≤ n) (hr : 0 < r)
    (ha : 0 < a) (hab : a < b) (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold TargetTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_odd hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_mul_targetTwo_zmod4 ha hab hbL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold TargetTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_odd hk,
        two_pow_zmod8_eq_zero_of_three_le hn,
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/-! ## source two-hole: non-resonant branches -/

/-- even `k`, smallest source hole `a≥2` では `r=1`。 -/
theorem SourceTwoHoleEquation.exitDepth_eq_one_of_even_of_two_le_firstHole
    {k n r L a b : ℕ}
    (hk : k % 2 = 0)
    (ha : 2 ≤ a) (hab : a < b) (hbn : b < n)
    (hr : 0 < r)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hMod := hEq.to_mod 4
  unfold SourceTwoHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_even hk,
      two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
      two_pow_zmod4_eq_zero_of_two_le ha,
      two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ b),
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_one_ne_one_zmod4 hMod).elim

/-- even `k`, first hole 1, second hole `b≥3` では `r=2`。 -/
theorem SourceTwoHoleEquation.exitDepth_eq_two_of_even_one_then_three
    {k n r L b : ℕ}
    (hk : k % 2 = 0)
    (hb : 3 ≤ b) (hbn : b < n)
    (hr : 0 < r) (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L 1 b) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold SourceTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_even hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ b),
        two_mul_mersenne_zmod4 hL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold SourceTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_even hk,
        two_pow_zmod8_eq_zero_of_three_le (by omega : 3 ≤ n),
        two_pow_zmod8_eq_zero_of_three_le hb,
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/-- odd `k`, first source hole 1 では `r=1`。 -/
theorem SourceTwoHoleEquation.exitDepth_eq_one_of_odd_firstHole_one
    {k n r L b : ℕ}
    (hk : k % 2 = 1)
    (hbn : b < n) (hb : 2 ≤ b)
    (hr : 0 < r)
    (hEq : SourceTwoHoleEquation k n r L 1 b) :
    r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hMod := hEq.to_mod 4
  unfold SourceTwoHoleModEquation at hMod
  try simp only [pow_one] at hMod
  rw [three_pow_zmod4_of_odd hk,
      two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
      two_pow_zmod4_eq_zero_of_two_le hb,
      two_pow_zmod4_eq_zero_of_two_le hr2] at hMod
  norm_num at hMod
  exact (neg_nine_ne_one_zmod4 hMod).elim

/-- odd `k`, smallest source hole `a≥3` では `r=2`。 -/
theorem SourceTwoHoleEquation.exitDepth_eq_two_of_odd_of_three_le_firstHole
    {k n r L a b : ℕ}
    (hk : k % 2 = 1)
    (ha : 3 ≤ a) (hab : a < b) (hbn : b < n)
    (hr : 0 < r) (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    r = 2 := by
  by_cases hr1 : r = 1
  · subst r
    have hMod := hEq.to_mod 4
    unfold SourceTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod4_of_odd hk,
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ n),
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ a),
        two_pow_zmod4_eq_zero_of_two_le (by omega : 2 ≤ b),
        two_mul_mersenne_zmod4 hL] at hMod
    norm_num at hMod
    exact (neg_three_ne_three_zmod4 hMod).elim
  · have hr2 : 2 ≤ r := by omega
    by_contra hrNe2
    have hr3 : 3 ≤ r := by omega
    have hMod := hEq.to_mod 8
    unfold SourceTwoHoleModEquation at hMod
    try simp only [pow_one] at hMod
    rw [three_pow_zmod8_of_odd hk,
        two_pow_zmod8_eq_zero_of_three_le (by omega : 3 ≤ n),
        two_pow_zmod8_eq_zero_of_three_le ha,
        two_pow_zmod8_eq_zero_of_three_le (by omega : 3 ≤ b),
        two_pow_zmod8_eq_zero_of_three_le hr3] at hMod
    norm_num at hMod
    exact (neg_three_ne_one_zmod8 hMod).elim

/--
source-two-hole で mod 4/8 だけでは残る二つの低位 resonance。

* even `k`: first/second holes = `(1,2)`
* odd `k`: first hole = `2`

後段の tail/loop sieve はまずここを重点的に処理すればよい。
-/
def SourceTwoHoleLowResonance
    (k a b : ℕ) : Prop :=
  (k % 2 = 0 ∧ a = 1 ∧ b = 2) ∨
  (k % 2 = 1 ∧ a = 2)

/-- source-one/split で残る主要 resonance は odd `k`, source hole `a=2`。 -/
def SourceOneHoleLowResonance
    (k a : ℕ) : Prop :=
  k % 2 = 1 ∧ a = 2

end Mersenne
end Collatz3
