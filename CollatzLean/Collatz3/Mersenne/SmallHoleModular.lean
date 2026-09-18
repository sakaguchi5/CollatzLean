import CollatzLean.Collatz3.Mersenne.SmallHoleExact
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: small-hole modular lifting

hole 0,1,2 の exact normal form を有限合同問題へ落とすための共通層。

modulus `m` に対して

`2^p2 = 1`, `3^p3 = 1` in `ZMod m`

という period certificate があれば、すべての exponent はそれぞれ
`mod p2`, `mod p3` に落とせる。

これにより、小 hole case の完全分類は

1. 整数 equation を `ZMod m` へ射影する。
2. exponent を有限 residue window へ縮約する。
3. modulus を段階的に強くして surviving residue classes を lift する。

という finite modular lifting に分離できる。
-/

namespace Collatz3
namespace Mersenne

/-- 一つの modulus における 2冪・3冪の period certificate。 -/
structure Pow23Periods (m p2 p3 : ℕ) : Prop where
  p2_pos : 0 < p2
  p3_pos : 0 < p3
  two_period : ((2 : ZMod m) ^ p2) = 1
  three_period : ((3 : ZMod m) ^ p3) = 1

/-- `a^p = 1` なら、`a^e` は exponent を `e % p` に置き換えても変わらない。 -/
theorem pow_eq_pow_mod_of_pow_eq_one
    {R : Type*} [Monoid R]
    (a : R) {p e : ℕ}
    (hPeriod : a ^ p = 1) :
    a ^ e = a ^ (e % p) := by
  have hDecomp : e % p + p * (e / p) = e := Nat.mod_add_div e p
  rw [← hDecomp, pow_add, pow_mul, hPeriod, one_pow, mul_one]
  simp

/--
`a^p = 1` かつ `p > 0` なら、
`a^e` は `p` 未満の exponent に縮約できる。
-/
theorem exists_reduced_pow_of_positive_period
    {R : Type*} [Monoid R]
    (a : R) {p e : ℕ}
    (hp : 0 < p)
    (hPeriod : a ^ p = 1) :
    ∃ r < p, a ^ e = a ^ r := by
  refine ⟨e % p, Nat.mod_lt e hp, ?_⟩
  exact pow_eq_pow_mod_of_pow_eq_one a hPeriod

namespace Pow23Periods

/-- 2冪 exponent の residue reduction。 -/
theorem two_pow_mod
    {m p2 p3 e : ℕ}
    (h : Pow23Periods m p2 p3) :
    (2 : ZMod m) ^ e = (2 : ZMod m) ^ (e % p2) :=
  pow_eq_pow_mod_of_pow_eq_one (2 : ZMod m) h.two_period

/-- 3冪 exponent の residue reduction。 -/
theorem three_pow_mod
    {m p2 p3 e : ℕ}
    (h : Pow23Periods m p2 p3) :
    (3 : ZMod m) ^ e = (3 : ZMod m) ^ (e % p3) :=
  pow_eq_pow_mod_of_pow_eq_one (3 : ZMod m) h.three_period

end Pow23Periods


/-- `mod 5` では 2,3 とも exponent period 4。 -/
theorem pow23Periods_mod5 : Pow23Periods 5 4 4 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- `mod 7` では `2` の period 3、`3` の period 6。 -/
theorem pow23Periods_mod7 : Pow23Periods 7 3 6 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/--
`mod 35` では両 exponent を period 12 の同じ有限 window に落とせる。
small-hole の最初の combined sieve として便利な modulus。
-/
theorem pow23Periods_mod35 : Pow23Periods 35 12 12 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- hole 0 equation の合同版。 -/
def NoHoleModEquation (m k n r L : ℕ) : Prop :=
  (3 : ZMod m) ^ k * ((2 : ZMod m) ^ n - 1) =
    (2 : ZMod m) ^ r * ((2 : ZMod m) ^ L - 1) + 1

/-- source one-hole equation の合同版。 -/
def SourceOneHoleModEquation (m k n r L a : ℕ) : Prop :=
  (3 : ZMod m) ^ k *
      ((2 : ZMod m) ^ n - 1 - (2 : ZMod m) ^ a) =
    (2 : ZMod m) ^ r * ((2 : ZMod m) ^ L - 1) + 1

/-- target one-hole equation の合同版。 -/
def TargetOneHoleModEquation (m k n r L b : ℕ) : Prop :=
  (3 : ZMod m) ^ k * ((2 : ZMod m) ^ n - 1) =
    (2 : ZMod m) ^ r *
      ((2 : ZMod m) ^ L - 1 - (2 : ZMod m) ^ b) + 1

/-- source two-hole equation の合同版。 -/
def SourceTwoHoleModEquation (m k n r L a b : ℕ) : Prop :=
  (3 : ZMod m) ^ k *
      ((2 : ZMod m) ^ n - 1 - (2 : ZMod m) ^ a - (2 : ZMod m) ^ b) =
    (2 : ZMod m) ^ r * ((2 : ZMod m) ^ L - 1) + 1

/-- split two-hole equation の合同版。 -/
def SplitTwoHoleModEquation (m k n r L a b : ℕ) : Prop :=
  (3 : ZMod m) ^ k *
      ((2 : ZMod m) ^ n - 1 - (2 : ZMod m) ^ a) =
    (2 : ZMod m) ^ r *
      ((2 : ZMod m) ^ L - 1 - (2 : ZMod m) ^ b) + 1

/-- target two-hole equation の合同版。 -/
def TargetTwoHoleModEquation (m k n r L a b : ℕ) : Prop :=
  (3 : ZMod m) ^ k * ((2 : ZMod m) ^ n - 1) =
    (2 : ZMod m) ^ r *
      ((2 : ZMod m) ^ L - 1 - (2 : ZMod m) ^ a - (2 : ZMod m) ^ b) + 1

/-- 整数 no-hole equation は任意 modulus 上の合同 equation を与える。 -/
theorem NoHoleEquation.to_mod
    {k n r L : ℕ}
    (h : NoHoleEquation k n r L)
    (m : ℕ) :
    NoHoleModEquation m k n r L := by
  unfold NoHoleEquation at h
  unfold NoHoleModEquation
  have hCast := congrArg (fun z : ℤ => (z : ZMod m)) h
  simpa using hCast

/-- source one-hole equation の modular projection。 -/
theorem SourceOneHoleEquation.to_mod
    {k n r L a : ℕ}
    (h : SourceOneHoleEquation k n r L a)
    (m : ℕ) :
    SourceOneHoleModEquation m k n r L a := by
  unfold SourceOneHoleEquation at h
  unfold SourceOneHoleModEquation
  have hCast := congrArg (fun z : ℤ => (z : ZMod m)) h
  simpa using hCast

/-- target one-hole equation の modular projection。 -/
theorem TargetOneHoleEquation.to_mod
    {k n r L b : ℕ}
    (h : TargetOneHoleEquation k n r L b)
    (m : ℕ) :
    TargetOneHoleModEquation m k n r L b := by
  unfold TargetOneHoleEquation at h
  unfold TargetOneHoleModEquation
  have hCast := congrArg (fun z : ℤ => (z : ZMod m)) h
  simpa using hCast

/-- source two-hole equation の modular projection。 -/
theorem SourceTwoHoleEquation.to_mod
    {k n r L a b : ℕ}
    (h : SourceTwoHoleEquation k n r L a b)
    (m : ℕ) :
    SourceTwoHoleModEquation m k n r L a b := by
  unfold SourceTwoHoleEquation at h
  unfold SourceTwoHoleModEquation
  have hCast := congrArg (fun z : ℤ => (z : ZMod m)) h
  simpa using hCast

/-- split two-hole equation の modular projection。 -/
theorem SplitTwoHoleEquation.to_mod
    {k n r L a b : ℕ}
    (h : SplitTwoHoleEquation k n r L a b)
    (m : ℕ) :
    SplitTwoHoleModEquation m k n r L a b := by
  unfold SplitTwoHoleEquation at h
  unfold SplitTwoHoleModEquation
  have hCast := congrArg (fun z : ℤ => (z : ZMod m)) h
  simpa using hCast

/-- target two-hole equation の modular projection。 -/
theorem TargetTwoHoleEquation.to_mod
    {k n r L a b : ℕ}
    (h : TargetTwoHoleEquation k n r L a b)
    (m : ℕ) :
    TargetTwoHoleModEquation m k n r L a b := by
  unfold TargetTwoHoleEquation at h
  unfold TargetTwoHoleModEquation
  have hCast := congrArg (fun z : ℤ => (z : ZMod m)) h
  simpa using hCast

/-- no-hole modular equation は有限 exponent residue window へ縮約できる。 -/
theorem NoHoleModEquation.reduce
    {m p2 p3 k n r L : ℕ}
    (hPeriods : Pow23Periods m p2 p3)
    (h : NoHoleModEquation m k n r L) :
    NoHoleModEquation m (k % p3) (n % p2) (r % p2) (L % p2) := by
  unfold NoHoleModEquation at h ⊢
  rw [← hPeriods.three_pow_mod (e := k),
      ← hPeriods.two_pow_mod (e := n),
      ← hPeriods.two_pow_mod (e := r),
      ← hPeriods.two_pow_mod (e := L)]
  exact h

/-- source one-hole modular equation の finite residue reduction。 -/
theorem SourceOneHoleModEquation.reduce
    {m p2 p3 k n r L a : ℕ}
    (hPeriods : Pow23Periods m p2 p3)
    (h : SourceOneHoleModEquation m k n r L a) :
    SourceOneHoleModEquation
      m (k % p3) (n % p2) (r % p2) (L % p2) (a % p2) := by
  unfold SourceOneHoleModEquation at h ⊢
  rw [← hPeriods.three_pow_mod (e := k),
      ← hPeriods.two_pow_mod (e := n),
      ← hPeriods.two_pow_mod (e := r),
      ← hPeriods.two_pow_mod (e := L),
      ← hPeriods.two_pow_mod (e := a)]
  exact h

/-- target one-hole modular equation の finite residue reduction。 -/
theorem TargetOneHoleModEquation.reduce
    {m p2 p3 k n r L b : ℕ}
    (hPeriods : Pow23Periods m p2 p3)
    (h : TargetOneHoleModEquation m k n r L b) :
    TargetOneHoleModEquation
      m (k % p3) (n % p2) (r % p2) (L % p2) (b % p2) := by
  unfold TargetOneHoleModEquation at h ⊢
  rw [← hPeriods.three_pow_mod (e := k),
      ← hPeriods.two_pow_mod (e := n),
      ← hPeriods.two_pow_mod (e := r),
      ← hPeriods.two_pow_mod (e := L),
      ← hPeriods.two_pow_mod (e := b)]
  exact h

/-- source two-hole modular equation の finite residue reduction。 -/
theorem SourceTwoHoleModEquation.reduce
    {m p2 p3 k n r L a b : ℕ}
    (hPeriods : Pow23Periods m p2 p3)
    (h : SourceTwoHoleModEquation m k n r L a b) :
    SourceTwoHoleModEquation
      m (k % p3) (n % p2) (r % p2) (L % p2) (a % p2) (b % p2) := by
  unfold SourceTwoHoleModEquation at h ⊢
  rw [← hPeriods.three_pow_mod (e := k),
      ← hPeriods.two_pow_mod (e := n),
      ← hPeriods.two_pow_mod (e := r),
      ← hPeriods.two_pow_mod (e := L),
      ← hPeriods.two_pow_mod (e := a),
      ← hPeriods.two_pow_mod (e := b)]
  exact h

/-- split two-hole modular equation の finite residue reduction。 -/
theorem SplitTwoHoleModEquation.reduce
    {m p2 p3 k n r L a b : ℕ}
    (hPeriods : Pow23Periods m p2 p3)
    (h : SplitTwoHoleModEquation m k n r L a b) :
    SplitTwoHoleModEquation
      m (k % p3) (n % p2) (r % p2) (L % p2) (a % p2) (b % p2) := by
  unfold SplitTwoHoleModEquation at h ⊢
  rw [← hPeriods.three_pow_mod (e := k),
      ← hPeriods.two_pow_mod (e := n),
      ← hPeriods.two_pow_mod (e := r),
      ← hPeriods.two_pow_mod (e := L),
      ← hPeriods.two_pow_mod (e := a),
      ← hPeriods.two_pow_mod (e := b)]
  exact h

/-- target two-hole modular equation の finite residue reduction。 -/
theorem TargetTwoHoleModEquation.reduce
    {m p2 p3 k n r L a b : ℕ}
    (hPeriods : Pow23Periods m p2 p3)
    (h : TargetTwoHoleModEquation m k n r L a b) :
    TargetTwoHoleModEquation
      m (k % p3) (n % p2) (r % p2) (L % p2) (a % p2) (b % p2) := by
  unfold TargetTwoHoleModEquation at h ⊢
  rw [← hPeriods.three_pow_mod (e := k),
      ← hPeriods.two_pow_mod (e := n),
      ← hPeriods.two_pow_mod (e := r),
      ← hPeriods.two_pow_mod (e := L),
      ← hPeriods.two_pow_mod (e := a),
      ← hPeriods.two_pow_mod (e := b)]
  exact h

/--
hole 1 の exact equation は任意 modulus で source/target one-hole residue case の
どちらかへ落ちる。
-/
theorem oneHole_modular_cases
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits)
    (hHole : Binary.oneCount sourceTail + Binary.oneCount targetBits = 1)
    (m : ℕ) :
    (∃ a : ℕ,
        0 < a ∧ a < sourceLength ∧
        SourceOneHoleModEquation m k sourceLength r targetLength a) ∨
      (∃ b : ℕ,
        0 < b ∧ b < targetLength ∧
        TargetOneHoleModEquation m k sourceLength r targetLength b) := by
  rcases oneHole_normalForm hEq hHole with h | h
  · rcases h with ⟨a, ha0, haN, hA⟩
    exact Or.inl ⟨a, ha0, haN, hA.to_mod m⟩
  · rcases h with ⟨b, hb0, hbL, hB⟩
    exact Or.inr ⟨b, hb0, hbL, hB.to_mod m⟩

/-- hole 2 の exact equation は任意 modulus で三つの finite residue case に落ちる。 -/
theorem twoHole_modular_cases
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits)
    (hHole : Binary.oneCount sourceTail + Binary.oneCount targetBits = 2)
    (m : ℕ) :
    (∃ a b : ℕ,
        0 < a ∧ a < b ∧ b < sourceLength ∧
        SourceTwoHoleModEquation m k sourceLength r targetLength a b) ∨
    (∃ a b : ℕ,
        0 < a ∧ a < sourceLength ∧
        0 < b ∧ b < targetLength ∧
        SplitTwoHoleModEquation m k sourceLength r targetLength a b) ∨
    (∃ a b : ℕ,
        0 < a ∧ a < b ∧ b < targetLength ∧
        TargetTwoHoleModEquation m k sourceLength r targetLength a b) := by
  rcases twoHole_normalForm hEq hHole with h | h | h
  · rcases h with ⟨a, b, ha0, hab, hbN, hAB⟩
    exact Or.inl ⟨a, b, ha0, hab, hbN, hAB.to_mod m⟩
  · rcases h with ⟨a, b, ha0, haN, hb0, hbL, hAB⟩
    exact Or.inr (Or.inl ⟨a, b, ha0, haN, hb0, hbL, hAB.to_mod m⟩)
  · rcases h with ⟨a, b, ha0, hab, hbL, hAB⟩
    exact Or.inr (Or.inr ⟨a, b, ha0, hab, hbL, hAB.to_mod m⟩)

end Mersenne
end Collatz3
