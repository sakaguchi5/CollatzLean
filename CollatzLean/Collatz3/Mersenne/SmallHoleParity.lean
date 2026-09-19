import CollatzLean.Collatz3.Mersenne.SmallHoleModular
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination


/-!
# Collatz3 Mersenne: mod 3 parity constraints

source endpoint に hole がない場合は `r,L` がともに odd。
split-two では target hole `b` を含めた parity relation を exact に固定する。
-/

namespace Collatz3
namespace Mersenne

private theorem twoPowParity_sourceEndpoint
    {r L : ℕ}
    (h :
      (2 : ZMod 3) ^ r * ((2 : ZMod 3) ^ L - 1) + 1 = 0) :
    r % 2 = 1 ∧ L % 2 = 1 := by
  have hp : (2 : ZMod 3) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := r) hp,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := L) hp] at h
  have hrlt : r % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hLlt : L % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hrCases : r % 2 = 0 ∨ r % 2 = 1 := by omega
  have hLCases : L % 2 = 0 ∨ L % 2 = 1 := by omega
  rcases hrCases with hr0 | hr1 <;>
    rcases hLCases with hL0 | hL1
  · rw [hr0, hL0] at h
    norm_num at h
  · rw [hr0, hL1] at h
    norm_num at h
    have hTwoNe : (2 : ZMod 3) ≠ 0 := by
      decide
    exact (hTwoNe h).elim
  · rw [hr1, hL0] at h
    norm_num at h
  · exact ⟨hr1, hL1⟩

private theorem splitEndpointParity
    {r L b : ℕ}
    (h :
      (2 : ZMod 3) ^ r *
          ((2 : ZMod 3) ^ L - 1 - (2 : ZMod 3) ^ b) + 1 = 0) :
    (r % 2 = 0 ∧ L % 2 = b % 2) ∨
      (r % 2 = 1 ∧ L % 2 = 0 ∧ b % 2 = 1) := by
  have hp : (2 : ZMod 3) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := r) hp,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := L) hp,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := b) hp] at h
  have hrlt : r % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hLlt : L % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hblt : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hrCases : r % 2 = 0 ∨ r % 2 = 1 := by omega
  have hLCases : L % 2 = 0 ∨ L % 2 = 1 := by omega
  have hbCases : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hrCases with hr0 | hr1 <;>
    rcases hLCases with hL0 | hL1 <;>
      rcases hbCases with hb0 | hb1
  · exact Or.inl ⟨hr0, by omega⟩
  · rw [hr0, hL0, hb1] at h
    norm_num at h
  · rw [hr0, hL1, hb0] at h
    norm_num at h
  · exact Or.inl ⟨hr0, by omega⟩
  · rw [hr1, hL0, hb0] at h
    norm_num at h
  · exact Or.inr ⟨hr1, hL0, hb1⟩
  · rw [hr1, hL1, hb0] at h
    norm_num at h
  · rw [hr1, hL1, hb1] at h
    norm_num at h

private theorem threePow_zero_zmod3
    {k : ℕ}
    (hk : 0 < k) :
    (3 : ZMod 3) ^ k = 0 := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ]
  have hThree : (3 : ZMod 3) = 0 := by
    decide
  rw [hThree, mul_zero]

/-- no-hole の positive depth では `r,L` はともに odd。 -/
theorem NoHoleEquation.endpoint_parity
    {k n r L : ℕ}
    (hk : 0 < k)
    (hEq : NoHoleEquation k n r L) :
    r % 2 = 1 ∧ L % 2 = 1 := by
  have hMod := hEq.to_mod 3
  unfold NoHoleModEquation at hMod
  rw [threePow_zero_zmod3 hk] at hMod
  have hCore :
      (2 : ZMod 3) ^ r *
          ((2 : ZMod 3) ^ L - 1) + 1 = 0 := by
    simpa using hMod.symm
  exact twoPowParity_sourceEndpoint hCore


/-- source-one の positive depth では `r,L` はともに odd。 -/
theorem SourceOneHoleEquation.endpoint_parity
    {k n r L a : ℕ}
    (hk : 0 < k)
    (hEq : SourceOneHoleEquation k n r L a) :
    r % 2 = 1 ∧ L % 2 = 1 := by
  have hMod := hEq.to_mod 3
  unfold SourceOneHoleModEquation at hMod
  rw [threePow_zero_zmod3 hk] at hMod
  have hCore :
      (2 : ZMod 3) ^ r *
          ((2 : ZMod 3) ^ L - 1) + 1 = 0 := by
    simpa using hMod.symm
  exact twoPowParity_sourceEndpoint hCore


/-- source-two の positive depth では `r,L` はともに odd。 -/
theorem SourceTwoHoleEquation.endpoint_parity
    {k n r L a b : ℕ}
    (hk : 0 < k)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    r % 2 = 1 ∧ L % 2 = 1 := by
  have hMod := hEq.to_mod 3
  unfold SourceTwoHoleModEquation at hMod
  rw [threePow_zero_zmod3 hk] at hMod
  have hCore :
      (2 : ZMod 3) ^ r *
          ((2 : ZMod 3) ^ L - 1) + 1 = 0 := by
    simpa using hMod.symm
  exact twoPowParity_sourceEndpoint hCore

/-- split-two の target parity exact classification。 -/
theorem SplitTwoHoleEquation.target_parity
    {k n r L a b : ℕ}
    (hk : 0 < k)
    (hEq : SplitTwoHoleEquation k n r L a b) :
    (r % 2 = 0 ∧ L % 2 = b % 2) ∨
      (r % 2 = 1 ∧ L % 2 = 0 ∧ b % 2 = 1) := by
  have hMod := hEq.to_mod 3
  unfold SplitTwoHoleModEquation at hMod
  rw [threePow_zero_zmod3 hk] at hMod
  have hCore :
      (2 : ZMod 3) ^ r *
          ((2 : ZMod 3) ^ L - 1 - (2 : ZMod 3) ^ b) + 1 = 0 := by
    simpa only [zero_mul] using hMod.symm
  exact splitEndpointParity hCore

/-- split-two で `r=1` なら target length は even、target hole は odd。 -/
theorem SplitTwoHoleEquation.target_parity_of_exit_one
    {k n L a b : ℕ}
    (hk : 0 < k)
    (hEq : SplitTwoHoleEquation k n 1 L a b) :
    L % 2 = 0 ∧ b % 2 = 1 := by
  rcases hEq.target_parity hk with hEven | hOdd
  · norm_num at hEven
  · exact hOdd.2

/-- split-two で `r=2` なら target length と target hole は同 parity。 -/
theorem SplitTwoHoleEquation.target_parity_of_exit_two
    {k n L a b : ℕ}
    (hk : 0 < k)
    (hEq : SplitTwoHoleEquation k n 2 L a b) :
    L % 2 = b % 2 := by
  rcases hEq.target_parity hk with hEven | hOdd
  · exact hEven.2
  · norm_num at hOdd

end Mersenne
end Collatz3
