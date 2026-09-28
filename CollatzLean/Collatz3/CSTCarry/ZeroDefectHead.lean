import CollatzLean.Collatz3.CSTCarry.CarryDeterministicSplit
import CollatzLean.Collatz3.CSTCarry.ProfileRowBridge

/-!
# Collatz3 CSTCarry: zero-defect row は strict boundedness を保存する

一 row の defect が `0` なら

`E + M*a = 3*E'`, `a<3`

である。`0<M` かつ `E<M` なら左辺は必ず `3M` 未満なので `E'<M`。

特に profile の critical index `0` row は常に

* boundary = 0,
* actual = 0,
* defect = 0,

であるため、canonical prefix `[1]` 側の最後の一 row は、既に得た strict bound を壊さない。
-/

namespace Collatz3
namespace CSTCarry

/-- defect `0` の一 step は `E<M` を `E'<M` に保つ。 -/
theorem carryStep_final_lt_of_defect_zero
    {M E a E' : ℕ}
    (hM : 0 < M)
    (hE : E < M)
    (ha : a < 3)
    (hEq : E + M * a = 3 * E') :
    E' < M := by
  have hCases : a = 0 ∨ a = 1 ∨ a = 2 := by
    omega
  rcases hCases with h0 | h1 | h2
  · subst a
    norm_num at hEq
    omega
  · subst a
    norm_num at hEq
    omega
  · subst a
    omega

/-- canonical next carry も defect `0` row では strict boundedness を保存する。 -/
theorem canonicalNextCarry_lt_modulus_of_defect_zero
    (H E : ℕ)
    (R : FerrersRow)
    (hE : E < 2 ^ H)
    (hDefect : R.defect = 0) :
    canonicalNextCarry H E R < 2 ^ H := by
  have hEq := canonicalNextCarry_spec H E R
  rw [hDefect] at hEq
  simp only [Nat.add_zero] at hEq
  exact carryStep_final_lt_of_defect_zero
    (by positivity)
    hE
    (canonicalCarryDigit_lt_three H E R)
    hEq

/-- profile の critical index `0` row の defect は常に `0`。 -/
@[simp] theorem profileFerrersRow_zero_defect
    {m : ℕ}
    (h : Critical.Profile m)
    (hm : 0 < m) :
    (profileFerrersRow h ⟨0, hm⟩).defect = 0 := by
  simp [profileFerrersRow, FerrersRow.defect, Critical.checkpoint]

/-- index `0` row の canonical next carry は strict modulus bound を保存する。 -/
theorem canonicalNextCarry_profileZero_lt
    {m : ℕ}
    (h : Critical.Profile m)
    (hm : 0 < m)
    (H E : ℕ)
    (hE : E < 2 ^ H) :
    canonicalNextCarry H E (profileFerrersRow h ⟨0, hm⟩) < 2 ^ H := by
  exact canonicalNextCarry_lt_modulus_of_defect_zero
    H E (profileFerrersRow h ⟨0, hm⟩) hE
    (profileFerrersRow_zero_defect h hm)

/-- singleton の index `0` row を最後まで走らせても strict modulus bound は保たれる。 -/
theorem canonicalFinalCarry_profileZero_singleton_lt
    {m : ℕ}
    (h : Critical.Profile m)
    (hm : 0 < m)
    (H E : ℕ)
    (hE : E < 2 ^ H) :
    canonicalFinalCarry H [profileFerrersRow h ⟨0, hm⟩] E < 2 ^ H := by
  simpa using canonicalNextCarry_profileZero_lt h hm H E hE

end CSTCarry
end Collatz3
