import CollatzLean.Collatz2.Canonical.Replay

/-!
# Collatz2 Native: replay quotient dynamics

replay quotient を新しい branch data として増やさない。
canonical residue modulus に対する自然な商を直接 `replayLayer` として読み、
word extension がこの商に与える2進 shift と、各 layer の3進 least digit を取り出す。

prefix 側では cumulative two-step exponent に従って quotient が右 shift される。
一度 zero layer に入れば、任意の suffix extension の後も zero layer のままである。
-/

namespace Collatz2
namespace Word

/-- start `X` の word `w` に対する自然な replay layer。 -/
def replayLayer (w : Word) (X : ℕ) : ℕ :=
  X / residueModulus w

/-- append により residue modulus は suffix の `2^H` 倍される。 -/
theorem residueModulus_append
    (u v : Word) :
    residueModulus (u ++ v) =
      residueModulus u * 2 ^ twoSteps v := by
  unfold residueModulus
  calc
    2 ^ (twoSteps (u ++ v) + 1)
        = 2 ^ ((twoSteps u + 1) + twoSteps v) := by
            apply congrArg (fun n : ℕ => 2 ^ n)
            simp [twoSteps_append]
            omega
    _ = 2 ^ (twoSteps u + 1) * 2 ^ twoSteps v := by
          rw [pow_add]

/--
固定 start から word を右へ延長すると replay layer は
suffix の総2除算指数だけ binary right shift される。
-/
theorem replayLayer_append
    (u v : Word)
    (X : ℕ) :
    replayLayer (u ++ v) X =
      replayLayer u X / 2 ^ twoSteps v := by
  unfold replayLayer
  rw [residueModulus_append]
  simp only [Nat.div_div_eq_div_mul]

/-- modulus 未満の start は zero replay layer にある。 -/
theorem replayLayer_eq_zero_of_lt_modulus
    {w : Word} {X : ℕ}
    (hX : X < residueModulus w) :
    replayLayer w X = 0 := by
  unfold replayLayer
  exact Nat.div_eq_of_lt hX

/-- 一度 zero replay layer に入れば任意の suffix extension 後も zero。 -/
theorem replayLayer_append_eq_zero_of_zero
    {u : Word} (v : Word) {X : ℕ}
    (hzero : replayLayer u X = 0) :
    replayLayer (u ++ v) X = 0 := by
  rw [replayLayer_append, hzero]
  simp

/-- replay layer の3進 least digit。 -/
def replayTernaryDigit (w : Word) (X : ℕ) : ℕ :=
  replayLayer w X % 3

/-- 3進 least digit は `0,1,2` のいずれか。 -/
theorem replayTernaryDigit_lt_three
    (w : Word) (X : ℕ) :
    replayTernaryDigit w X < 3 := by
  unfold replayTernaryDigit
  exact Nat.mod_lt _ (by omega)

/--
任意の replay layer は `3 * higherLayer + digit` に一意に分解される。
後続の suffix-replay 解析では、この digit が旧 `j` 座標の薄い形になる。
-/
theorem replayLayer_ternary_decomposition
    (w : Word) (X : ℕ) :
    replayLayer w X =
      3 * (replayLayer w X / 3) + replayTernaryDigit w X := by
  have h := Nat.mod_add_div (replayLayer w X) 3
  simpa [replayTernaryDigit, Nat.add_comm] using h.symm

end Word
end Collatz2
