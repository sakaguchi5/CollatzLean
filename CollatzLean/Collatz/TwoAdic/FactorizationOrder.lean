import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# exact 2進分解の指数順序

exact factor の odd part が奇数なら、同じ数に見えている任意の2冪因子より
exact exponent は小さくなれない。
-/

namespace Collatz
namespace TwoAdic

/--
`n = 2^e * u` が exact 2進分解で、さらに `n = 2^b * v` なら `b ≤ e`。
-/
theorem ExactFactor.exponent_ge_of_eq_twoPow_mul
    {n e u b v : ℕ}
    (h : ExactFactor n e u)
    (hpow : n = 2 ^ b * v) :
    b ≤ e := by
  by_contra hnot
  have heb : e < b := by omega
  obtain ⟨r, hur⟩ :=
    oddPart_eq_twoPow_mul_of_lt
      (h.1.symm.trans hpow) heb
  exact odd_even_false h.2 (by
    rw [hur]
    exact even_two_pow_succ_mul r v)

end TwoAdic
end Collatz
