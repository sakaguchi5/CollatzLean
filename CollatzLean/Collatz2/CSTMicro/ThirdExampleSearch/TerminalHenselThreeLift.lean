import Mathlib.Data.Nat.Factorization.Defs


/-!
# 第3例探索 6: terminal Hensel の 3-lift sieve

右端から backward に Hensel 状態を復元するとき、

  3 q_prev + 1 = 2 q_next + 2^d

を満たす必要がある。
`q_next ≡ 2 (mod 3)` なら右辺の `2^d` が 3 の倍数にならないため、
predecessor は存在しない。

さらに 3 個の lift のうち少なくとも 1 個を kill できれば、survivor は高々 2 個になる。
これが residue tree の分岐数を `3^K` ではなく最大 `2^K` に抑える核である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- `2^d mod 3` は常に 1 または 2 であり、0 にはならない。 -/
theorem two_pow_mod_three_one_or_two (d : ℕ) :
    2 ^ d % 3 = 1 ∨ 2 ^ d % 3 = 2 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rcases ih with h1 | h2
      · right
        simp [pow_succ, Nat.mul_mod, h1]
      · left
        simp [pow_succ, Nat.mul_mod, h2]

/--
`q_next ≡ 2 (mod 3)` は backward Hensel recurrence の dead state である。
-/
theorem no_hensel_predecessor_of_mod_three_eq_two
    (qPrev qNext d : ℕ)
    (hRec : 3 * qPrev + 1 = 2 * qNext + 2 ^ d)
    (hNext : qNext % 3 = 2) :
    False := by
  have hMod := congrArg (fun z : ℕ => z % 3) hRec
  rcases two_pow_mod_three_one_or_two d with hPow | hPow
  · simp [Nat.add_mod, Nat.mul_mod, hNext, hPow] at hMod
  · simp [Nat.add_mod, Nat.mul_mod, hNext, hPow] at hMod

/--
3 個の residue lift のうち少なくとも 1 個が死ぬなら、survivor は高々 2 個。

Hensel 固有の仕事は `hkilled` を各 residue class で供給することだけで、
cardinality の部分はこの有限集合補題で完全に分離できる。
-/
theorem terminalHensel_survivor_threeLift_le_two
    (survives : Fin 3 → Prop)
    [DecidablePred survives]
    (hkilled : ∃ a : Fin 3, ¬ survives a) :
    (Finset.univ.filter survives).card ≤ 2 := by
  obtain ⟨a, ha⟩ := hkilled
  have hSub :
      Finset.univ.filter survives ⊆ Finset.univ.erase a := by
    intro x hx
    have hxSurvives : survives x := (Finset.mem_filter.mp hx).2
    have hxa : x ≠ a := by
      intro h
      subst x
      exact ha hxSurvives
    simp [hxa]
  have hCard := Finset.card_le_card hSub
  simpa using hCard

end ThirdExampleSearch
end CSTMicro
end Collatz2
