import CollatzLean.CollatzFirstLayer.NegativeShadowAlignment

/-!
# negative shadowのexact one-bit臨界境界

negative shadow magnitudeの二状態

`b = a + 2 * k`

で差がexactに1ビット、かつ`k`が奇数である場合を扱う。
`a`側の次指数がexactに1なら、`b`側も指数1を使うことはできず、
完全2進分解により次指数は少なくとも2になる。

これは既存`oddShadowStep_ordered_alignment`の仮定`e < m`が
境界`e = m = 1`で使えない箇所を補う局所定理である。
-/

namespace CollatzFirstLayer
namespace ExpWord

/--
exact one-bitだけ離れた二つのnegative shadow magnitudeで、
下側が指数1を使うなら上側の次指数は2以上である。
-/
theorem oddShadowStep_exact_one_bit_forces_other_exponent_two_le
    {a b a' b' e₂ k : ℕ}
    (haOdd : Odd a')
    (hbOdd : Odd b')
    (hkOdd : Odd k)
    (hA : 2 * a' + 1 = 3 * a)
    (hB : 2 ^ e₂ * b' + 1 = 3 * b)
    (hAlign : b = a + 2 * k) :
    2 ≤ e₂ := by
  by_contra hnot
  have he : e₂ = 0 ∨ e₂ = 1 := by
    omega
  rcases haOdd with ⟨u, hu⟩
  rcases hbOdd with ⟨v, hv⟩
  rcases hkOdd with ⟨r, hr⟩
  rcases he with rfl | rfl
  · norm_num at hB
    omega
  · norm_num at hB
    omega

end ExpWord
end CollatzFirstLayer
