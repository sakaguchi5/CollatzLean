import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostArithmetic

/-!
# MultiCorner attached branch: straight corridor による cost transport

attached の previous corner と terminal corner の間が straight corridor であるとき、
二つの cell は独立ではない。

ここでは packet の index bookkeeping にはまだ依存せず、straight corridor から得られる
二つの exact 入力

  3^W w₁ = 2^(W+ρ) w₀

  M ∣ 3^W δ₁ - 2^(W+ρ) δ₀

を仮定し、各 cell の exact cost identity

  M C_j = G δ_j + w_j

から

  G ∣ 3^W C₁ - 2^(W+ρ) C₀

を導く。

数学的には

  3^W C₁ ≡ 2^(W+ρ) C₀  (mod G)

である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

/--
straight corridor を隔てた二つの cell cost の transport に必要な最小データ。

`rho` は previous exposed corner の gap から straight baseline `1` を引いた余分な深さ。
actual attached 適用では `1 ≤ rho` を別に得るが、この純算術定理には不要。
-/
structure AttachedStraightCostTransfer where
  modulus : ℤ
  gap : ℤ
  width : ℕ
  rho : ℕ

  cost0 : ℤ
  cost1 : ℤ
  delta0 : ℤ
  delta1 : ℤ
  weight0 : ℤ
  weight1 : ℤ

  modulus_ne : modulus ≠ 0

  cell0_exact :
    modulus * cost0 = gap * delta0 + weight0
  cell1_exact :
    modulus * cost1 = gap * delta1 + weight1

  weight_transport :
    (3 : ℤ) ^ width * weight1 =
      (2 : ℤ) ^ (width + rho) * weight0

  delta_transport :
    modulus ∣
      (3 : ℤ) ^ width * delta1 -
        (2 : ℤ) ^ (width + rho) * delta0

namespace AttachedStraightCostTransfer

/--
straight corridor の同じ multiplier が cell cost にも降りる。

  G ∣ 3^W C₁ - 2^(W+ρ) C₀.

`delta_transport` の modulus factor と `weight_transport` の exact equality を
cell-cost identity に代入し、共通 modulus を cancel するだけである。
-/
theorem gap_dvd_cost_transport
    (T : AttachedStraightCostTransfer) :
    T.gap ∣
      (3 : ℤ) ^ T.width * T.cost1 -
        (2 : ℤ) ^ (T.width + T.rho) * T.cost0 := by
  rcases T.delta_transport with ⟨z, hz⟩
  let X : ℤ :=
    (3 : ℤ) ^ T.width * T.cost1 -
      (2 : ℤ) ^ (T.width + T.rho) * T.cost0
  have hScaled :
      T.modulus * X =
        T.gap *
          ((3 : ℤ) ^ T.width * T.delta1 -
            (2 : ℤ) ^ (T.width + T.rho) * T.delta0) := by
    dsimp [X]
    calc
      T.modulus *
          ((3 : ℤ) ^ T.width * T.cost1 -
            (2 : ℤ) ^ (T.width + T.rho) * T.cost0) =
        (3 : ℤ) ^ T.width * (T.modulus * T.cost1) -
          (2 : ℤ) ^ (T.width + T.rho) *
            (T.modulus * T.cost0) := by
              ring
      _ =
        (3 : ℤ) ^ T.width * (T.gap * T.delta1 + T.weight1) -
          (2 : ℤ) ^ (T.width + T.rho) *
            (T.gap * T.delta0 + T.weight0) := by
              rw [T.cell1_exact, T.cell0_exact]
      _ =
        T.gap *
            ((3 : ℤ) ^ T.width * T.delta1 -
              (2 : ℤ) ^ (T.width + T.rho) * T.delta0) +
          ((3 : ℤ) ^ T.width * T.weight1 -
            (2 : ℤ) ^ (T.width + T.rho) * T.weight0) := by
              ring
      _ =
        T.gap *
          ((3 : ℤ) ^ T.width * T.delta1 -
            (2 : ℤ) ^ (T.width + T.rho) * T.delta0) := by
              rw [T.weight_transport]
              ring
  have hScaled' : T.modulus * X = T.modulus * (T.gap * z) := by
    rw [hScaled, hz]
    ring
  have hCancel : X = T.gap * z :=
    mul_left_cancel₀ T.modulus_ne hScaled'
  refine ⟨z, ?_⟩
  exact hCancel

end AttachedStraightCostTransfer

end MultiCorner
end CSTMicro
end Collatz2
