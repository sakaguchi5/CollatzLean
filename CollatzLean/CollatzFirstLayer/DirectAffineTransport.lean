import CollatzLean.CollatzFirstLayer.AffineTransport


/-!
# affine定数全体の直接輸送評価

既存の`TransportBound`は各suffixを一様評価した後に語長を掛ける。
ここではtotal項とaffine定数全体を、同じ係数で直接抑える。
-/

namespace CollatzFirstLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- total乗法項とaffine定数全体の直接上界。 -/
structure DirectAffineTransportBound
    (C : ℕ) (w : ExpWord) : Prop where
  total : 3 ^ oddSteps w ≤ C * 2 ^ twoSteps w
  affine : affineConst w ≤ C * 2 ^ twoSteps w

/-- 直接輸送上界の下では終点は`C * (start+1)`以下。 -/
theorem endpoint_le_directAffineTransport
    {w : ExpWord} {x y C : ℕ}
    (hrun : Realizes w x y)
    (h : DirectAffineTransportBound C w) :
    y ≤ C * (x + 1) := by
  have hmain :
      2 ^ twoSteps w * y ≤
        2 ^ twoSteps w * (C * (x + 1)) := by
    calc
      2 ^ twoSteps w * y
          = 3 ^ oddSteps w * x + affineConst w := hrun
      _ ≤ (C * 2 ^ twoSteps w) * x +
            C * 2 ^ twoSteps w :=
        Nat.add_le_add
          (Nat.mul_le_mul_right x h.total)
          h.affine
      _ = 2 ^ twoSteps w * (C * (x + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hmain
    (Nat.pow_pos (by omega : 0 < (2 : ℕ)))

/-- 既存のsuffix輸送上界から直接輸送上界を得る。 -/
theorem DirectAffineTransportBound.ofTransportBound
    (C : ℕ) (w : ExpWord)
    (h : TransportBound C w) :
    DirectAffineTransportBound (w.length * C + C) w where
  total := by
    calc
      3 ^ oddSteps w ≤ C * 2 ^ twoSteps w := h.total
      _ ≤ (w.length * C + C) * 2 ^ twoSteps w := by
        exact Nat.mul_le_mul_right _ (by omega)
  affine := by
    have hB := affineConst_le_length_mul_transport C w h.suffix
    calc
      affineConst w ≤ w.length * C * 2 ^ twoSteps w := hB
      _ ≤ (w.length * C + C) * 2 ^ twoSteps w := by
        exact Nat.mul_le_mul_right _ (by omega)

/-- 任意の有限語は明示的な直接輸送係数を持つ。 -/
theorem directAffineTransportBound
    (w : ExpWord) :
    DirectAffineTransportBound
      (3 ^ oddSteps w + affineConst w) w where
  total := by
    have hpow : 1 ≤ 2 ^ twoSteps w := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.pow_pos (by omega)))
    calc
      3 ^ oddSteps w
          ≤ (3 ^ oddSteps w + affineConst w) * 1 := by
            simp
      _ ≤ (3 ^ oddSteps w + affineConst w) * 2 ^ twoSteps w :=
        Nat.mul_le_mul_left _ hpow

  affine := by
    have hpow : 1 ≤ 2 ^ twoSteps w := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.pow_pos (by omega)))
    calc
      affineConst w
          ≤ (3 ^ oddSteps w + affineConst w) * 1 := by
            simp
      _ ≤ (3 ^ oddSteps w + affineConst w) * 2 ^ twoSteps w :=
        Nat.mul_le_mul_left _ hpow

end CollatzFirstLayer
