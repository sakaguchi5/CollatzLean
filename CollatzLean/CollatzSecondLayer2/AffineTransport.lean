import CollatzLean.CollatzFirstLayer.Affine



/-!
# affine定数の一様輸送評価

語の各suffixが終端scaleに対してどれだけ増幅し得るかを一つの定数`C`で抑え、
affine定数の全`+1`寄与を`length * C * 2^H`以下に評価する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
`j`番目の`+1`が終点へ輸送される正規化係数を一様に抑える条件。
-/
def SuffixTransportBound (C : ℕ) (w : ExpWord) : Prop :=
  ∀ j : ℕ, j < w.length →
    3 ^ (w.length - (j + 1)) * 2 ^ twoSteps (w.take j) ≤
      C * 2 ^ twoSteps w

/-- total乗法係数と全affine suffix係数を同じ`C`で抑える。 -/
structure TransportBound (C : ℕ) (w : ExpWord) : Prop where
  total : 3 ^ oddSteps w ≤ C * 2 ^ twoSteps w
  suffix : SuffixTransportBound C w

/-- suffix輸送上界からaffine定数の総和を評価する。 -/
theorem affineConst_le_length_mul_transport
    (C : ℕ) (w : ExpWord)
    (h : SuffixTransportBound C w) :
    affineConst w ≤ w.length * C * 2 ^ twoSteps w := by
  induction w with
  | nil => simp [affineConst]
  | cons e w ih =>
      have hhead :
          3 ^ w.length ≤ C * 2 ^ twoSteps (e :: w) := by
        have h0 := h 0 (by simp)
        simpa [SuffixTransportBound] using h0
      have htail : SuffixTransportBound C w := by
        intro j hj
        have hs := h (j + 1) (by simp; omega)
        have hscaled :
            2 ^ e *
                (3 ^ (w.length - (j + 1)) *
                  2 ^ twoSteps (w.take j)) ≤
              2 ^ e * (C * 2 ^ twoSteps w) := by
          simpa [SuffixTransportBound, List.take_succ_cons,
            twoSteps_cons, pow_add,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hs
        exact Nat.le_of_mul_le_mul_left hscaled
          (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
      have hi := ih htail
      have htailScaled :
          2 ^ e * affineConst w ≤
            w.length * C * 2 ^ twoSteps (e :: w) := by
        calc
          2 ^ e * affineConst w
              ≤ 2 ^ e * (w.length * C * 2 ^ twoSteps w) :=
            Nat.mul_le_mul_left _ hi
          _ = w.length * C * 2 ^ twoSteps (e :: w) := by
            rw [twoSteps_cons, pow_add]
            ring
      calc
        affineConst (e :: w)
            = 3 ^ w.length + 2 ^ e * affineConst w := by
              simp [affineConst]
        _ ≤ C * 2 ^ twoSteps (e :: w) +
              w.length * C * 2 ^ twoSteps (e :: w) :=
            Nat.add_le_add hhead htailScaled
        _ = (e :: w).length * C * 2 ^ twoSteps (e :: w) := by
            simp only [List.length_cons]
            ring

/--
輸送係数`C`の下で、実現終点は`C * (start + length)`以下。
-/
theorem endpoint_le_transport_mul_start_add_length
    {w : ExpWord} {x y C : ℕ}
    (hrun : Realizes w x y)
    (h : TransportBound C w) :
    y ≤ C * (x + w.length) := by
  have hB :
      affineConst w ≤ w.length * C * 2 ^ twoSteps w :=
    affineConst_le_length_mul_transport C w h.suffix
  have hmain :
      2 ^ twoSteps w * y ≤
        2 ^ twoSteps w * (C * (x + w.length)) := by
    calc
      2 ^ twoSteps w * y
          = 3 ^ oddSteps w * x + affineConst w := hrun
      _ ≤ (C * 2 ^ twoSteps w) * x +
            w.length * C * 2 ^ twoSteps w :=
          Nat.add_le_add
            (Nat.mul_le_mul_right x h.total)
            hB
      _ = 2 ^ twoSteps w * (C * (x + w.length)) := by ring
  exact Nat.le_of_mul_le_mul_left hmain
    (Nat.pow_pos (by omega : 0 < (2 : ℕ)))


/--
輸送係数・開始値・語長が同じparameter `q`の固定多項式以下なら、
終点も固定多項式以下になる。
-/
theorem endpoint_le_polynomial_of_transport
    {w : ExpWord} {x y C q Kc B Kx A Kt D : ℕ}
    (hrun : Realizes w x y)
    (htransport : TransportBound C w)
    (hC : C ≤ Kc * (q + 1) ^ B)
    (hx : x ≤ Kx * (q + 1) ^ A)
    (hlen : w.length ≤ Kt * (q + 1) ^ D) :
    y ≤ Kc * (Kx + Kt) * (q + 1) ^ (B + A + D) := by
  have hA : (q + 1) ^ A ≤ (q + 1) ^ (A + D) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hD : (q + 1) ^ D ≤ (q + 1) ^ (A + D) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hx' : x ≤ Kx * (q + 1) ^ (A + D) :=
    hx.trans (Nat.mul_le_mul_left Kx hA)
  have hlen' : w.length ≤ Kt * (q + 1) ^ (A + D) :=
    hlen.trans (Nat.mul_le_mul_left Kt hD)
  have hsum :
      x + w.length ≤ (Kx + Kt) * (q + 1) ^ (A + D) := by
    calc
      x + w.length
          ≤ Kx * (q + 1) ^ (A + D) +
              Kt * (q + 1) ^ (A + D) :=
        Nat.add_le_add hx' hlen'
      _ = (Kx + Kt) * (q + 1) ^ (A + D) := by ring
  have hy := endpoint_le_transport_mul_start_add_length hrun htransport
  calc
    y ≤ C * (x + w.length) := hy
    _ ≤ (Kc * (q + 1) ^ B) *
          ((Kx + Kt) * (q + 1) ^ (A + D)) :=
      Nat.mul_le_mul hC hsum
    _ = Kc * (Kx + Kt) * (q + 1) ^ (B + A + D) := by
      rw [show B + A + D = B + (A + D) by omega, pow_add]
      ring

end CollatzSecondLayer2
