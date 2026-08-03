import CollatzLean.CollatzFirstLayer.CanonicalResidue

/-!
# 2進returnによる有限語replay

開始値を `2^(H+1)` の倍数だけ動かすと、同じ有限指数語を実現する新しい終点を明示的に構成できる。
この定理は「同じ語をreplayする」ことの純代数版である。
-/

namespace CollatzFirstLayer
namespace ExpWord

/--
語全体のreplay定理。
開始値を `2^(H+1)k` 増やすと、終点は `2·3^p k` 増える。
-/
theorem replay_theorem {w : ExpWord} {X Z k : ℕ}
    (h : Realizes w X Z) :
    Realizes w
      (X + 2 ^ (twoSteps w + 1) * k)
      (Z + 2 * 3 ^ oddSteps w * k) := by
  unfold Realizes at h ⊢
  rw [pow_add]
  norm_num
  calc
    2 ^ twoSteps w * (Z + 2 * 3 ^ oddSteps w * k)
        = 2 ^ twoSteps w * Z +
          3 ^ oddSteps w * (2 ^ twoSteps w * 2 * k) := by ring
    _ = (3 ^ oddSteps w * X + affineConst w) +
          3 ^ oddSteps w * (2 ^ twoSteps w * 2 * k) := by rw [h]
    _ = 3 ^ oddSteps w *
          (X + (2 ^ twoSteps w * 2) * k) + affineConst w := by ring

/-- replay後の終点差。 -/
lemma replay_endpoint_difference (w : ExpWord) (Z k : ℕ) :
    (Z + 2 * 3 ^ oddSteps w * k) - Z =
      2 * 3 ^ oddSteps w * k := by
  omega

/-- `2^(H+1)` returnはcanonical剰余類を保存する。 -/
theorem replay_preserves_canonical_class (w : ExpWord) (X k : ℕ) :
    (((X + residueModulus w * k : ℕ) : ZMod (residueModulus w))) =
      ((X : ℕ) : ZMod (residueModulus w)) := by
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]

end ExpWord
end CollatzFirstLayer
