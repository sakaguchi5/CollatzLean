import CollatzLean.Collatz4.Core.Forward

/-!
# Collatz4.Core.Normalization

前向き写像の合流を生む最小の `01` 規則。

奇数部分の二進末尾が `...01` の枝と、2指数を2増やしてその `01` を
除いた枝は、次の1回で同じ状態へ入る。
-/

namespace Collatz4

/-- `01` を1個剥がすときの状態変換。 -/
def strip01 (x : ForwardState) : ForwardState :=
  ⟨x.t + 2, (x.u - 1) / 4⟩

/--
合流の基本恒等式。

`(t, 4u+1)` と `(t+2, u)` は次の1回で同じ状態へ進む。
-/
theorem step_merge01 (t u : ℕ) :
    step ⟨t, 4 * u + 1⟩ = step ⟨t + 2, u⟩ := by
  have hz : 3 * u + 1 ≠ 0 := three_mul_add_one_ne_zero u
  have hnum : 3 * (4 * u + 1) + 1 = 2 ^ 2 * (3 * u + 1) := by
    ring
  have hv : v2 (3 * (4 * u + 1) + 1) = v2 (3 * u + 1) + 2 := by
    rw [hnum]
    simpa [v2] using
      (padicValNat_base_pow_mul (p := 2) (n := 3 * u + 1)
        (by norm_num : 1 < (2 : ℕ)) hz 2)
  have ho : oddPart (3 * (4 * u + 1) + 1) = oddPart (3 * u + 1) := by
    rw [hnum]
    simpa [oddPart] using
      (Nat.divMaxPow_base_pow_mul (p := 2) (by norm_num : (2 : ℕ) ≠ 0)
        (3 * u + 1) 2)
  apply ForwardState.ext
  · simp [step, hv]
    omega
  · simp [step, ho]

end Collatz4
