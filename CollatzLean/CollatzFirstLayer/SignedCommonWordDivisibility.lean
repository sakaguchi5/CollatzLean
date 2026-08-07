import CollatzLean.CollatzFirstLayer.CommonWordDifference
import CollatzLean.CollatzFirstLayer.CanonicalReplay

/-!
# 共通wordの整数実現と2進整除

既存の整数affine差分公式を`RealizesInt`へ包装する。
開始差・終了差が自然数offsetとして与えられる場合には、
2と3の互いに素性から開始offsetの全2進depth整除を得る。

さらに、自然数実現の両終点が奇数なら終了差に追加の1ビットがあるため、
開始差は`residueModulus = 2^(twoSteps+1)`全体で割り切れる。
整数実現に対するsigned replayの平行移動公式もここで用意する。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- 同じwordの二つの整数実現に対する差のexact輸送式。 -/
theorem realizesInt_common_word_difference
    {w : ExpWord} {x₁ x₂ y₁ y₂ : ℤ}
    (h₁ : RealizesInt w x₁ y₁)
    (h₂ : RealizesInt w x₂ y₂) :
    (2 : ℤ) ^ twoSteps w * (y₂ - y₁) =
      (3 : ℤ) ^ oddSteps w * (x₂ - x₁) := by
  unfold RealizesInt at h₁ h₂
  exact signed_common_affine_difference h₁ h₂

/-- `residueModulus`を整数上の純粋な2冪として書く。 -/
@[simp] theorem residueModulus_int_cast
    (w : ExpWord) :
    (residueModulus w : ℤ) =
      (2 : ℤ) ^ (twoSteps w + 1) := by
  simp [residueModulus]

/--
整数実現の開始差・終了差が自然数offsetとして与えられる場合、
開始offsetはwordの全2冪depthで割り切れる。
-/
theorem twoPow_twoSteps_dvd_nat_startOffset_of_common_signed_word
    {w : ExpWord} {x₁ x₂ y₁ y₂ : ℤ} {dx dy : ℕ}
    (h₁ : RealizesInt w x₁ y₁)
    (h₂ : RealizesInt w x₂ y₂)
    (hx : x₂ = x₁ + (dx : ℤ))
    (hy : y₂ = y₁ + (dy : ℤ)) :
    2 ^ twoSteps w ∣ dx := by
  have hDiff := realizesInt_common_word_difference h₁ h₂
  rw [hx, hy] at hDiff
  have hZ :
      (2 : ℤ) ^ twoSteps w * (dy : ℤ) =
        (3 : ℤ) ^ oddSteps w * (dx : ℤ) := by
    simpa using hDiff
  have hNat :
      2 ^ twoSteps w * dy =
        3 ^ oddSteps w * dx := by
    exact_mod_cast hZ
  have hProduct :
      2 ^ twoSteps w ∣ 3 ^ oddSteps w * dx :=
    ⟨dy, hNat.symm⟩
  have hCoprime :
      Nat.Coprime (2 ^ twoSteps w) (3 ^ oddSteps w) :=
    Nat.Coprime.pow
      (twoSteps w) (oddSteps w)
      (by decide : Nat.Coprime 2 3)
  exact Nat.Coprime.dvd_of_dvd_mul_left hCoprime hProduct

/--
同じwordの二自然数実現で両終点が奇数なら、開始差は
`residueModulus w = 2^(twoSteps w + 1)`全体で割り切れる。

既存の`2^twoSteps`整除に、終点差が偶数であることから1ビットを追加する。
-/
theorem residueModulus_dvd_startDifference_of_common_word
    {w : ExpWord} {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : Realizes w x₁ y₁)
    (h₂ : Realizes w x₂ y₂)
    (hx : x₁ ≤ x₂)
    (hy₁ : Odd y₁)
    (hy₂ : Odd y₂) :
    residueModulus w ∣ x₂ - x₁ := by
  have hy : y₁ ≤ y₂ :=
    realizes_common_word_finish_mono h₁ h₂ hx
  rcases hy₁ with ⟨a, ha⟩
  rcases hy₂ with ⟨b, hb⟩
  have hab : a ≤ b := by
    omega
  have hFinishDiff :
      y₂ - y₁ = 2 * (b - a) := by
    omega
  have hDiff := realizes_common_word_difference h₁ h₂ hx
  have hProduct :
      2 ^ (twoSteps w + 1) ∣
        3 ^ oddSteps w * (x₂ - x₁) := by
    refine ⟨b - a, ?_⟩
    calc
      3 ^ oddSteps w * (x₂ - x₁)
          = 2 ^ twoSteps w * (y₂ - y₁) := hDiff.symm
      _ = 2 ^ twoSteps w * (2 * (b - a)) := by
            rw [hFinishDiff]
      _ = 2 ^ (twoSteps w + 1) * (b - a) := by
            rw [pow_succ]
            ring
  have hCoprime :
      Nat.Coprime
        (2 ^ (twoSteps w + 1))
        (3 ^ oddSteps w) :=
    Nat.Coprime.pow
      (twoSteps w + 1) (oddSteps w)
      (by decide : Nat.Coprime 2 3)
  have hDiv :
      2 ^ (twoSteps w + 1) ∣ x₂ - x₁ :=
    hCoprime.dvd_of_dvd_mul_left hProduct
  simpa [residueModulus] using hDiv

/--
整数実現を`residueModulus`の整数倍だけ下げるsigned replay。
開始を`M*k`下げると、終点は`2*3^L*k`だけ下がる。

`k`は整数なので、下方向だけでなく同じaffine合同類上の平行移動として使える。
-/
theorem realizesInt_sub_replay
    {w : ExpWord} {x y : ℤ}
    (h : RealizesInt w x y)
    (k : ℤ) :
    RealizesInt w
      (x - (residueModulus w : ℤ) * k)
      (y - 2 * (3 : ℤ) ^ oddSteps w * k) := by
  unfold RealizesInt at h ⊢
  rw [residueModulus_int_cast]
  calc
    (2 : ℤ) ^ twoSteps w *
          (y - 2 * (3 : ℤ) ^ oddSteps w * k)
        =
      (2 : ℤ) ^ twoSteps w * y -
        (2 : ℤ) ^ (twoSteps w + 1) *
          (3 : ℤ) ^ oddSteps w * k := by
            rw [pow_succ]
            ring
    _ =
      ((3 : ℤ) ^ oddSteps w * x + affineConstInt w) -
        (2 : ℤ) ^ (twoSteps w + 1) *
          (3 : ℤ) ^ oddSteps w * k := by
            rw [h]
    _ =
      (3 : ℤ) ^ oddSteps w *
          (x - (2 : ℤ) ^ (twoSteps w + 1) * k) +
        affineConstInt w := by
            ring

end ExpWord
end CollatzFirstLayer
