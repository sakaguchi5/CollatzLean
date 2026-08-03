import CollatzLean.CollatzFirstLayer.Terminal
import CollatzLean.CollatzFirstLayer.Orbit

/-!
# terminal構造からの強い派生定理

非空の有効語ではdeterminant非零性を自動導出し、terminalのalpha gapを
suffixのexactな深さ収支へ展開する。さらにomegaの2進深さを、奇数核を
伴う完全分解として保存する。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- 正の指数を持つ非空語ではdeterminantは0でない。 -/
theorem determinant_ne_zero_of_valid_nonempty
    {w : ExpWord}
    (hvalid : Valid w)
    (hne : w ≠ []) :
    determinant w ≠ 0 := by
  have hH : 0 < twoSteps w :=
    twoSteps_pos_of_valid_nonempty hvalid hne
  have hodd : Odd (determinant w) :=
    determinant_odd_of_twoSteps_pos hH
  intro hzero
  rw [hzero] at hodd
  rcases hodd with ⟨k, hk⟩
  omega

namespace Runs

/-- 非空の実軌道語ではdeterminant非零性は自動。 -/
theorem determinant_ne_zero
    {w : ExpWord} {X Y : ℕ}
    (h : Runs w X Y)
    (hne : w ≠ []) :
    determinant w ≠ 0 :=
  determinant_ne_zero_of_valid_nonempty h.valid hne

end Runs

/--
`alpha(A++R,λAR)=alpha(A,λA)+gap`をsuffixのexactな深さ収支へ展開する。
-/
theorem alpha_gap_suffix_balance
    {A R : ExpWord} {lambdaA lambdaAR gap : ℕ}
    (hgap :
      alpha (A ++ R) lambdaAR =
        alpha A lambdaA + gap) :
    twoSteps R + lambdaAR = lambdaA + gap := by
  unfold alpha at hgap
  rw [twoSteps_append] at hgap
  omega

/-- 整数の完全2進分解。 -/
def ExactTwoFactorInt (z : ℤ) (d : ℕ) (u : ℤ) : Prop :=
  z = (2 : ℤ) ^ d * u ∧ Odd u

/-- terminal suffixのomegaは深さ`lambdaA`で正確に止まる。 -/
theorem terminal_suffix_exact_twoFactor
    {A R : ExpWord} {X YA YAR lambdaA lambdaAR uA uAR gap : ℕ}
    (hA : Realizes A X YA)
    (hAR : Realizes (A ++ R) X YAR)
    (rA : IsReturn X YA lambdaA uA)
    (rAR : IsReturn X YAR lambdaAR uAR)
    (hgap :
      alpha (A ++ R) lambdaAR =
        alpha A lambdaA + gap)
    (hgapPos : 0 < gap)
    (hvalid : Valid (A ++ R))
    (hne : A ++ R ≠ []) :
    ∃ kappa : ℤ,
      ExactTwoFactorInt (omega A R) lambdaA kappa := by
  have hH : 0 < twoSteps (A ++ R) :=
    twoSteps_pos_of_valid_nonempty hvalid hne
  rcases terminal_suffix_factorization
      hA hAR rA rAR hgap hgapPos hH with
    ⟨kappa, hkappa, homega⟩
  exact ⟨kappa, homega, hkappa⟩

/-- terminal suffixのomegaは0にならない。 -/
theorem terminal_suffix_omega_ne_zero
    {A R : ExpWord} {X YA YAR lambdaA lambdaAR uA uAR gap : ℕ}
    (hA : Realizes A X YA)
    (hAR : Realizes (A ++ R) X YAR)
    (rA : IsReturn X YA lambdaA uA)
    (rAR : IsReturn X YAR lambdaAR uAR)
    (hgap :
      alpha (A ++ R) lambdaAR =
        alpha A lambdaA + gap)
    (hgapPos : 0 < gap)
    (hvalid : Valid (A ++ R))
    (hne : A ++ R ≠ []) :
    omega A R ≠ 0 := by
  rcases terminal_suffix_exact_twoFactor
      hA hAR rA rAR hgap hgapPos hvalid hne with
    ⟨kappa, homega, hkappa⟩
  intro hzero
  rw [hzero] at homega
  have hkappaZero : kappa = 0 := by
    have hpow : (2 : ℤ) ^ lambdaA ≠ 0 := by norm_num
    exact (mul_eq_zero.mp homega.symm).resolve_left hpow
  rw [hkappaZero] at hkappa
  rcases hkappa with ⟨k, hk⟩
  omega

end ExpWord
end CollatzFirstLayer
