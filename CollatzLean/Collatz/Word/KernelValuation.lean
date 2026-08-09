import CollatzLean.Collatz.Word.Kernel

/-!
# kernelの2進因子と奇数核

旧Terminal.leanにあった有限kernelのodd-factorization部分だけを復元する。
-/

namespace Collatz
namespace Word

/-- 正の2冪と整数の積は偶数。 -/
lemma even_two_pow_mul_int {s : ℕ} (hs : 0 < s) (z : ℤ) :
    Even ((2 : ℤ) ^ s * z) := by
  cases s with
  | zero => simp at hs
  | succ t =>
      refine ⟨(2 : ℤ) ^ t * z, ?_⟩
      rw [pow_succ]
      ring

/-- 正の総2進指数を持つ語のdeterminantは奇数。 -/
lemma determinant_odd_of_twoSteps_pos
    {w : Collatz.Word} (hH : 0 < w.twoSteps) : Odd w.determinant := by
  unfold determinant
  apply Odd.sub_even
  · have h3 : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    exact h3.pow
  · have h2 : Even (2 : ℤ) := ⟨1, by norm_num⟩
    exact h2.pow_of_ne_zero (Nat.ne_of_gt hH)

/-- 奇数積から正の2冪倍を引いたdefect kernelは奇数。 -/
lemma defectKernel_odd
    {A B : Collatz.Word} {uA uB s : ℕ}
    (huA : Odd (uA : ℤ))
    (hDB : Odd B.determinant)
    (hs : 0 < s) :
    Odd (A.defectKernel B uA uB s) := by
  unfold defectKernel
  apply Odd.sub_even
  · exact huA.mul hDB
  · have hEven := even_two_pow_mul_int hs ((uB : ℤ) * A.determinant)
    simpa [mul_assoc] using hEven

/-- depth差が正ならomegaは前側2冪と奇数核へ分解される。 -/
theorem terminal_factorization_with_odd_kernel
    {A B : Collatz.Word} {X YA YB lambdaA lambdaB uA uB s : ℕ}
    (hA : A.Realizes X YA) (hB : B.Realizes X YB)
    (rA : IsReturn X YA lambdaA uA) (rB : IsReturn X YB lambdaB uB)
    (hgap : B.returnDepth lambdaB = A.returnDepth lambdaA + s)
    (hs : 0 < s)
    (hBpos : 0 < B.twoSteps) :
    ∃ kappa : ℤ, Odd kappa ∧
      A.omega B = (2 : ℤ) ^ A.returnDepth lambdaA * kappa := by
  refine ⟨A.defectKernel B uA uB s, ?_, ?_⟩
  · exact defectKernel_odd rA.2.natCast
      (determinant_odd_of_twoSteps_pos hBpos) hs
  · exact terminal_factorization hA hB rA rB hgap

/-- 後側prefixが`A ++ R`なら共通prefixの2冪を消去できる。 -/
theorem terminal_suffix_factorization
    {A R : Collatz.Word} {X YA YAR lambdaA lambdaAR uA uAR s : ℕ}
    (hA : A.Realizes X YA) (hAR : (A ++ R).Realizes X YAR)
    (rA : IsReturn X YA lambdaA uA) (rAR : IsReturn X YAR lambdaAR uAR)
    (hgap : (A ++ R).returnDepth lambdaAR = A.returnDepth lambdaA + s)
    (hs : 0 < s)
    (hARpos : 0 < (A ++ R).twoSteps) :
    ∃ kappa : ℤ, Odd kappa ∧ A.omega R = (2 : ℤ) ^ lambdaA * kappa := by
  rcases terminal_factorization_with_odd_kernel
      hA hAR rA rAR hgap hs hARpos with ⟨kappa, hk, homega⟩
  refine ⟨kappa, hk, ?_⟩
  have hpow : (2 : ℤ) ^ A.twoSteps ≠ 0 :=
    pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
  apply mul_left_cancel₀ hpow
  calc
    (2 : ℤ) ^ A.twoSteps * A.omega R = A.omega (A ++ R) :=
      (omega_append_right A R).symm
    _ = (2 : ℤ) ^ A.returnDepth lambdaA * kappa := homega
    _ = (2 : ℤ) ^ A.twoSteps * ((2 : ℤ) ^ lambdaA * kappa) := by
      unfold returnDepth
      rw [pow_add]
      ring

/-- terminal suffixのcenter差を2冪・奇数核・determinantへ分離する。 -/
theorem terminal_center_difference
    {A R : Collatz.Word} {X YA YAR lambdaA lambdaAR uA uAR s : ℕ}
    (hA : A.Realizes X YA) (hAR : (A ++ R).Realizes X YAR)
    (rA : IsReturn X YA lambdaA uA) (rAR : IsReturn X YAR lambdaAR uAR)
    (hgap : (A ++ R).returnDepth lambdaAR = A.returnDepth lambdaA + s)
    (hs : 0 < s)
    (hARpos : 0 < (A ++ R).twoSteps)
    (hDA : A.determinant ≠ 0) (hDR : R.determinant ≠ 0) :
    ∃ kappa : ℤ, Odd kappa ∧
      A.center - R.center =
        (((2 : ℚ) ^ lambdaA) * (kappa : ℚ)) /
          ((A.determinant : ℚ) * (R.determinant : ℚ)) := by
  rcases terminal_suffix_factorization
      hA hAR rA rAR hgap hs hARpos with ⟨kappa, hk, homega⟩
  refine ⟨kappa, hk, ?_⟩
  rw [center_difference hDA hDR, homega]
  push_cast
  rfl

end Word
end Collatz
