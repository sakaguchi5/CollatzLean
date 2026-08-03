import CollatzLean.CollatzFirstLayer.Center

/-!
# terminal pairと局所defect

二つのprefixのreturn分解から、omegaを2冪と奇数核へ分離する。
ここでは無限軌道やterminal抽出の存在は仮定せず、有限データ間の恒等式だけを証明する。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- prefixの2進重み `H+«λ»`。 -/
def alpha (w : ExpWord) («λ» : ℕ) : ℕ := twoSteps w + «λ»

/-- 二つのreturn分解から現れる一般defect核。 -/
def defectKernel (A B : ExpWord) (uA uB : ℕ) (s : ℕ) : ℤ :=
  (uA : ℤ) * determinant B -
  (2 : ℤ) ^ s * (uB : ℤ) * determinant A

/-- 二つのreturn prefix間のomega恒等式。 -/
theorem omega_from_two_returns
    {A B : ExpWord} {X YA YB «λA» «λB» uA uB : ℕ}
    (hA : Realizes A X YA) (hB : Realizes B X YB)
    (rA : IsReturn X YA «λA» uA) (rB : IsReturn X YB «λB» uB) :
    omega A B =
      (2 : ℤ) ^ alpha A «λA» * (uA : ℤ) * determinant B -
      (2 : ℤ) ^ alpha B «λB» * (uB : ℤ) * determinant A := by
  have dA := realizes_return_defect hA rA
  have dB := realizes_return_defect hB rB
  unfold omega alpha
  calc
    affineConstInt A * determinant B - affineConstInt B * determinant A
        = (affineConstInt A + determinant A * (X : ℤ)) * determinant B -
          (affineConstInt B + determinant B * (X : ℤ)) * determinant A := by ring
    _ = ((2 : ℤ) ^ (twoSteps A + «λA») * (uA : ℤ)) * determinant B -
          ((2 : ℤ) ^ (twoSteps B + «λB») * (uB : ℤ)) * determinant A := by
          rw [dA, dB]
    _ = (2 : ℤ) ^ (twoSteps A + «λA») * (uA : ℤ) * determinant B -
          (2 : ℤ) ^ (twoSteps B + «λB») * (uB : ℤ) * determinant A := by ring

/--
後側のalphaが `s` だけ大きい場合、omegaから前側の2冪をくくり出せる。
-/
theorem terminal_determinant_factorization
    {A B : ExpWord} {X YA YB «λA» «λB» uA uB s : ℕ}
    (hA : Realizes A X YA) (hB : Realizes B X YB)
    (rA : IsReturn X YA «λA» uA) (rB : IsReturn X YB «λB» uB)
    (hgap : alpha B «λB» = alpha A «λA» + s) :
    omega A B =
      (2 : ℤ) ^ alpha A «λA» * defectKernel A B uA uB s := by
  rw [omega_from_two_returns hA hB rA rB]
  unfold defectKernel
  rw [hgap, pow_add]
  ring

/-- 正の2冪と任意の整数の積は偶数である。 -/
lemma even_two_pow_mul_int {s : ℕ} (hs : 0 < s) (z : ℤ) :
    Even ((2 : ℤ) ^ s * z) := by
  cases s with
  | zero => simp at hs
  | succ t =>
      refine ⟨(2 : ℤ) ^ t * z, ?_⟩
      rw [pow_succ]
      ring

/--
正の総2除算数を持つ語のdeterminantは奇数である。
-/
lemma determinant_odd_of_twoSteps_pos {w : ExpWord}
    (hH : 0 < twoSteps w) : Odd (determinant w) := by
  unfold determinant
  apply Odd.sub_even
  · have h3 : Odd (3 : ℤ) := by
      exact ⟨1, by norm_num⟩
    exact h3.pow
  · have h2 : Even (2 : ℤ) := by
      exact ⟨1, by norm_num⟩
    exact h2.pow_of_ne_zero (Nat.ne_of_gt hH)

/--
奇数積から正の2冪倍を引いた核は奇数である。
-/
lemma defectKernel_odd
    {A B : ExpWord} {uA uB s : ℕ}
    (huA : Odd (uA : ℤ))
    (hDB : Odd (determinant B))
    (hs : 0 < s) :
    Odd (defectKernel A B uA uB s) := by
  unfold defectKernel
  apply Odd.sub_even
  · exact huA.mul hDB
  · have hEven := even_two_pow_mul_int hs ((uB : ℤ) * determinant A)
    simpa [mul_assoc] using hEven

/--
正のgapを持つterminal pairでは、omegaは前側の2冪と奇数核へ分解される。
-/
theorem terminal_factorization_with_odd_kernel
    {A B : ExpWord} {X YA YB «λA» «λB» uA uB s : ℕ}
    (hA : Realizes A X YA) (hB : Realizes B X YB)
    (rA : IsReturn X YA «λA» uA) (rB : IsReturn X YB «λB» uB)
    (hgap : alpha B «λB» = alpha A «λA» + s)
    (hs : 0 < s)
    (hBpos : 0 < twoSteps B) :
    ∃ κ : ℤ, Odd κ ∧
      omega A B = (2 : ℤ) ^ alpha A «λA» * κ := by
  refine ⟨defectKernel A B uA uB s, ?_, ?_⟩
  · exact defectKernel_odd rA.2.natCast
      (determinant_odd_of_twoSteps_pos hBpos) hs
  · exact terminal_determinant_factorization hA hB rA rB hgap

/--
後側prefixが `A ++ R` である場合、共通prefixが消費した2冪を消去し、
局所suffix `R` に対する `omega A R = 2^«λA» κ` を得る。
-/
theorem terminal_suffix_factorization
    {A R : ExpWord} {X YA YAR «λA» «λAR» uA uAR s : ℕ}
    (hA : Realizes A X YA) (hAR : Realizes (A ++ R) X YAR)
    (rA : IsReturn X YA «λA» uA) (rAR : IsReturn X YAR «λAR» uAR)
    (hgap : alpha (A ++ R) «λAR» = alpha A «λA» + s)
    (hs : 0 < s)
    (hARpos : 0 < twoSteps (A ++ R)) :
    ∃ κ : ℤ, Odd κ ∧ omega A R = (2 : ℤ) ^ «λA» * κ := by
  rcases terminal_factorization_with_odd_kernel
      hA hAR rA rAR hgap hs hARpos with ⟨κ, hκ, hω⟩
  refine ⟨κ, hκ, ?_⟩
  have hpow : (2 : ℤ) ^ twoSteps A ≠ 0 := by
    exact pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
  apply mul_left_cancel₀ hpow
  calc
    (2 : ℤ) ^ twoSteps A * omega A R
        = omega A (A ++ R) := (omega_append_right A R).symm
    _ = (2 : ℤ) ^ alpha A «λA» * κ := hω
    _ = (2 : ℤ) ^ twoSteps A * ((2 : ℤ) ^ «λA» * κ) := by
          unfold alpha
          rw [pow_add]
          ring

/--
terminal suffixのcenter差を、2冪、奇数核、二つのdeterminantへ分離する。
-/
theorem terminal_center_difference
    {A R : ExpWord} {X YA YAR «λA» «λAR» uA uAR s : ℕ}
    (hA : Realizes A X YA) (hAR : Realizes (A ++ R) X YAR)
    (rA : IsReturn X YA «λA» uA) (rAR : IsReturn X YAR «λAR» uAR)
    (hgap : alpha (A ++ R) «λAR» = alpha A «λA» + s)
    (hs : 0 < s)
    (hARpos : 0 < twoSteps (A ++ R))
    (hDA : determinant A ≠ 0) (hDR : determinant R ≠ 0) :
    ∃ κ : ℤ, Odd κ ∧
      center A - center R =
        (((2 : ℚ) ^ «λA») * (κ : ℚ)) /
          ((determinant A : ℚ) * (determinant R : ℚ)) := by
  rcases terminal_suffix_factorization
      hA hAR rA rAR hgap hs hARpos with ⟨κ, hκ, hω⟩
  refine ⟨κ, hκ, ?_⟩
  rw [center_difference_formula hDA hDR, hω]
  push_cast
  rfl

end ExpWord
end CollatzFirstLayer
