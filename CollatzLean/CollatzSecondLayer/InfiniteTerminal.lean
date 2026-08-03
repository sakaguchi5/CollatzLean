import CollatzLean.CollatzSecondLayer.C3Cylinder
import CollatzLean.CollatzFirstLayer.TerminalConsequences

/-!
# 無限terminal抽出

polynomial-small canonical C3 cylinder列から、terminal pairを無限部分列として
抽出するためのデータを定義する。

旧型が保存していた`realizes`、総2除算数正値、determinant非零は、実行証明と
非空性から自動導出する。terminalのalpha gapはsuffixのexactな深さ収支として
公開する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 第一層のterminal suffix定理を適用できる有限terminal pair。 -/
structure TerminalPairData where
  A : ExpWord
  R : ExpWord
  X : ℕ
  YA : ℕ
  YAR : ℕ
  lambdaA : ℕ
  lambdaAR : ℕ
  uA : ℕ
  uAR : ℕ
  gap : ℕ
  runA : Runs A X YA
  runR : Runs R YA YAR
  returnA : IsReturn X YA lambdaA uA
  returnAR : IsReturn X YAR lambdaAR uAR
  alpha_gap :
    alpha (A ++ R) lambdaAR = alpha A lambdaA + gap
  gap_pos : 0 < gap
  A_nonempty : A ≠ []
  R_nonempty : R ≠ []

namespace TerminalPairData

/-- 保存された実行証明から`A`の実現式を取得する。 -/
theorem realizesA (T : TerminalPairData) :
    Realizes T.A T.X T.YA :=
  T.runA.realizes

/-- 保存された実行証明から`R`の実現式を取得する。 -/
theorem realizesR (T : TerminalPairData) :
    Realizes T.R T.YA T.YAR :=
  T.runR.realizes

/-- 連続実行から`A ++ R`の実現式を取得する。 -/
theorem realizesAR (T : TerminalPairData) :
    Realizes (T.A ++ T.R) T.X T.YAR :=
  realizes_append T.runA.realizes T.runR.realizes

/-- 旧API互換：runから`A`の実現式を取得する。 -/
theorem realizesA_of_run (T : TerminalPairData) :
    Realizes T.A T.X T.YA :=
  T.realizesA

/-- 旧API互換：連続runから全語の実現式を取得する。 -/
theorem realizesAR_of_runs (T : TerminalPairData) :
    Realizes (T.A ++ T.R) T.X T.YAR :=
  T.realizesAR

/-- terminal pair全語は非空。 -/
theorem total_nonempty (T : TerminalPairData) :
    T.A ++ T.R ≠ [] := by
  exact List.append_ne_nil_of_left_ne_nil T.A_nonempty T.R

/-- terminal pair全語は有効。 -/
theorem total_valid (T : TerminalPairData) :
    Valid (T.A ++ T.R) :=
  valid_append T.runA.valid T.runR.valid

/-- terminal pair全語の総2除算数は正。 -/
theorem total_twoSteps_pos (T : TerminalPairData) :
    0 < twoSteps (T.A ++ T.R) :=
  twoSteps_pos_of_valid_nonempty T.total_valid T.total_nonempty

/-- `A`のdeterminant非零性はrunと非空性から自動。 -/
theorem detA_ne (T : TerminalPairData) :
    determinant T.A ≠ 0 :=
  T.runA.determinant_ne_zero T.A_nonempty

/-- `R`のdeterminant非零性はrunと非空性から自動。 -/
theorem detR_ne (T : TerminalPairData) :
    determinant T.R ≠ 0 :=
  T.runR.determinant_ne_zero T.R_nonempty

/-- alpha gapをsuffixのexactな深さ収支へ展開する。 -/
theorem suffixDepthBalance (T : TerminalPairData) :
    twoSteps T.R + T.lambdaAR = T.lambdaA + T.gap :=
  alpha_gap_suffix_balance T.alpha_gap

/-- terminal suffixのomegaは`lambdaA`で正確に止まる。 -/
theorem omegaExactDepth (T : TerminalPairData) :
    ∃ kappa : ℤ,
      ExactTwoFactorInt (omega T.A T.R) T.lambdaA kappa :=
  terminal_suffix_exact_twoFactor
    T.realizesA T.realizesAR T.returnA T.returnAR
    T.alpha_gap T.gap_pos T.total_valid T.total_nonempty

/-- terminal suffixのomegaは非零。 -/
theorem omega_ne_zero (T : TerminalPairData) :
    omega T.A T.R ≠ 0 :=
  terminal_suffix_omega_ne_zero
    T.realizesA T.realizesAR T.returnA T.returnAR
    T.alpha_gap T.gap_pos T.total_valid T.total_nonempty

/-- terminal pairのomegaはanchor深さの2冪と奇数核へ分解される。 -/
theorem oddKernel (T : TerminalPairData) :
    ∃ kappa : ℤ, Odd kappa ∧
      omega T.A T.R = (2 : ℤ) ^ T.lambdaA * kappa := by
  rcases T.omegaExactDepth with ⟨kappa, homega, hkappa⟩
  exact ⟨kappa, hkappa, homega⟩

/-- terminal pairのcenter差分解。 -/
theorem centerDifference (T : TerminalPairData) :
    ∃ kappa : ℤ, Odd kappa ∧
      center T.A - center T.R =
        (((2 : ℚ) ^ T.lambdaA) * (kappa : ℚ)) /
          ((determinant T.A : ℚ) * (determinant T.R : ℚ)) := by
  exact terminal_center_difference
    T.realizesA T.realizesAR T.returnA T.returnAR
    T.alpha_gap T.gap_pos T.total_twoSteps_pos
    T.detA_ne T.detR_ne

/-- terminal pairの二つのcenterは一致しない。 -/
theorem center_ne (T : TerminalPairData) :
    center T.A ≠ center T.R := by
  intro hcenter
  rcases T.centerDifference with ⟨kappa, hkappaOdd, hdiff⟩
  have hkappa : kappa ≠ 0 := by
    intro hk
    subst kappa
    rcases hkappaOdd with ⟨z, hz⟩
    omega
  have htwo : (2 : ℚ) ^ T.lambdaA ≠ 0 := by norm_num
  have hkappaQ : (kappa : ℚ) ≠ 0 := by exact_mod_cast hkappa
  have hdetA : (determinant T.A : ℚ) ≠ 0 := by exact_mod_cast T.detA_ne
  have hdetR : (determinant T.R : ℚ) ≠ 0 := by exact_mod_cast T.detR_ne
  have hquot :
      (((2 : ℚ) ^ T.lambdaA) * (kappa : ℚ)) /
          ((determinant T.A : ℚ) * (determinant T.R : ℚ)) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero htwo hkappaQ)
      (mul_ne_zero hdetA hdetR)
  apply hquot
  rw [← hdiff, hcenter, sub_self]

end TerminalPairData

/--
canonical C3 cylinder列から抽出された無限terminal部分列。

`sourceIndex`は元列の狭義単調な添字であり、各terminal pairはそのcylinderの
全語、開始値、終点に一致する。さらに、抽出後も元cylinder長が無限大へ進む。
-/
structure InfiniteTerminalExtraction
    {O : OddOrbit} (S : C3CylinderSequence O) where
  sourceIndex : ℕ → ℕ
  sourceIndex_strict : StrictMono sourceIndex
  pair : ℕ → TerminalPairData
  sourceRelation : ∀ n : ℕ,
    (pair n).A ++ (pair n).R =
      (S.cylinder (sourceIndex n)).snapshot.word
  sourceStart : ∀ n : ℕ,
    (pair n).X =
      (S.cylinder (sourceIndex n)).snapshot.start
  sourceFinish : ∀ n : ℕ,
    (pair n).YAR =
      (S.cylinder (sourceIndex n)).snapshot.finish
  sourceLengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (S.cylinder (sourceIndex j)).toFirstCrossingCylinder.length

/-- 無限terminal部分列を抽出できないことが実在する。 -/
def HasInfiniteTerminalExtractionObstruction : Prop :=
  ∃ O : OddOrbit, ∃ S : C3CylinderSequence O,
    ¬ Nonempty (InfiniteTerminalExtraction S)

/-- 一つのC3 cylinder列について、無限terminal抽出または抽出不能性を得る。 -/
theorem infiniteTerminalExtraction_split
    {O : OddOrbit} (S : C3CylinderSequence O) :
    HasInfiniteTerminalExtractionObstruction ∨
      Nonempty (InfiniteTerminalExtraction S) := by
  classical
  by_cases h : Nonempty (InfiniteTerminalExtraction S)
  · exact Or.inr h
  · exact Or.inl ⟨O, S, h⟩

end CollatzSecondLayer
