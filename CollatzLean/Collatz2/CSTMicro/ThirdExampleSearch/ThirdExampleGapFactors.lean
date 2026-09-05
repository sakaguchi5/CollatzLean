import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ExactGapOneBeattyCertificate
import Mathlib.Data.ZMod.Basic
set_option linter.style.nativeDecide false

/-!
# 第3例探索 2: target gap の小さい固定因子

固定 target の coefficient gap

  G = 2^(H+1) - 3^(p+1)

には、探索で安価に使える小因子がある。
巨大整数 `G` 自体は生成せず、各 modulus 上の modular power だけを計算する。

確認する因子は

  79,
  1153,
  5_821_007

であり、その積は

  530_218_064_609.

従って真の gap-one certificate の `gap` はこの modulus 上で 0 になる。
その結果 `m * gap` 項が消え、deficit には `m` 非依存の合同条件が生じる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/-- target gap を消す固定合同 modulus。 -/
def thirdExampleGapFactorModulus : ℕ :=
  530_218_064_609

/-- 三つの確認済み因子の積。 -/
theorem thirdExampleGapFactorModulus_eq_product :
    thirdExampleGapFactorModulus = 79 * 1153 * 5_821_007 := by
  norm_num [thirdExampleGapFactorModulus]

/-- `79` 上で target gap は 0。巨大な `G` は作らない。 -/
theorem thirdExampleGapFactor79 :
    (2 : ZMod 79) ^ (thirdExampleTargetH + 1) -
      (3 : ZMod 79) ^ (thirdExampleTargetP + 1) = 0 := by
  native_decide

/-- `1153` 上で target gap は 0。 -/
theorem thirdExampleGapFactor1153 :
    (2 : ZMod 1153) ^ (thirdExampleTargetH + 1) -
      (3 : ZMod 1153) ^ (thirdExampleTargetP + 1) = 0 := by
  native_decide

/-- `5_821_007` 上で target gap は 0。 -/
theorem thirdExampleGapFactor5821007 :
    (2 : ZMod 5_821_007) ^ (thirdExampleTargetH + 1) -
      (3 : ZMod 5_821_007) ^ (thirdExampleTargetP + 1) = 0 := by
  native_decide

/--
三因子をまとめた modulus 上でも target gap は exact に 0。
後段はこの一つだけを使えばよい。
-/
theorem thirdExampleGapFactorModulus_spec :
    (2 : ZMod thirdExampleGapFactorModulus) ^ (thirdExampleTargetH + 1) -
      (3 : ZMod thirdExampleGapFactorModulus) ^ (thirdExampleTargetP + 1) = 0 := by
  native_decide

/--
真の target certificate の `gap` は固定 modulus 上で 0。
certificate の `next_gap_equation` と上の modular checkpoint だけを使う。
-/
theorem thirdExampleCertificate_gap_eq_zero_mod
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    (gap : ZMod thirdExampleGapFactorModulus) = 0 := by
  have hGap := congrArg
    (fun n : ℕ => (n : ZMod thirdExampleGapFactorModulus))
    C.next_gap_equation
  push_cast at hGap
  calc
    (gap : ZMod thirdExampleGapFactorModulus) =
        ((3 : ZMod thirdExampleGapFactorModulus) ^
            (thirdExampleTargetP + 1) + (gap : ZMod thirdExampleGapFactorModulus)) -
          (3 : ZMod thirdExampleGapFactorModulus) ^
            (thirdExampleTargetP + 1) := by ring
    _ =
        (2 : ZMod thirdExampleGapFactorModulus) ^
            (thirdExampleTargetH + 1) -
          (3 : ZMod thirdExampleGapFactorModulus) ^
            (thirdExampleTargetP + 1) := by rw [hGap]
    _ = 0 := thirdExampleGapFactorModulus_spec

/--
従って deficit equation をこの modulus へ写すと `m*gap` が完全に消える。
ここでは critical budget 自体は proof-side の値のまま保持する。
-/
theorem thirdExampleDeficit_gapFree_mod
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    (deficit : ZMod thirdExampleGapFactorModulus) =
      (3 : ZMod thirdExampleGapFactorModulus) ^ thirdExampleTargetP +
        (Word.criticalAffineConst thirdExampleTargetP :
          ZMod thirdExampleGapFactorModulus) -
        (2 : ZMod thirdExampleGapFactorModulus) ^ thirdExampleTargetH := by
  have hDef := congrArg
    (fun n : ℕ => (n : ZMod thirdExampleGapFactorModulus))
    C.deficit_equation
  push_cast at hDef
  have hGapZero := thirdExampleCertificate_gap_eq_zero_mod C
  rw [hGapZero] at hDef
  simp only [mul_zero, add_zero] at hDef
  calc
    (deficit : ZMod thirdExampleGapFactorModulus) =
        ((2 : ZMod thirdExampleGapFactorModulus) ^ thirdExampleTargetH +
          (deficit : ZMod thirdExampleGapFactorModulus)) -
          (2 : ZMod thirdExampleGapFactorModulus) ^ thirdExampleTargetH := by ring
    _ =
        ((3 : ZMod thirdExampleGapFactorModulus) ^ thirdExampleTargetP +
          (Word.criticalAffineConst thirdExampleTargetP :
            ZMod thirdExampleGapFactorModulus)) -
          (2 : ZMod thirdExampleGapFactorModulus) ^ thirdExampleTargetH := by
            rw [← hDef]
    _ = _ := by ring

end ThirdExampleSearch
end CSTMicro
end Collatz2
