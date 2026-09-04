import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCanonical42FullPrefixBridge

/-!
# 第3例探索 D1: 有限剰余 SearchState

巨大な exact affine state や `PureBProfileObstruction` を探索 hot path に持ち込まず、
第3例 target 全体を通した後に必要な二つの剰余だけを保持する。

* 左側: `mod 2^68`
* 右側: `mod 3^42`

ここで保持する値は start/end value そのものではなく、
`criticalPrefixDefectZ thirdExampleTargetP y` の二つの剰余像である。
この区別を型名・field 名に残し、後段で別の Hensel endpoint residue と混同しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
第3例 target の full prefix defect に対する実行用有限状態。

proof object は一切持たない。`native_decide` 側へ渡すのはこの種の有限データだけにする。
-/
@[ext]
structure ThirdExampleResidueSearchState where
  fullDefectModTwo : ZMod thirdExampleLeftModulus
  fullDefectModThree : ZMod thirdExampleRightModulus
  deriving DecidableEq

/--
canonical 42-block modular fold を左右二つの固定 modulus で一度ずつ評価して
有限 SearchState を作る。

この定義自身は certification を要求しない。certification は correctness theorem 側だけで使う。
-/
def thirdExampleResidueSearchState
    (y : ℤ) : ThirdExampleResidueSearchState :=
  {
    fullDefectModTwo :=
      (thirdExampleCanonical42ModularFold
        thirdExampleLeftModulus y).apply 0
    fullDefectModThree :=
      (thirdExampleCanonical42ModularFold
        thirdExampleRightModulus y).apply 0
  }

@[simp] theorem thirdExampleResidueSearchState_fullDefectModTwo
    (y : ℤ) :
    (thirdExampleResidueSearchState y).fullDefectModTwo =
      (thirdExampleCanonical42ModularFold
        thirdExampleLeftModulus y).apply 0 := by
  rfl

@[simp] theorem thirdExampleResidueSearchState_fullDefectModThree
    (y : ℤ) :
    (thirdExampleResidueSearchState y).fullDefectModThree =
      (thirdExampleCanonical42ModularFold
        thirdExampleRightModulus y).apply 0 := by
  rfl

/--
proof-side で比較する exact canonical full state の二つの剰余像。

この定義は hot path 用ではない。D0 bridge の到達先を一つの record に束ねるためだけに置く。
-/
def thirdExampleExactResidueSearchState
    (y : ℤ) : ThirdExampleResidueSearchState :=
  {
    fullDefectModTwo :=
      ((thirdExampleExactCanonicalFullState y : ℤ) :
        ZMod thirdExampleLeftModulus)
    fullDefectModThree :=
      ((thirdExampleExactCanonicalFullState y : ℤ) :
        ZMod thirdExampleRightModulus)
  }

/--
左右の packet certification があれば、実行用 SearchState は
exact canonical full state の二つの剰余像と record 全体として一致する。
-/
theorem thirdExampleResidueSearchState_eq_exact
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    (y : ℤ) :
    thirdExampleResidueSearchState y =
      thirdExampleExactResidueSearchState y := by
  apply ThirdExampleResidueSearchState.ext
  · exact
      thirdExampleCanonical42LeftFold_apply_zero_eq_exactCanonicalFullState
        CertL y
  · exact
      thirdExampleCanonical42RightFold_apply_zero_eq_exactCanonicalFullState
        CertR y

/-- 左剰余だけを直接取り出す correctness wrapper。 -/
theorem thirdExampleResidueSearchState_left_exact
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (y : ℤ) :
    (thirdExampleResidueSearchState y).fullDefectModTwo =
      ((thirdExampleExactCanonicalFullState y : ℤ) :
        ZMod thirdExampleLeftModulus) := by
  exact
    thirdExampleCanonical42LeftFold_apply_zero_eq_exactCanonicalFullState
      CertL y

/-- 右剰余だけを直接取り出す correctness wrapper。 -/
theorem thirdExampleResidueSearchState_right_exact
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    (y : ℤ) :
    (thirdExampleResidueSearchState y).fullDefectModThree =
      ((thirdExampleExactCanonicalFullState y : ℤ) :
        ZMod thirdExampleRightModulus) := by
  exact
    thirdExampleCanonical42RightFold_apply_zero_eq_exactCanonicalFullState
      CertR y

end ThirdExampleSearch
end CSTMicro
end Collatz2
