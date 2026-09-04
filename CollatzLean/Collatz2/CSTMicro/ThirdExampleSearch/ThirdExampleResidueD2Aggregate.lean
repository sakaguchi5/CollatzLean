import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueSearchState
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleHensel42ResidueCompleteness
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.StartValuePrefix68
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.AffineSuffixModThree

/-!
# 第3例探索 D2 集約: exact mathematics から有限剰余 packet へ

D1 の full-prefix defect state と、旧 D4 を置換する42段 Hensel residue を一つの層でまとめる。

ここで意図的に二種類の `mod 3^42` 値を区別する。

1. `fullDefectModThree`
   = full critical-prefix defect の `mod 3^42` 像。
2. `endpointModThree`
   = gap-one endpoint candidate 自身の `mod 3^42` 像。

両者が等しいという新しい数学命題はこのファイルでは仮定も主張もしない。
後段 verifier が要求する compatibility equation を別途課すことで、
未証明の bridge を SearchState に紛れ込ませない。

D2 相当としてここで確定するのは、

* canonical 42-block fold -> exact full defect residue,
* 42段 Hensel fold -> exact endpoint residue,
* 左 68 block -> start value residue の一意性,
* 右 42 block -> affine suffix residue の exact 切断,

という lossless な有限化である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
D2 で verifier 側へ渡す有限 packet。

`defectState` と `endpointModThree` を分離していることが重要。
proof object や巨大 exact integer は field に持たない。
-/
@[ext]
structure ThirdExampleD2FinitePacket where
  defectState : ThirdExampleResidueSearchState
  endpointModThree : ℕ
  deriving DecidableEq

/--
数学側の parameter `y` と gap-one endpoint `endpoint` から有限 packet を作る。

この定義は完全に計算用であり、certification は受け取らない。
-/
def thirdExampleD2FinitePacket
    (y : ℤ)
    (endpoint : ℕ) : ThirdExampleD2FinitePacket :=
  {
    defectState := thirdExampleResidueSearchState y
    endpointModThree := thirdExampleHensel42Residue endpoint
  }

@[simp] theorem thirdExampleD2FinitePacket_defectState
    (y : ℤ)
    (endpoint : ℕ) :
    (thirdExampleD2FinitePacket y endpoint).defectState =
      thirdExampleResidueSearchState y := by
  rfl

@[simp] theorem thirdExampleD2FinitePacket_endpointModThree
    (y : ℤ)
    (endpoint : ℕ) :
    (thirdExampleD2FinitePacket y endpoint).endpointModThree =
      thirdExampleHensel42Residue endpoint := by
  rfl

/--
D2 の中心 soundness packet。

左右の full-defect state は D0 の exact canonical state の剰余像であり、
endpoint 側は上界仮定なしで exact に `endpoint mod 3^42` である。
-/
theorem thirdExampleD2FinitePacket_exact
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (CertR : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    (y : ℤ)
    (endpoint : ℕ) :
    ((thirdExampleD2FinitePacket y endpoint).defectState.fullDefectModTwo =
        ((thirdExampleExactCanonicalFullState y : ℤ) :
          ZMod thirdExampleLeftModulus)) ∧
    ((thirdExampleD2FinitePacket y endpoint).defectState.fullDefectModThree =
        ((thirdExampleExactCanonicalFullState y : ℤ) :
          ZMod thirdExampleRightModulus)) ∧
    ((thirdExampleD2FinitePacket y endpoint).endpointModThree =
        endpoint % thirdExampleRightModulus) := by
  constructor
  · exact thirdExampleResidueSearchState_left_exact CertL y
  · constructor
    · exact thirdExampleResidueSearchState_right_exact CertR y
    · exact thirdExampleHensel42Residue_eq_mod endpoint

/--
左 modulus の名前を使った `StartValuePrefix68` wrapper。
`3^68 * n + B68 = 0 (mod 2^68)` が成立すれば、
start residue は固定 inverse により一意。
-/
theorem startValue_eq_thirdExampleLeftResidue
    (n B68 : ℕ)
    (hResidue :
      (((3 : ℕ) ^ 68 : ZMod thirdExampleLeftModulus) *
          (n : ZMod thirdExampleLeftModulus) +
        (B68 : ZMod thirdExampleLeftModulus)) = 0) :
    (n : ZMod thirdExampleLeftModulus) =
      - (prefix68Inverse : ZMod thirdExampleLeftModulus) *
        (B68 : ZMod thirdExampleLeftModulus) := by
  exact startValue_eq_prefix68Residue n B68 hResidue

/--
右 modulus の名前を使った 42-block suffix wrapper。
full affine constant の左側が `3^42` を因子に持つなら、
`mod 3^42` では右 collar だけが exact に残る。
-/
theorem affineConst_mod_thirdExampleRightModulus_of_suffix42
    (fullB leftPart prefixH B42 : ℕ)
    (hSplit :
      fullB =
        3 ^ 42 * leftPart +
          2 ^ prefixH * B42) :
    (fullB : ZMod thirdExampleRightModulus) =
      ((2 : ℕ) ^ prefixH : ZMod thirdExampleRightModulus) *
        (B42 : ZMod thirdExampleRightModulus) := by
  exact
    affineConst_mod_threePow_of_suffix42
      fullB leftPart prefixH B42 hSplit

/--
D2 の endpoint residue は常に right modulus 未満。
このため後段の finite verifier では canonical Nat representative のまま保持できる。
-/
theorem thirdExampleD2FinitePacket_endpointModThree_lt
    (y : ℤ)
    (endpoint : ℕ) :
    (thirdExampleD2FinitePacket y endpoint).endpointModThree <
      thirdExampleRightModulus := by
  exact thirdExampleHensel42Residue_lt_rightModulus endpoint

/--
42段 endpoint residue を `ZMod (3^42)` として読む wrapper。
Nat representation と modular representation の間で情報を失わない。
-/
theorem thirdExampleD2FinitePacket_endpointModThree_eq_zmod_val
    (y : ℤ)
    (endpoint : ℕ) :
    (thirdExampleD2FinitePacket y endpoint).endpointModThree =
      (endpoint : ZMod thirdExampleRightModulus).val := by
  exact thirdExampleHensel42Residue_eq_rightZMod_val endpoint

end ThirdExampleSearch
end CSTMicro
end Collatz2
