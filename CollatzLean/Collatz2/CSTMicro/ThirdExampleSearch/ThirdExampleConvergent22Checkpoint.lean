import Mathlib.Tactic

/-!
# 第3例探索: convergent 22 の軽量 checkpoint

このファイルは固定巨大 window の**実行用 checkpoint**だけを持つ。

重要な設計方針:

* `criticalPowerP 22` / `criticalPowerQ 22` を定義から再計算しない。
* `actualCriticalOstrowskiRank 6_586_818_669` も実行時には呼ばない。
* rank、scale、block length、multiplicity を literal な小整数データとして保持する。
* 42 block の個数と total mass は、この literal table だけから検証する。

actual Farey/convergent 列との一致証明は certification 層の仕事として分離する。
探索 hot path はこのファイルの literal checkpoint だけを参照する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 第3例探索で最初に残る巨大 window の odd-step 数。 -/
def thirdExampleTargetP : ℕ :=
  6_586_818_669

/-- 同じ window の first-drop terminal two-depth。 -/
def thirdExampleTargetH : ℕ :=
  10_439_860_590

/-- rebound 側の convergent numerator checkpoint。 -/
def thirdExampleConvergent22P : ℕ :=
  6_586_818_670

/-- rebound 側の convergent denominator checkpoint。 -/
def thirdExampleConvergent22Q : ℕ :=
  10_439_860_591

/-- 固定 window で使う Ostrowski rank checkpoint。 -/
def thirdExampleTargetRank : ℕ :=
  19

/-- 固定 window の最大 scale checkpoint。 -/
def thirdExampleMaxScale : ℕ :=
  21

@[simp] theorem thirdExampleTargetP_succ :
    thirdExampleTargetP + 1 = thirdExampleConvergent22P := by
  norm_num [thirdExampleTargetP, thirdExampleConvergent22P]

@[simp] theorem thirdExampleTargetH_succ :
    thirdExampleTargetH + 1 = thirdExampleConvergent22Q := by
  norm_num [thirdExampleTargetH, thirdExampleConvergent22Q]

@[simp] theorem thirdExampleTargetRank_add_two :
    thirdExampleTargetRank + 2 = thirdExampleMaxScale := by
  norm_num [thirdExampleTargetRank, thirdExampleMaxScale]

/--
固定 window の canonical block を表す軽量 record。
`length` は actual `criticalPowerP scale` の値を literal checkpoint として保持する。
hot path では `criticalPowerP` 自体を評価しない。
-/
structure ThirdExampleCheckpointBlock where
  scale : ℕ
  length : ℕ
  multiplicity : ℕ
  deriving DecidableEq, Repr

/--
固定 window の grouped canonical Ostrowski skeleton。

scale 3  : length 2           × 2
scale 5  : length 12          × 3
scale 7  : length 53          × 5
scale 9  : length 665         × 23
scale 11 : length 31_867      × 2
scale 13 : length 111_202     × 1
scale 15 : length 10_590_737  × 1
scale 17 : length 53_715_833  × 3
scale 19 : length 225_644_606 × 1
scale 21 : length 6_189_245_291 × 1
-/
def thirdExampleCheckpointBlocks : List ThirdExampleCheckpointBlock :=
  [ { scale := 3,  length := 2,             multiplicity := 2  }
  , { scale := 5,  length := 12,            multiplicity := 3  }
  , { scale := 7,  length := 53,            multiplicity := 5  }
  , { scale := 9,  length := 665,           multiplicity := 23 }
  , { scale := 11, length := 31_867,        multiplicity := 2  }
  , { scale := 13, length := 111_202,       multiplicity := 1  }
  , { scale := 15, length := 10_590_737,    multiplicity := 1  }
  , { scale := 17, length := 53_715_833,    multiplicity := 3  }
  , { scale := 19, length := 225_644_606,   multiplicity := 1  }
  , { scale := 21, length := 6_189_245_291, multiplicity := 1  }
  ]

/-- grouped skeleton は10種類の scale だけを持つ。 -/
theorem thirdExampleCheckpointBlocks_length :
    thirdExampleCheckpointBlocks.length = 10 := by
  norm_num [thirdExampleCheckpointBlocks]

/-- grouped skeleton が表す block 総数。 -/
def thirdExampleCheckpointBlockCount : ℕ :=
  (thirdExampleCheckpointBlocks.map
    (fun B => B.multiplicity)).sum

/-- grouped skeleton は exact に42 block。 -/
theorem thirdExampleCheckpointBlockCount_eq :
    thirdExampleCheckpointBlockCount = 42 := by
  norm_num [thirdExampleCheckpointBlockCount, thirdExampleCheckpointBlocks]

/-- grouped skeleton が覆う odd-column の total mass。 -/
def thirdExampleCheckpointMass : ℕ :=
  (thirdExampleCheckpointBlocks.map
    (fun B => B.multiplicity * B.length)).sum

/-- literal checkpoint だけから total mass が target `p` に一致する。 -/
theorem thirdExampleCheckpointMass_eq_targetP :
    thirdExampleCheckpointMass = thirdExampleTargetP := by
  norm_num [
    thirdExampleCheckpointMass,
    thirdExampleCheckpointBlocks,
    thirdExampleTargetP
  ]

/--
42個へ展開した scale list。
この list の評価には巨大冪も Farey recursion も現れない。
-/
def thirdExampleCanonicalBlockScales : List ℕ :=
  List.replicate 2 3 ++
  List.replicate 3 5 ++
  List.replicate 5 7 ++
  List.replicate 23 9 ++
  List.replicate 2 11 ++
  [13] ++
  [15] ++
  List.replicate 3 17 ++
  [19] ++
  [21]

/-- explicit canonical skeleton は exact に42 block。 -/
theorem thirdExampleCanonicalBlockScales_length :
    thirdExampleCanonicalBlockScales.length = 42 := by
  norm_num [thirdExampleCanonicalBlockScales]

/-- 左側 start residue 用 modulus。128 bit 程度で十分。 -/
def thirdExampleLeftModulus : ℕ :=
  2 ^ 68

/-- 右側 endpoint residue 用 modulus。128 bit 程度で十分。 -/
def thirdExampleRightModulus : ℕ :=
  3 ^ 42

/-- 左 modulus は正。 -/
theorem thirdExampleLeftModulus_pos :
    0 < thirdExampleLeftModulus := by decide

/-- 右 modulus は正。 -/
theorem thirdExampleRightModulus_pos :
    0 < thirdExampleRightModulus := by decide

end ThirdExampleSearch
end CSTMicro
end Collatz2
