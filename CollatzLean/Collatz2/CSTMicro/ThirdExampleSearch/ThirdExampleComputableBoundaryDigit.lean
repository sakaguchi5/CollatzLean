import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalHenselBoundaryDigitAdapter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleHensel42ResidueCompleteness

/-!
# 第3例探索 D3.1: criticalization boundary digit の計算可能化

既存の proof-side API では、criticalization boundary が許す Hensel digit は
`PureBProfileObstruction` と normalized terminal tail から一意に決まる。
しかし最終 `native_decide` の hot path に proof object を持ち込んではいけない。

このファイルでは、boundary 判定に本当に必要な有限情報だけを切り出す。

* left cut `cut`
* normalized terminal tail の `mod 3` digit

この二つから `Fin 3` の候補を純粋な計算として返す。
そして proof-side の normalized terminal tail をその `mod 3` digit に落とした場合、
既存の `terminalHenselBoundaryCandidate` と exact に一致することを証明する。

重要なのは、この計算関数自身は `PureBProfileObstruction` も証明項も引数に取らないことである。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
整数の normalized terminal tail から、その `mod 3` class だけを `Fin 3` にする。

proof-side の巨大整数から runtime に渡す必要がある情報はこの一桁だけである。
-/
def thirdExampleNormalizedTailDigit
    (z : ℤ) : Fin 3 :=
  henselThreeLiftIndexOfDigit (z : ZMod 3)

/-- `Fin 3` に落としても元の `ZMod 3` class は失われない。 -/
@[simp] theorem henselThreeLiftDigit_thirdExampleNormalizedTailDigit
    (z : ℤ) :
    henselThreeLiftDigit (thirdExampleNormalizedTailDigit z) =
      (z : ZMod 3) := by
  unfold thirdExampleNormalizedTailDigit
  exact henselThreeLiftDigit_indexOfDigit _

/--
有限データだけから計算する boundary digit。

既存の exact bridge

  boundaryDigit = -2^beattyIndex(cut) * normalizedTail   (mod 3)

の右辺を、そのまま `Fin 3` の Hensel candidate に戻す。
`normalizedTailDigit` は既に一桁へ圧縮されているので巨大整数は不要。
-/
def thirdExampleComputableBoundaryDigit
    (cut : ℕ)
    (normalizedTailDigit : Fin 3) : Fin 3 :=
  henselThreeLiftIndexOfDigit
    (((- (2 : ℤ) ^ beattyIndex cut : ℤ) : ZMod 3) *
      henselThreeLiftDigit normalizedTailDigit)

/--
計算した `Fin 3` candidate を `ZMod 3` に戻すと、
定義通り `-2^beta(cut) * normalizedTailDigit` になる。
-/
@[simp] theorem henselThreeLiftDigit_thirdExampleComputableBoundaryDigit
    (cut : ℕ)
    (normalizedTailDigit : Fin 3) :
    henselThreeLiftDigit
        (thirdExampleComputableBoundaryDigit cut normalizedTailDigit) =
      (((- (2 : ℤ) ^ beattyIndex cut : ℤ) : ZMod 3) *
        henselThreeLiftDigit normalizedTailDigit) := by
  unfold thirdExampleComputableBoundaryDigit
  exact henselThreeLiftDigit_indexOfDigit _

/--
中心 soundness bridge。

proof-side の actual normalized terminal tail を一桁へ落としてから
`thirdExampleComputableBoundaryDigit` を評価すると、既存の
`terminalHenselBoundaryCandidate` と exact に一致する。

従って boundary の三択を潰す処理そのものは、
`PureBProfileObstruction` を持たない有限計算へ移せる。
-/
theorem thirdExampleComputableBoundaryDigit_eq_terminalHenselBoundaryCandidate
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {cut : ℕ}
    (hcut : cut < P.criticalizationStart) :
    thirdExampleComputableBoundaryDigit
        cut
        (thirdExampleNormalizedTailDigit
          (P.criticalizationNormalizedTerminalTail
            cut (Nat.le_of_lt hcut))) =
      terminalHenselBoundaryCandidate P hStart := by
  apply henselThreeLiftDigitEquiv.injective
  change
    henselThreeLiftDigit
        (thirdExampleComputableBoundaryDigit
          cut
          (thirdExampleNormalizedTailDigit
            (P.criticalizationNormalizedTerminalTail
              cut (Nat.le_of_lt hcut)))) =
      henselThreeLiftDigit
        (terminalHenselBoundaryCandidate P hStart)
  rw [henselThreeLiftDigit_thirdExampleComputableBoundaryDigit]
  rw [henselThreeLiftDigit_thirdExampleNormalizedTailDigit]
  unfold terminalHenselBoundaryCandidate
  rw [henselThreeLiftDigit_indexOfDigit]
  rw [
    MultiCorner.criticalizationBoundaryDigit_eq_neg_normalizedTerminalTail
      P hStart hcut
  ]
  push_cast
  rfl

/--
上の計算可能 candidate は、actual normalized tail を入力した場合に必ず
既存 boundary filter を通る。
-/
theorem thirdExampleComputableBoundaryDigit_survives
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {cut : ℕ}
    (hcut : cut < P.criticalizationStart) :
    terminalHenselBoundarySurvives P hStart
      (thirdExampleComputableBoundaryDigit
        cut
        (thirdExampleNormalizedTailDigit
          (P.criticalizationNormalizedTerminalTail
            cut (Nat.le_of_lt hcut)))) := by
  rw [thirdExampleComputableBoundaryDigit_eq_terminalHenselBoundaryCandidate
      P hStart hcut]
  exact terminalHenselBoundaryCandidate_survives P hStart

/--
actual normalized tail から得た計算可能 boundary digit は 0 digit にはならない。
これは既存 boundary unit の非零性を有限 candidate 側へ輸送したもの。
-/
theorem henselThreeLiftDigit_thirdExampleComputableBoundaryDigit_ne_zero
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {cut : ℕ}
    (hcut : cut < P.criticalizationStart) :
    henselThreeLiftDigit
        (thirdExampleComputableBoundaryDigit
          cut
          (thirdExampleNormalizedTailDigit
            (P.criticalizationNormalizedTerminalTail
              cut (Nat.le_of_lt hcut)))) ≠ 0 := by
  rw [thirdExampleComputableBoundaryDigit_eq_terminalHenselBoundaryCandidate
      P hStart hcut]
  unfold terminalHenselBoundaryCandidate
  rw [henselThreeLiftDigit_indexOfDigit]
  exact MultiCorner.criticalizationBoundaryDigit_ne_zero P hStart

end ThirdExampleSearch
end CSTMicro
end Collatz2
