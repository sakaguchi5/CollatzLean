import CollatzLean.Collatz3.CSTMicro.CSTCriterion

/-!
# Collatz3 CSTCarry: CST を `B < D*R` に固定する公開 bridge

既存 `CSTMicro.CSTCriterion` は path-wise CST をすでに exact に解いている。
このファイルでは、会話で使ってきた記号

* `B` : affine correction numerator,
* `D = 2^H - 3^P` : first-crossing terminal gap,
* `R` : parity cylinder の最小非負代表

に対応する theorem 名だけを薄く公開する。
新しい数学的仮定は追加しない。
-/

namespace Collatz3
namespace CSTMicro
namespace FirstPassagePath

/--
一つの first coefficient crossing path 上で CST が成立することは、exact に

  B < (2^H - 3^P) * R

と同値。
-/
theorem cstHolds_iff_affineConst_lt_terminalGap_mul_leastRepresentative
    (P : FirstPassagePath) :
    P.CSTHolds ↔
      affineConst P.word <
        P.terminalGap * leastRepresentative P.word := by
  exact P.cstHolds_iff_pureSeparation

/-- 同じ条件を critical gap `2^criticalTwoDepth(p)-3^p` で書き直した形。 -/
theorem cstHolds_iff_affineConst_lt_criticalGap_mul_leastRepresentative
    (P : FirstPassagePath) :
    P.CSTHolds ↔
      affineConst P.word <
        (2 ^ Critical.criticalTwoDepth P.endpointOddCount -
          3 ^ P.endpointOddCount) * leastRepresentative P.word := by
  rw [← P.terminalGap_eq_criticalGap]
  exact P.cstHolds_iff_affineConst_lt_terminalGap_mul_leastRepresentative

end FirstPassagePath
end CSTMicro
end Collatz3
