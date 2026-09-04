import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleForcedHensel42
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueD2Aggregate

/-!
# 第3例探索 D3 集約: 計算可能 boundary digit から deterministic Hensel-42 へ

D3.1 と D3.2 を接続する薄い集約層。

ここでは、各 Hensel depth `r` に対して

* どの left cut を使うか
* normalized terminal tail の `mod 3` digit

が有限データとして供給されたとき、それを boundary digit に変換して42段を一本鎖で積む。

重要:
このファイルは「同じ criticalization boundary が42個の digit 全部を与える」とは仮定しない。
最終 soundness に必要な残りの数学は、各 `r < 42` で

  computed boundary digit = actual endpoint digit

を示す compatibility theorem だけに集約される。
-/

namespace Collatz2
namespace CSTMicro
open ExternalArithmetic
namespace ThirdExampleSearch

/--
各 depth の有限 boundary data から Hensel digit provider を作る。
`cut` と `normalizedTailDigit` はどちらも runtime data だけでよい。
-/
def thirdExampleBoundaryDigitProvider
    (cut : ℕ → ℕ)
    (normalizedTailDigit : ℕ → Fin 3)
    (r : ℕ) : Fin 3 :=
  thirdExampleComputableBoundaryDigit
    (cut r)
    (normalizedTailDigit r)

/-- boundary data から直接作る42段 deterministic residue。 -/
def thirdExampleForcedBoundaryHensel42
    (cut : ℕ → ℕ)
    (normalizedTailDigit : ℕ → Fin 3) : ℕ :=
  thirdExampleForcedHensel42
    (thirdExampleBoundaryDigitProvider cut normalizedTailDigit)

/--
42段の boundary provider が actual endpoint の各 ternary digit と一致するなら、
最終 residue は exact に endpoint `mod 3^42`。

これが次段 verifier へ渡す最小 compatibility obligation である。
-/
theorem thirdExampleForcedBoundaryHensel42_eq_mod
    (cut : ℕ → ℕ)
    (normalizedTailDigit : ℕ → Fin 3)
    (endpoint : ℕ)
    (hCompat :
      ∀ r : ℕ, r < 42 →
        thirdExampleBoundaryDigitProvider
            cut normalizedTailDigit r =
          gapOneThreeAdicDigitFin endpoint r) :
    thirdExampleForcedBoundaryHensel42
        cut normalizedTailDigit =
      endpoint % thirdExampleRightModulus := by
  unfold thirdExampleForcedBoundaryHensel42
  apply thirdExampleForcedHensel42_eq_mod
  exact hCompat

/--
一段については、actual normalized terminal tail を有限 digit に落として使えば、
計算可能 step と既存 proof-side canonical boundary step は exact に同じ。

これにより proof-side の一意性を runtime の一分岐 step へ安全に輸送できる。
-/
theorem thirdExampleForcedBoundaryStep_eq_terminalCandidateStep
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {cut : ℕ}
    (hcut : cut < P.criticalizationStart)
    (q r : ℕ) :
    thirdExampleForcedHenselStep
        q r
        (thirdExampleComputableBoundaryDigit
          cut
          (thirdExampleNormalizedTailDigit
            (P.criticalizationNormalizedTerminalTail
              cut (Nat.le_of_lt hcut)))) =
      thirdExampleForcedHenselStep
        q r
        (terminalHenselBoundaryCandidate P hStart) := by
  rw [thirdExampleComputableBoundaryDigit_eq_terminalHenselBoundaryCandidate
      P hStart hcut]

end ThirdExampleSearch
end CSTMicro
end Collatz2
