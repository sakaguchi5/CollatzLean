import CollatzLean.Collatz4.Finite.ThreePowerForwardCompression
import CollatzLean.Collatz4.Targets.M7.CompressionData
import CollatzLean.Collatz4.Targets.M7.ForwardReduction

set_option linter.style.nativeDecide false

/-!
# Collatz4.Targets.M7.StructuralCompression

M=7 の 2179 候補を、同期合流を使って 97 代表へ圧縮する。

重要なのは、各候補を最終時刻まで独立な「別問題」として扱わないことである。
`CompressionData` が保持する合流時刻で候補と代表が同じ状態になることを
有限 certificate で確認し、その後の一致は一般の同期合流定理から導く。

これにより

`2179 candidates -> 97 representative trajectories`

を Lean 上の構造として得る。
-/

namespace Collatz4.Targets.M7

open Collatz4.Dynamics
open Collatz4.Finite

/--
保存された class / merge time が実際の累積軌道と一致することをまとめた certificate。

各候補 `i` について

* 候補開始時刻 ≤ merge time
* 代表開始時刻 ≤ merge time
* merge time ≤ 8456
* その時刻で両軌道が exact に一致

を確認する。
-/
private theorem compression_merge_certificate :
    ∀ i : Fin candidateCount,
      candidateN i ≤ compressionMergeTime i ∧
      compressionRepresentativeN (compressionRepresentativeOf i) ≤
        compressionMergeTime i ∧
      compressionMergeTime i ≤ targetTime ∧
      threePowerAt (candidateN i) (compressionMergeTime i) =
        threePowerAt
          (compressionRepresentativeN (compressionRepresentativeOf i))
          (compressionMergeTime i) := by
  native_decide

/-- M=7 の 2179 -> 97 同期合流圧縮。 -/
def m7ThreePowerCompression :
    ThreePowerCompression
      (Fin candidateCount)
      (Fin compressionRepresentativeCount)
      targetTime where
  candidateN := candidateN
  representativeN := compressionRepresentativeN
  representativeOf := compressionRepresentativeOf
  merges := by
    intro i
    have h := compression_merge_certificate i
    exact ⟨compressionMergeTime i, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/--
保存した 97 個の終端 `v₂` 値が、実際の代表軌道の終端と一致する。
-/
theorem compression_representative_t_certificate :
    ∀ r : Fin compressionRepresentativeCount,
      accumulatedV2
        (m7ThreePowerCompression.representativeTerminal r) =
      compressionRepresentativeTTable[r.1]! := by
  native_decide

/--
97代表の保存された終端2指数は重複しない。
実軌道との一致は `compression_representative_t_certificate` が保証する。
-/
theorem compression_representative_t_values_nodup :
    compressionRepresentativeTTable.toList.Nodup :=
  compressionRepresentativeTTable_nodup

/--
M=7 の `forwardProblem` は、一般 `ThreePowerCompression` の終点圧縮として読める。
-/
def m7FinalStateCompression :
    FinalStateCompression
      (Fin compressionRepresentativeCount)
      forwardProblem :=
  Collatz4.Finite.finalStateCompression_of_threePower
    m7ThreePowerCompression
    forwardProblem
    (by
      intro i
      rfl)
    (by
      intro i
      rfl)

end Collatz4.Targets.M7
