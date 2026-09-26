import CollatzLean.Collatz4.Dynamics.ThreePowerCompression
import CollatzLean.Collatz4.Finite.AccumulatedForwardBridge
import CollatzLean.Collatz4.Finite.RepresentativeCompression

/-!
# Collatz4.Finite.ThreePowerForwardCompression

`Dynamics.ThreePowerCompression` で得た `3^n - 1` 族の同期合流圧縮を、
既存の `Finite.ForwardProblem` の `FinalStateCompression` へ運ぶ一般 bridge。

候補側 `ForwardProblem` が

* 開始状態 `ofNat (3^n - 1)`
* 残り段数 `T - n`

を使っていることだけを仮定する。M 固有の定数は置かない。
-/

namespace Collatz4.Finite

open Collatz4.Dynamics

/--
`ThreePowerCompression` を `ForwardProblem` の終点圧縮として読む。

一般累積写像と `ForwardState/run` の可換性は
`AccumulatedForwardBridge` から供給される。
-/
def finalStateCompression_of_threePower
    {ι ρ : Type} {T : ℕ}
    (C : Collatz4.Dynamics.ThreePowerCompression ι ρ T)
    (P : ForwardProblem ι)
    (hinitial : ∀ i : ι,
      P.initialState i =
        ForwardState.ofNat (3 ^ C.candidateN i - 1))
    (hsteps : ∀ i : ι,
      P.remainingSteps i = T - C.candidateN i) :
    FinalStateCompression ρ P where
  representativeFinal := fun r =>
    ForwardState.ofNat (C.representativeTerminal r)
  representativeOf := C.representativeOf
  final_eq_representative := by
    intro i
    unfold ForwardProblem.finalState
    rw [hsteps i, hinitial i]
    rw [← ofNat_accumulatedRun]
    apply congrArg ForwardState.ofNat
    simpa [
      Collatz4.Dynamics.ThreePowerCompression.candidateTerminal,
      Collatz4.Dynamics.ThreePowerCompression.representativeTerminal,
      threePowerAt,
      accumulatedAt
    ] using C.candidateTerminal_eq_representative i

end Collatz4.Finite
