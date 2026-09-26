import CollatzLean.Collatz4.General.ForwardProblem

/-!
# Collatz4.General.Witness

元の数論的 witness と有限前向き問題の間を結ぶ、最小の一般語彙。

重要なのは、ここでは「witness が何であるか」を決め打ちしないこと。
m ごとの数論的意味は特殊化側で定義し、一般層は reduction の論理だけを扱う。
-/

namespace Collatz4.General

/--
命題 `W` の任意の witness が、有限前向き候補へ落ちること。
-/
def ReducesTo {ι : Type} (W : Prop) (P : ForwardProblem ι) : Prop :=
  W → P.Candidate

/-- reduction を適用するだけの補助定理。 -/
theorem candidate_of_reduction
    {ι : Type} {W : Prop} {P : ForwardProblem ι}
    (hreduce : ReducesTo W P) (hW : W) :
    P.Candidate :=
  hreduce hW

end Collatz4.General
