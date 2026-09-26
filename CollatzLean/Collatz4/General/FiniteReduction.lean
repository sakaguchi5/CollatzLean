import CollatzLean.Collatz4.General.Witness

/-!
# Collatz4.General.FiniteReduction

一般 witness を有限問題へ落とした後の論理をまとめる。

この層には m 固有定数も native 計算も置かない。
-/

namespace Collatz4.General

/--
有限問題に候補が存在しないなら、その有限問題へ必ず落ちる元 witness も存在しない。
-/
theorem no_witness_of_reduction
    {ι : Type} {W : Prop} {P : ForwardProblem ι}
    (hreduce : ReducesTo W P)
    (hfinite : ¬ P.Candidate) :
    ¬ W := by
  intro hW
  exact hfinite (hreduce hW)

end Collatz4.General
