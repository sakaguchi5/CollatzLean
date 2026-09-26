import CollatzLean.Collatz4.General.Pruning
import CollatzLean.Collatz4.M7.ForwardReduction

/-!
# Collatz4.M7.LivePruning

一般 pruning 語彙へ m=7 固有 threshold を代入する特殊化。
-/

namespace Collatz4.M7

/-- m=7 の共通終端時刻と目標2指数。 -/
def liveTarget : Collatz4.General.LiveTarget :=
  ⟨targetTime, targetTwoExponent⟩

/-- m=7 の live 必要条件。一般定義への特殊化。 -/
def liveNecessary (s : ℕ) (x : ForwardState) : Prop :=
  Collatz4.General.liveNecessary liveTarget s x

/-- m=7 の checkpoint 三分岐に固有な数値。 -/
def checkpointSpec : Collatz4.General.CheckpointSpec :=
  ⟨11057, 10671, 64, 21⟩

/-- m=7 の checkpoint 安全述語。一般定義への特殊化。 -/
def checkpointSafe (x : ForwardState) : Prop :=
  Collatz4.General.checkpointSafe checkpointSpec x

end Collatz4.M7
