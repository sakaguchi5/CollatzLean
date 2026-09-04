import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint
import Mathlib.Tactic.NormNum

/-!
# 第3例探索: 長い attached 幅の actual-phase checkpoint

直前の数値枝狩りで得られた、幅22/23に対する actual Beatty 位相候補を
literal checkpoint として保存する。

このファイルの役割は既存の `ThirdExampleConvergent22Checkpoint` と同じである。
巨大な Beatty / continued-fraction 計算を hot path で再実行せず、有限表だけを
後段へ渡す。

注意:
この literal 表が actual Beatty 位相の全候補と一致すること自体の certification は
別 theorem として接続するべきであり、このファイルでは定義から捏造しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 長幅枝で保持する位相 checkpoint。 -/
structure ThirdExampleLongWidthPhaseCheckpoint where
  r : ℕ
  w : ℕ
  delta : ℕ
  deriving DecidableEq, Repr

/-- 幅23で残った actual-phase checkpoint は2本。 -/
def thirdExampleWidth23PhaseCheckpoints :
    List ThirdExampleLongWidthPhaseCheckpoint :=
  [ { r := 3,  w := 23, delta := 3_348_766_160 }
  , { r := 15, w := 23, delta := 3_348_766_160 }
  ]

/-- 幅22で残った actual-phase checkpoint は4本。 -/
def thirdExampleWidth22PhaseCheckpoints :
    List ThirdExampleLongWidthPhaseCheckpoint :=
  [ { r := 3,  w := 22, delta :=   222_632_438 }
  , { r := 7,  w := 22, delta := 2_969_418_734 }
  , { r := 9,  w := 22, delta := 1_653_093_581 }
  , { r := 15, w := 22, delta := 1_083_284_150 }
  ]

/-- 幅23の phase checkpoint は exact に2本。 -/
theorem thirdExampleWidth23PhaseCheckpoints_length :
    thirdExampleWidth23PhaseCheckpoints.length = 2 := by
  norm_num [thirdExampleWidth23PhaseCheckpoints]

/-- 幅22の phase checkpoint は exact に4本。 -/
theorem thirdExampleWidth22PhaseCheckpoints_length :
    thirdExampleWidth22PhaseCheckpoints.length = 4 := by
  norm_num [thirdExampleWidth22PhaseCheckpoints]

/-- 幅23の `r` 候補 checkpoint。 -/
def ThirdExampleWidth23RCheckpoint (r : ℕ) : Prop :=
  r = 3 ∨ r = 15

/-- 幅22の `r` 候補 checkpoint。 -/
def ThirdExampleWidth22RCheckpoint (r : ℕ) : Prop :=
  r = 3 ∨ r = 7 ∨ r = 9 ∨ r = 15

/-- 幅23表から取り出した `r` 列は `[3,15]`。 -/
theorem thirdExampleWidth23PhaseCheckpoints_r_map :
    thirdExampleWidth23PhaseCheckpoints.map
      (fun P => P.r) = [3, 15] := by
  rfl

/-- 幅22表から取り出した `r` 列は `[3,7,9,15]`。 -/
theorem thirdExampleWidth22PhaseCheckpoints_r_map :
    thirdExampleWidth22PhaseCheckpoints.map
      (fun P => P.r) = [3, 7, 9, 15] := by
  rfl

/-- 幅23の2候補では `delta` は共通。 -/
theorem thirdExampleWidth23PhaseCheckpoints_delta_map :
    thirdExampleWidth23PhaseCheckpoints.map
      (fun P => P.delta) = [3_348_766_160, 3_348_766_160] := by
  rfl

/-- 幅22の4候補の `delta` checkpoint。 -/
theorem thirdExampleWidth22PhaseCheckpoints_delta_map :
    thirdExampleWidth22PhaseCheckpoints.map
      (fun P => P.delta) =
        [222_632_438, 2_969_418_734, 1_653_093_581, 1_083_284_150] := by
  rfl

end ThirdExampleSearch
end CSTMicro
end Collatz2
