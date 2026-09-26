import CollatzLean.Collatz4.Targets.M7.MasterBridge
import CollatzLean.Collatz4.Targets.M7.StructuralResult

/-!
# Collatz4.Targets.M7.MasterToWitness

`M7MasterWitness` と、有限排除済みの固定 `M7Witness` の間に残っている
record extraction を明示する層。

重要:
現在の `M7MasterWitness` は actual reachability から

* source `Q_N`
* branch index
* prefix exponent word
* terminal exponent `2q-1`
* master equation

を保持するが、固定 finite problem で使う

* target time `8456`
* target 2 exponent `10996`
* 固定 residual record による `G_*`
* residual length と recurrence

を強制する定理はまだない。

`(2401,29)` および `(13396,8455)` は、これまでの探索では逆木 record /
近似から選ばれた値であり、`M7MasterWitness` の定義だけからは導出されていない。

したがってこのファイルでは論理の穴を仮定で隠さず、
「何を追加証明すれば完全な `OddQBranchReachable 7` 排除になるか」を
`M7FixedRecordExtraction` として正確に型にする。
-/

namespace Collatz4.Targets.M7

open Collatz4.Finite

/--
master witness `h` から固定 M=7 residual problem を取り出すために、
現在まだ別途証明が必要なデータ。

`q` は master witness のものをそのまま保存し、`q_pos` は既に `h` が持つので
ここでは重複して保持しない。
-/
structure M7FixedRecordExtraction (h : M7MasterWitness) where
  residualLength : ℕ
  residual_even : residualLength % 2 = 0
  residual_le :
    residualLength ≤ residualTwoExponent h.q
  g_lower :
    Collatz4.Finite.residualGMin
      (residualTwoExponent h.q) residualLength ≤ gStar
  g_upper :
    gStar ≤ Collatz4.Finite.residualGMax
      (residualTwoExponent h.q) residualLength
  recurrence :
    Collatz4.Finite.ResidualRecurrence residualLength
      (ForwardState.ofNat
        (3 ^ (targetTime - residualLength) - 1))
      targetState

namespace M7FixedRecordExtraction

/--
record extraction が得られれば、master witness から既存 `M7Witness` を
仮定なしで構成できる。
-/
def toM7Witness
    {h : M7MasterWitness}
    (x : M7FixedRecordExtraction h) :
    M7Witness where
  q := h.q
  r := x.residualLength
  q_pos := h.q_pos
  r_even := x.residual_even
  r_le_residual := x.residual_le
  g_lower := x.g_lower
  g_upper := x.g_upper
  recurrence := x.recurrence

end M7FixedRecordExtraction

/--
個々の master witness について fixed record extraction があれば、
その master witness は存在不能。
-/
theorem no_master_witness_of_fixed_record_extraction
    (h : M7MasterWitness)
    (x : M7FixedRecordExtraction h) :
    False := by
  exact no_m7_witness_via_compression ⟨x.toM7Witness⟩

/--
残っている数学的主張を一つの命題として公開する。

これが証明できれば
`M7MasterWitness -> M7Witness`
が本当に閉じる。
-/
def EveryM7MasterHasFixedRecord : Prop :=
  ∀ h : M7MasterWitness, Nonempty (M7FixedRecordExtraction h)

/--
`EveryM7MasterHasFixedRecord` が証明されれば master witness 自体が存在しない。
-/
theorem no_m7_master_witness_of_fixed_record_theorem
    (hextract : EveryM7MasterHasFixedRecord) :
    ¬ HasM7MasterWitness := by
  intro hmaster
  rcases hmaster with ⟨h⟩
  rcases hextract h with ⟨x⟩
  exact no_master_witness_of_fixed_record_extraction h x

/--
fixed record extraction theorem が得られれば、
研究対象に近い最上流命題 `OddQBranchReachable 7` も排除される。
-/
theorem no_oddQBranchReachable7_of_fixed_record_theorem
    (hextract : EveryM7MasterHasFixedRecord) :
    ¬ Collatz4.Parametric.OddQBranchReachable 7 := by
  intro hreach
  have hmaster : HasM7MasterWitness :=
    masterWitness_of_oddQBranchReachable hreach
  exact no_m7_master_witness_of_fixed_record_theorem hextract hmaster

end Collatz4.Targets.M7
