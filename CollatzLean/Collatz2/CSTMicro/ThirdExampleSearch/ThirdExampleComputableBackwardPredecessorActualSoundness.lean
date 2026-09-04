import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleComputableBackwardPredecessor
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselChain

/-!
# 第3例探索 D4.2: 計算可能 predecessor の actual-chain soundness

D4.1 の executable predecessor を、既存の純粋 Hensel chain に接続する。

対象は二種類。

* `MonotoneSuffixHenselChain`
  restarted branch の `delta 0 = 1` を持つ版。
* `FreeBaseMonotoneHenselChain`
  attached branch の入口 exponent を固定しない版。

内部 step では actual recurrence と staircase 条件から
`IsBackwardPredecessor` witness を作り、D4.1 の completeness を使う。
terminal 直前では `q_terminal = 0` と actual recurrence から terminal seed の
exact correctness を得る。

このファイルの theorem は proof-side だけで chain object を使い、
D4.1 の実行関数自体には proof object を持ち込まない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/-- proof-side の actual chain state を D4 の有限 state へ写す。 -/
def thirdExampleBackwardStateOfMonotone
    (C : MonotoneSuffixHenselChain)
    (i : ℕ) : ThirdExampleBackwardHenselState :=
  { q := C.q i, delta := C.delta i }

@[simp] theorem thirdExampleBackwardStateOfMonotone_q
    (C : MonotoneSuffixHenselChain)
    (i : ℕ) :
    (thirdExampleBackwardStateOfMonotone C i).q = C.q i := rfl

@[simp] theorem thirdExampleBackwardStateOfMonotone_delta
    (C : MonotoneSuffixHenselChain)
    (i : ℕ) :
    (thirdExampleBackwardStateOfMonotone C i).delta = C.delta i := rfl

/--
`MonotoneSuffixHenselChain` の内部 actual step は executable predecessor が exact に復元する。
-/
theorem thirdExampleComputableBackwardPredecessor_actual_monotone
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hi : i + 1 < C.width) :
    thirdExampleComputableBackwardPredecessor
        (C.q (i + 1))
        (C.delta (i + 1)) =
      some (thirdExampleBackwardStateOfMonotone C i) := by
  apply thirdExampleComputableBackwardPredecessor_complete
  exact C.actual_isBackwardPredecessor hi

/--
`MonotoneSuffixHenselChain` の terminal 直前も、actual terminal exponent を入力すれば
terminal seed が exact に actual state を返す。
-/
theorem thirdExampleComputableTerminalPredecessor_actual_monotone
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hTerminal : i + 1 = C.width) :
    thirdExampleComputableTerminalPredecessor (C.delta i) =
      some (thirdExampleBackwardStateOfMonotone C i) := by
  apply thirdExampleComputableTerminalPredecessor_complete
  have hi : i < C.width := by omega
  have hRec := C.recurrence i hi
  rw [hTerminal, C.q_terminal] at hRec
  simpa using hRec

/-- proof-side の free-base actual chain state を D4 の有限 state へ写す。 -/
def thirdExampleBackwardStateOfFreeBase
    (C : FreeBaseMonotoneHenselChain)
    (i : ℕ) : ThirdExampleBackwardHenselState :=
  { q := C.q i, delta := C.delta i }

@[simp] theorem thirdExampleBackwardStateOfFreeBase_q
    (C : FreeBaseMonotoneHenselChain)
    (i : ℕ) :
    (thirdExampleBackwardStateOfFreeBase C i).q = C.q i := rfl

@[simp] theorem thirdExampleBackwardStateOfFreeBase_delta
    (C : FreeBaseMonotoneHenselChain)
    (i : ℕ) :
    (thirdExampleBackwardStateOfFreeBase C i).delta = C.delta i := rfl

/--
free-base chain の内部 actual step も、同じ `IsBackwardPredecessor` predicate を満たす。
入口 exponent `delta 0 = 1` はこの局所事実には不要である。
-/
theorem freeBase_actual_isBackwardPredecessor
    (C : FreeBaseMonotoneHenselChain)
    {i : ℕ}
    (hi : i + 1 < C.width) :
    MonotoneSuffixHenselChain.IsBackwardPredecessor
      (C.q (i + 1))
      (C.delta (i + 1))
      (C.delta i)
      (C.q i) := by
  constructor
  · rcases C.delta_step i hi with hSame | hUp
    · exact Or.inl hSame.symm
    · exact Or.inr hUp.symm
  · exact C.recurrence i (by omega)

/--
attached branch の自然な受け皿である `FreeBaseMonotoneHenselChain` でも、
内部 executable predecessor は actual state を exact に返す。
-/
theorem thirdExampleComputableBackwardPredecessor_actual_freeBase
    (C : FreeBaseMonotoneHenselChain)
    {i : ℕ}
    (hi : i + 1 < C.width) :
    thirdExampleComputableBackwardPredecessor
        (C.q (i + 1))
        (C.delta (i + 1)) =
      some (thirdExampleBackwardStateOfFreeBase C i) := by
  apply thirdExampleComputableBackwardPredecessor_complete
  exact freeBase_actual_isBackwardPredecessor C hi

/--
free-base chain の terminal 直前も terminal seed が exact に actual state を返す。
これが attached actual quotient chain を42段 executable 化する入口になる。
-/
theorem thirdExampleComputableTerminalPredecessor_actual_freeBase
    (C : FreeBaseMonotoneHenselChain)
    {i : ℕ}
    (hTerminal : i + 1 = C.width) :
    thirdExampleComputableTerminalPredecessor (C.delta i) =
      some (thirdExampleBackwardStateOfFreeBase C i) := by
  apply thirdExampleComputableTerminalPredecessor_complete
  have hi : i < C.width := by omega
  have hRec := C.recurrence i hi
  rw [hTerminal, C.q_terminal] at hRec
  simpa using hRec

end ThirdExampleSearch
end CSTMicro
end Collatz2
