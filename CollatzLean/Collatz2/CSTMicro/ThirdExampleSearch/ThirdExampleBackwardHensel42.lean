import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleComputableBackwardPredecessorActualSoundness

/-!
# 第3例探索 D4.3: terminal から42セルを戻す deterministic Hensel chain

D4.1 の executable predecessor を繰り返し、有限長の backward chain を作る。

terminal 直前だけは next exponent が存在しないので、

  terminal exponent -> terminal seed

を最初の1セルとして数える。その後、内部 predecessor を41回適用することで
terminal から合計42個の occupied states を戻す。

従って `thirdExampleBackwardHensel42` は

  1 terminal seed + 41 internal predecessor = 42 cells

という実行形である。

この計算器自体は chain proof object を引数に取らない。
actual-chain theorem 側だけで既存 recurrence を使い、結果が本物の42セル suffix と
exact に一致することを示す。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
既に右側 state が一つ得られているところから、内部 predecessor を `steps` 回戻す。
途中で recurrence が割り切れなければ `none` になる。
-/
def thirdExampleBackwardHenselIterate :
    ℕ → ThirdExampleBackwardHenselState → Option ThirdExampleBackwardHenselState
  | 0, S => some S
  | steps + 1, S =>
      match thirdExampleComputableBackwardPredecessor S.q S.delta with
      | none => none
      | some SPrev => thirdExampleBackwardHenselIterate steps SPrev

@[simp] theorem thirdExampleBackwardHenselIterate_zero
    (S : ThirdExampleBackwardHenselState) :
    thirdExampleBackwardHenselIterate 0 S = some S := rfl

/-- 一回以上では最初に executable predecessor を一度だけ評価する。 -/
@[simp] theorem thirdExampleBackwardHenselIterate_succ
    (steps : ℕ)
    (S : ThirdExampleBackwardHenselState) :
    thirdExampleBackwardHenselIterate (steps + 1) S =
      match thirdExampleComputableBackwardPredecessor S.q S.delta with
      | none => none
      | some SPrev => thirdExampleBackwardHenselIterate steps SPrev := rfl

/--
`MonotoneSuffixHenselChain` の actual internal state から `steps` 回戻せば、
exact に `steps` 個左の actual stateへ到達する。
-/
theorem thirdExampleBackwardHenselIterate_actual_monotone
    (C : MonotoneSuffixHenselChain)
    (i steps : ℕ)
    (hRange : i + steps < C.width) :
    thirdExampleBackwardHenselIterate
        steps
        (thirdExampleBackwardStateOfMonotone C (i + steps)) =
      some (thirdExampleBackwardStateOfMonotone C i) := by
  induction steps generalizing i with
  | zero =>
      rfl
  | succ steps ih =>
      have hIdx : i + (steps + 1) = (i + steps) + 1 := by omega
      rw [hIdx]
      rw [thirdExampleBackwardHenselIterate_succ]
      change
        (match thirdExampleComputableBackwardPredecessor
            (C.q ((i + steps) + 1))
            (C.delta ((i + steps) + 1)) with
          | none => none
          | some SPrev => thirdExampleBackwardHenselIterate steps SPrev) =
        some (thirdExampleBackwardStateOfMonotone C i)
      have hStepRange : (i + steps) + 1 < C.width := by omega
      rw [thirdExampleComputableBackwardPredecessor_actual_monotone
        C (i := i + steps) hStepRange]
      exact ih i (by omega)

/--
`FreeBaseMonotoneHenselChain` でも同じ deterministic iterate が actual state を exact に復元する。
attached branch ではこちらを使う。
-/
theorem thirdExampleBackwardHenselIterate_actual_freeBase
    (C : FreeBaseMonotoneHenselChain)
    (i steps : ℕ)
    (hRange : i + steps < C.width) :
    thirdExampleBackwardHenselIterate
        steps
        (thirdExampleBackwardStateOfFreeBase C (i + steps)) =
      some (thirdExampleBackwardStateOfFreeBase C i) := by
  induction steps generalizing i with
  | zero =>
      rfl
  | succ steps ih =>
      have hIdx : i + (steps + 1) = (i + steps) + 1 := by omega
      rw [hIdx]
      rw [thirdExampleBackwardHenselIterate_succ]
      change
        (match thirdExampleComputableBackwardPredecessor
            (C.q ((i + steps) + 1))
            (C.delta ((i + steps) + 1)) with
          | none => none
          | some SPrev => thirdExampleBackwardHenselIterate steps SPrev) =
        some (thirdExampleBackwardStateOfFreeBase C i)
      have hStepRange : (i + steps) + 1 < C.width := by omega
      rw [thirdExampleComputableBackwardPredecessor_actual_freeBase
        C (i := i + steps) hStepRange]
      exact ih i (by omega)

/--
terminal exponent から42個の occupied states を deterministic に戻す。

* 1個目: terminal seed
* 残り41個: internal predecessor
-/
def thirdExampleBackwardHensel42
    (terminalDelta : ℕ) : Option ThirdExampleBackwardHenselState :=
  match thirdExampleComputableTerminalPredecessor terminalDelta with
  | none => none
  | some STerminalPrev =>
      thirdExampleBackwardHenselIterate 41 STerminalPrev

/--
`MonotoneSuffixHenselChain` の terminal suffix が exact に42セルある位置 `i` から始まるなら、
42段 executable chain は `i` 番目の actual state を返す。
-/
theorem thirdExampleBackwardHensel42_actual_monotone
    (C : MonotoneSuffixHenselChain)
    (i : ℕ)
    (hWidth : i + 42 = C.width) :
    thirdExampleBackwardHensel42 (C.delta (i + 41)) =
      some (thirdExampleBackwardStateOfMonotone C i) := by
  have hTerminal : i + 41 + 1 = C.width := by omega
  have hSeed :=
    thirdExampleComputableTerminalPredecessor_actual_monotone
      C (i := i + 41) hTerminal
  unfold thirdExampleBackwardHensel42
  rw [hSeed]
  exact thirdExampleBackwardHenselIterate_actual_monotone C i 41 (by omega)

/--
monotone chain の幅が42以上なら、terminal から42セル戻した位置は `width - 42`。
-/
theorem thirdExampleBackwardHensel42_actual_monotone_of_fortyTwo_le
    (C : MonotoneSuffixHenselChain)
    (hFortyTwo : 42 ≤ C.width) :
    thirdExampleBackwardHensel42 (C.delta (C.width - 1)) =
      some (thirdExampleBackwardStateOfMonotone C (C.width - 42)) := by
  have hWidth : C.width - 42 + 42 = C.width := by omega
  have hIndex : C.width - 1 = C.width - 42 + 41 := by omega
  rw [hIndex]
  exact thirdExampleBackwardHensel42_actual_monotone
    C (C.width - 42) hWidth

/--
`FreeBaseMonotoneHenselChain` の terminal suffix に対する42セル版。
attached actual quotient chain を executable な有限 chain へ落とす中心 theorem。
-/
theorem thirdExampleBackwardHensel42_actual_freeBase
    (C : FreeBaseMonotoneHenselChain)
    (i : ℕ)
    (hWidth : i + 42 = C.width) :
    thirdExampleBackwardHensel42 (C.delta (i + 41)) =
      some (thirdExampleBackwardStateOfFreeBase C i) := by
  have hTerminal : i + 41 + 1 = C.width := by omega
  have hSeed :=
    thirdExampleComputableTerminalPredecessor_actual_freeBase
      C (i := i + 41) hTerminal
  unfold thirdExampleBackwardHensel42
  rw [hSeed]
  exact thirdExampleBackwardHenselIterate_actual_freeBase C i 41 (by omega)

/--
free-base chain の幅が42以上なら、terminal から42セル戻した結果を
`width - 42` の actual state と直接同定できる。
-/
theorem thirdExampleBackwardHensel42_actual_freeBase_of_fortyTwo_le
    (C : FreeBaseMonotoneHenselChain)
    (hFortyTwo : 42 ≤ C.width) :
    thirdExampleBackwardHensel42 (C.delta (C.width - 1)) =
      some (thirdExampleBackwardStateOfFreeBase C (C.width - 42)) := by
  have hWidth : C.width - 42 + 42 = C.width := by omega
  have hIndex : C.width - 1 = C.width - 42 + 41 := by omega
  rw [hIndex]
  exact thirdExampleBackwardHensel42_actual_freeBase
    C (C.width - 42) hWidth

end ThirdExampleSearch
end CSTMicro
end Collatz2
