import CollatzLean.Collatz4.Targets.M7.LivePruning

set_option linter.style.nativeDecide false

/-!
# Collatz4.Targets.M7.FiniteCertificate

M=7 に本当に固有な有限計算部分。

一般理論はこのファイルの数値を知らず、ここで得られた certificate だけを受け取る。

## 計算上の方針

旧版では

* `final_two_exponent_certificate` が各候補を最終時刻 `8456` まで計算し、
* `checkpoint_certificate` が同じ各候補を checkpoint `8455` まで再計算していた。

そのため、2179候補についてほぼ同じ前向き軌道を2回ずつ走査していた。

ここでは checkpoint 状態を一度だけ計算し、その同じ状態 `x` に対して

1. `checkpointSafe x`
2. 最後の1段 `step x` の2指数が `targetTwoExponent` と異なる

を一つの `native_decide` で同時に certificate する。

公開 theorem

* `final_two_exponent_certificate`
* `checkpoint_certificate`

の名前と型は従来どおり維持する。
-/

namespace Collatz4.Targets.M7

open Collatz4.Finite

/--
`run` の最後の1段を右側へ取り出す。

`run` 自体は末尾再帰として

`run (k+1) x = run k (step x)`

と定義されているが、決定的反復なので

`run (k+1) x = step (run k x)`

も成り立つ。

この補題は計算 certificate とは独立な純粋な構造補題。
-/
private theorem run_succ_last (k : ℕ) (x : ForwardState) :
    run (k + 1) x = step (run k x) := by
  induction k generalizing x with
  | zero =>
      rfl
  | succ k ih =>
      rw [run_succ]
      rw [ih]
      rw [run_succ]

/--
M=7 の各候補では、最終状態は checkpoint 状態からちょうど1回 `step`
した状態である。

これにより checkpoint までの巨大な前向き計算を
final certificate 側で最初から再実行する必要がなくなる。
-/
private theorem finalState_eq_step_checkpointState
    (i : Fin candidateCount) :
    finalState i = step (checkpointState i) := by
  have hN : candidateN i ≤ 4368 := candidateN_upper i
  have hsplit :
      targetTime - candidateN i = (8455 - candidateN i) + 1 := by
    simp only [targetTime]
    omega
  unfold finalState remainingSteps checkpointState
  rw [hsplit, run_succ_last]

/--
M=7 の有限計算を一度だけ行う統合 certificate。

各候補について `checkpointState i` を一度だけ生成し、

* checkpoint の三分岐が成立すること
* その状態から最後の1段だけ進めても目標2指数にならないこと

を同時に確認する。

旧版の二つの独立した `native_decide` に比べ、
checkpoint までの前向き計算の重複を除去している。
-/
private theorem combined_certificate :
    ∀ i : Fin candidateCount,
      let x := checkpointState i
      checkpointSafe x ∧
        (step x).t ≠ targetTwoExponent := by
  simp only [
    checkpointSafe,
    Collatz4.Finite.checkpointSafe,
    checkpointSpec
  ]
  native_decide

/--
最終時刻では、M=7 の有限候補のどれも必要な目標2指数を持たない。

一般 `ForwardProblem` に対する2指数 certificate の M=7 実体。

重い native 計算は `combined_certificate` で既に実行済みで、
ここでは checkpoint から最終状態への1段対応を使って結果だけを取り出す。
-/
theorem final_two_exponent_certificate :
    ∀ i : Fin candidateCount, (finalState i).t ≠ targetTwoExponent := by
  intro i
  rw [finalState_eq_step_checkpointState]
  exact (combined_certificate i).2

/--
構造確認用 checkpoint certificate。

三分岐の形は一般層、
`11057 / 10671 / 64 / 21`
という値だけが M=7 固有である。

重い native 計算は `combined_certificate` と共有する。
-/
theorem checkpoint_certificate :
    ∀ i : Fin candidateCount, checkpointSafe (checkpointState i) := by
  intro i
  exact (combined_certificate i).1

end Collatz4.Targets.M7
