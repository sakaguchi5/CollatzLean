import CollatzLean.Collatz4.Dynamics.Accumulated
import CollatzLean.Collatz4.Finite.Forward

/-!
# Collatz4.Finite.AccumulatedForwardBridge

`Dynamics.Accumulated` の自然数座標

`F(A) = 3*A + 2^v₂(A)`

と、有限排除で使う `Finite.ForwardState` / `step` / `run` を接続する一般 bridge。

このファイルにより、一般 Collatz 層で証明した合流や累積 2 指数の定理を、
既存の有限候補・certificate 層へそのまま運べる。

ここには `M=7` などの target 固有定数を置かない。
-/

namespace Collatz4.Finite

open Collatz4.Dynamics

/--
自然数 `A` を `ForwardState` へ移したときの 2 指数は、
一般累積座標の `accumulatedV2 A` と一致する。
-/
theorem ofNat_t_eq_accumulatedV2 (A : ℕ) :
    (ForwardState.ofNat A).t = accumulatedV2 A := by
  rfl

/--
自然数 `A` を `ForwardState` へ移したときの奇数部分は、
一般累積座標の `accumulatedOddPart A` と一致する。
-/
theorem ofNat_u_eq_accumulatedOddPart (A : ℕ) :
    (ForwardState.ofNat A).u = accumulatedOddPart A := by
  rfl

/--
一般累積写像を 1 回進めてから `ForwardState` へ移すことと、
先に `ForwardState` へ移して `step` を 1 回進めることは同じ。

これが `Dynamics.Accumulated` と `Finite.Forward` の基本可換図である。
-/
theorem ofNat_accumulatedStep (A : ℕ) :
    ForwardState.ofNat (accumulatedStep A) =
      step (ForwardState.ofNat A) := by
  apply ForwardState.ext
  · have h := accumulatedV2_step A
    simpa [ForwardState.ofNat, step, v2, oddPart,
      accumulatedV2, accumulatedOddPart] using h
  · have h := accumulatedOddPart_step A
    simpa [ForwardState.ofNat, step, v2, oddPart,
      accumulatedV2, accumulatedOddPart, oddStep] using h

/--
一般累積写像を `k` 回進めてから `ForwardState` へ移すことと、
有限層の `run` を `k` 回進めることは完全に一致する。

この定理により、`accumulatedRun` 上の一般定理を既存の finite certificate に
直接接続できる。
-/
theorem ofNat_accumulatedRun (k A : ℕ) :
    ForwardState.ofNat (accumulatedRun k A) =
      run k (ForwardState.ofNat A) := by
  induction k generalizing A with
  | zero =>
      rfl
  | succ k ih =>
      rw [accumulatedRun_succ, run_succ]
      rw [ih]
      rw [ofNat_accumulatedStep]

/--
`run` で得た状態が表す自然数は、一般累積写像 `accumulatedRun` の値そのもの。
-/
theorem run_ofNat_value (k A : ℕ) :
    (run k (ForwardState.ofNat A)).value = accumulatedRun k A := by
  rw [← ofNat_accumulatedRun]
  exact ForwardState.value_ofNat _

/--
`run` 後の 2 指数成分は、対応する `accumulatedRun` の 2 進指数と一致する。
-/
theorem run_ofNat_t (k A : ℕ) :
    (run k (ForwardState.ofNat A)).t =
      accumulatedV2 (accumulatedRun k A) := by
  have h := congrArg ForwardState.t (ofNat_accumulatedRun k A)
  simpa [ForwardState.ofNat, v2, accumulatedV2] using h.symm

/--
`run` 後の奇数部分成分は、対応する `accumulatedRun` の奇数部分と一致する。
-/
theorem run_ofNat_u (k A : ℕ) :
    (run k (ForwardState.ofNat A)).u =
      accumulatedOddPart (accumulatedRun k A) := by
  have h := congrArg ForwardState.u (ofNat_accumulatedRun k A)
  simpa [ForwardState.ofNat, oddPart, accumulatedOddPart] using h.symm

/--
`run` 後の奇数部分を通常の奇数圧縮 Collatz 軌道として読む版。

有限層の状態 `u` は、開始自然数の奇数部分を `oddRun` で同じ回数だけ
進めた値と一致する。
-/
theorem run_ofNat_u_eq_oddRun (k A : ℕ) :
    (run k (ForwardState.ofNat A)).u =
      oddRun k (accumulatedOddPart A) := by
  rw [run_ofNat_u]
  exact accumulatedOddPart_run k A

end Collatz4.Finite
