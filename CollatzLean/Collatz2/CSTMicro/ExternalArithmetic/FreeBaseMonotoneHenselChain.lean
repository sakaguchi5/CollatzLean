import Mathlib.Tactic.Linarith
/-!
# Free-base monotone Hensel chain

restarted branch の `MonotoneSuffixHenselChain` は入口指数 `delta 0 = 1` を持つ。
attached branch では入口直前が exposed corner なので、その初期指数は固定されない。

このファイルでは、入口値を固定せずに

  q_width = 0,
  3 q_i = 2 q_(i+1) + 2^(delta_i) - 1,
  delta_(i+1) = delta_i または delta_i + 1

だけを保持する純粋 Hensel chain を定義する。

後段の repeated-factor 算術では `delta 0 = 1` は本質ではなく、
この free-base 版が attached branch の自然な受け皿になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
入口指数を固定しない monotone Hensel chain。
意味がある添字は `0 <= i <= width` の範囲だけである。
-/
structure FreeBaseMonotoneHenselChain where
  width : ℕ
  width_pos : 0 < width
  delta : ℕ → ℕ
  q : ℕ → ℤ
  delta_pos :
    ∀ i : ℕ, i < width → 0 < delta i
  delta_step :
    ∀ i : ℕ, i + 1 < width →
      delta (i + 1) = delta i ∨
        delta (i + 1) = delta i + 1
  q_terminal : q width = 0
  recurrence :
    ∀ i : ℕ, i < width →
      3 * q i =
        2 * q (i + 1) + (2 : ℤ) ^ delta i - 1

namespace FreeBaseMonotoneHenselChain

/-- shifted quotient `Q_i = q_i + 1`。 -/
def qOne
    (C : FreeBaseMonotoneHenselChain)
    (i : ℕ) : ℤ :=
  C.q i + 1

/-- `q` recurrence を `Q=q+1` の homogeneous-ready form に直す。 -/
theorem qOne_recurrence
    (C : FreeBaseMonotoneHenselChain)
    {i : ℕ}
    (hi : i < C.width) :
    3 * C.qOne i =
      2 * C.qOne (i + 1) + (2 : ℤ) ^ C.delta i := by
  unfold qOne
  have h := C.recurrence i hi
  linarith

end FreeBaseMonotoneHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
