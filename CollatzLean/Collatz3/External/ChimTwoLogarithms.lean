import Mathlib.Data.Int.Basic

/-!
# Chim 型 p-adic two-logarithm の A2 用純粋算術層

source-two even resonance では Collatz 固有の整理を終えると

`3^k ∣ 2^m - 7`

という純粋な指数型合同だけが残る。

従来はこの先を `SourceTwoFinalExternalArithmetic.even_resonance_bound`
という branch field として受け取っていた。このファイルではその責務を
Collatz/Mersenne 語彙から切り離し、p-adic two-logarithm の純粋算術 input に移す。

現段階では Kwok Chi Chim の explicit p-adic two-logarithm estimate を
A2 が実際に使う `p=3, α=2, β=7` へ特殊化した working theorem として隔離する。
数値 cutoff `2^392` は既存 A2 interface が使ってきた安全 cutoff をそのまま維持する。

将来、Chim の一般公式を Lean 化した時点で、この axiom を derived theorem に置き換える。
-/

namespace Collatz3
namespace External
namespace ChimTwoLogarithms

/--
純粋算術 specialization:

`k≥7` かつ `3^k ∣ 2^m-7` なら `k < 2^392`。

Collatz equation、hole、Mersenne block は仮定しない。
-/
axiom twoPow_sub_seven_threeAdic_depth_lt_twoPow392
    {k m : ℕ}
    (hk7 : 7 ≤ k)
    (hdiv : (3 : ℤ) ^ k ∣ (2 : ℤ) ^ m - 7) :
    k < 2 ^ 392

end ChimTwoLogarithms
end External
end Collatz3
