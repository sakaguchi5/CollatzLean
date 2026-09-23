import CollatzLean.Collatz3.Binary.Complexity

/-!
# Collatz3 External: powers of three の period-1 break escape

Ralf Stephan, *Aperiodicity and subword complexity in the binary expansion of powers of three*
(arXiv:2607.14774, 2026) の period `p=1` 部分から、この repository が実際に使う
最小の帰結だけを cited input として切り出す。

前版では

`∀ B, ∃ K, period-break≤B → k<K`

という existential な形を置いていた。しかし `K` が `Classical.choose` でしか得られないと、
後段の bounded finite sieve が実際に列挙可能な自然数 bound を持てない。

A2 target `n=1` で必要なのは `B=6` だけなので、ここでは cited input 自体をさらに狭め、
その場合の explicit safe bound だけを置く。

公開されている Stephan の p=1 proof engine では shared endgame の定数は

`c8 = (4 * C(3,1) * log 3 + 4) / log 2`,
`C = max (log c8) 1`

で明示される。repo 内ですでに使っている安全評価

`C(3,1) * log 3 ≤ 8 * 10^12`

と `log 2 > 0.69`, `log 10 < 3` を粗く組み合わせると `C ≤ 42` とできる。
transition 数を 7 以上にする shared endgame の threshold は
`exp ((8 * (2 + C))^2)` で抑えられ、これは `2^180000` より小さい。
そこで successor を含めた自然数 bound として `2^180000 + 1` を採用する。

このファイルではまだ Stephan の digit-block proof 全体を再構成せず、上記の
explicit specialization を cited theorem として隔離する。Collatz equation、hole、
Mersenne normal form は一切仮定しない。
-/

namespace Collatz3
namespace External
namespace StephanTransitions

/--
period-1 break が 6 以下の場合に使う explicit safe depth bound。

`+1` は shared endgame の `ceil(exp(...)) + 1` を安全に自然数側へ包むために付ける。
値は計算可能であり、後段の finite sieve が直接参照できる。
-/
def periodOneBreakSixDepthBound : ℕ :=
  2 ^ 180000 + 1

/--
`3^k` の canonical binary word の period-1 break 数が 6 以下なら
`k < 2^180000 + 1`。

Stephan [2026] の period `p=1` theorem の、A2 が実際に必要とする explicit specialization。
この theorem は Collatz 固有の branch を仮定しない。

将来 p=1 の gap-principle / window-count proof engine を
`External/BakerWustholz.lean` から直接移植した時点で、この axiom は derived theorem に
置き換える。
-/
axiom threePow_periodOne_breakSix_bounded
    {k : ℕ}
    (hk2 : 2 ≤ k)
    (hBreak : Binary.HasPeriodBreakAtMost (3 ^ k) 1 6) :
    k < periodOneBreakSixDepthBound

end StephanTransitions
end External
end Collatz3
