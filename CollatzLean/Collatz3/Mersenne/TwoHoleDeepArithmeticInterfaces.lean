import CollatzLean.Collatz3.Mersenne.TwoHoleM5Modular
import CollatzLean.Collatz3.Mersenne.SourceTwoHoleResonanceThreeTail
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleSmallSource
import CollatzLean.Collatz3.Mersenne.SmallHolePeel

/-!
# Collatz3 Mersenne: two-hole 深部算術の細分化 interface

`TwoHoleFullExternalArithmetic` を一枚岩のまま使う代わりに、現時点で必要な入力を

* 既知の明示的 two-logarithm 定理から得る特殊 corollary、
* 有限 modular certificate、
* まだ genuinely residual な split / target arithmetic、

の三種類へ分離する。

ここで置く定義は axiom ではない。外部数学または有限計算を後から独立に実装するための
`Prop` interface である。
-/

namespace Collatz3
namespace Mersenne

/--
source-even resonance `(a,b)=(1,2)` に必要な Chim 型特殊 corollary。

M₄ reduction が与える四つの residue と exact equation を仮定した形にまで特殊化している。
想定する証明は、内部の elementary 2-adic cleanup と Chim の明示的
3-adic two-logarithm bound の合成である。
-/
def ChimTwoSevenEscape : Prop :=
  ∀ {k n r L : ℕ},
    7 ≤ k →
    (k - 6) % 972 = 966 →
    n % 486 = 394 →
    r % 486 = 3 →
    L % 486 = 391 →
    SourceTwoHoleEquation k n r L 1 2 →
    False

/--
source-odd resonance `a=2` の `M₄ * 2593` finite certificate。

この interface は深い数論を含まない。想定する実装は tail/loop reduction 後の
有限 residue 検査であり、`native_decide` certificate へ置き換える対象である。
-/
def SourceOddM5FiniteCertificate : Prop :=
  ∀ {k n r L b : ℕ},
    7 ≤ k →
    k % 2 = 1 →
    2 < b →
    b < n →
    0 < r →
    0 < L →
    SourceTwoHoleEquation k n r L 2 b →
    False

/--
split-two の `a=1`, `n≥3` branch を M₄ で消す finite certificate。

exit depth は内部定理で even branch なら `r=2`、odd branch なら `r=1` に固定済みなので、
finite certificate 側ではその二型だけを受け取る。
-/
structure SplitAOneM4FiniteCertificate : Prop where
  even_impossible :
    ∀ {k n L b : ℕ},
      7 ≤ k →
      k % 2 = 0 →
      3 ≤ n →
      0 < b → b < L →
      SplitTwoHoleEquation k n 2 L 1 b →
      False
  odd_impossible :
    ∀ {k n L b : ℕ},
      7 ≤ k →
      k % 2 = 1 →
      3 ≤ n →
      0 < b → b < L →
      SplitTwoHoleEquation k n 1 L 1 b →
      False

/-- split odd `a=2` で `M₄*2593` 後に残る三 residue family。 -/
def SplitOddA2ResidueClass (n L b : ℕ) : Prop :=
  (n % 486 = 23 ∧ L % 486 = 21 ∧ b % 486 = 19) ∨
  (n % 486 = 185 ∧ L % 486 = 183 ∧ b % 486 = 181) ∨
  (n % 486 = 347 ∧ L % 486 = 345 ∧ b % 486 = 343)

/--
split odd `a=2` の `M₄*2593` finite reduction。

有限計算で残るのは `r=4`, `k≡1 (mod 1944)` と上の三 residue family だけ、
という部分だけを interface にする。
-/
def SplitOddA2M5FiniteReduction : Prop :=
  ∀ {k n r L b : ℕ},
    7 ≤ k →
    k % 2 = 1 →
    2 < n →
    0 < r →
    0 < b → b < L →
    SplitTwoHoleEquation k n r L 2 b →
    r = 4 ∧
      k % 1944 = 1 ∧
      SplitOddA2ResidueClass n L b

/--
`n < b+4` 側の split odd `a=2` lift を排除する Chim 型特殊 corollary。

想定する証明では `v₂(k-1)` から source width を logarithmic に抑え、
2-adic / 3-adic two-logarithm bound を順に適用する。
-/
def ChimSplitSourceEscape : Prop :=
  ∀ {k n L b : ℕ},
    7 ≤ k →
    k % 2 = 1 →
    k % 1944 = 1 →
    SplitOddA2ResidueClass n L b →
    n < b + 4 →
    SplitTwoHoleEquation k n 4 L 2 b →
    False

/--
`n=b+4` の balanced split odd `a=2` lift を排除する Chim 型特殊 corollary。

`k=1` には実際の exact family があるため、`k≥7` を明示的に仮定する。
-/
def ChimSplitTargetEscape : Prop :=
  ∀ {k n L b : ℕ},
    7 ≤ k →
    k % 2 = 1 →
    k % 1944 = 1 →
    SplitOddA2ResidueClass n L b →
    n = b + 4 →
    SplitTwoHoleEquation k n 4 L 2 b →
    False

/--
`b+4<n` 側の split odd `a=2` lift を排除する Gouillon 型 real two-log corollary。

想定する証明は `|k log 3 - m log 2|` の upper bound と
明示的 lower bound の衝突で source width を logarithmic に抑え、
最後に 3-adic estimate と合わせる。
-/
def GouillonThreeTwoEscape : Prop :=
  ∀ {k n L b : ℕ},
    7 ≤ k →
    k % 2 = 1 →
    k % 1944 = 1 →
    SplitOddA2ResidueClass n L b →
    b + 4 < n →
    SplitTwoHoleEquation k n 4 L 2 b →
    False

/--
現時点で「既知数学または有限計算」として分離できた入力を束ねる。

`split_regular` と `target` の genuinely residual arithmetic はここには含めない。
-/
structure TwoHoleKnownArithmetic : Prop where
  source_even_chim : ChimTwoSevenEscape
  source_odd_m5 : SourceOddM5FiniteCertificate
  split_a_one_m4 : SplitAOneM4FiniteCertificate
  split_odd_a_two_m5 : SplitOddA2M5FiniteReduction
  split_source_chim : ChimSplitSourceEscape
  split_target_chim : ChimSplitTargetEscape
  split_three_two_gouillon : GouillonThreeTwoEscape

/--
split-two で現在なお残る二つの regular interior branch。

low-bit theorem により exit depth は既に

* even `k`, `a≥2` なら `r=1`,
* odd `k`, `a≥3` なら `r=2`

へ固定できるため、residual interface もその exact 形だけを受け取る。
-/
structure SplitTwoRegularResidualArithmetic : Prop where
  even_impossible :
    ∀ {k n L a b : ℕ},
      7 ≤ k →
      k % 2 = 0 →
      2 ≤ a → a < n →
      0 < b → b < L →
      SplitTwoHoleEquation k n 1 L a b →
      False
  odd_impossible :
    ∀ {k n L a b : ℕ},
      7 ≤ k →
      k % 2 = 1 →
      3 ≤ a → a < n →
      0 < b → b < L →
      SplitTwoHoleEquation k n 2 L a b →
      False

/--
target-two の genuinely residual arithmetic。

top target hole は既存 peel により target-one へ戻せるので除外し、
`b+1<L` の interior case だけを small/large source width に分ける。

* `n≤3`: 既存 `n=2→1`, `n=3 mod 7` reduction の後の有限 residual。
* `n≥4`: geometric / valuation / `period-break≤5` reduction の後の finite residual。
-/
structure TargetTwoResidualArithmetic : Prop where
  small_source_impossible :
    ∀ {k n r L a b : ℕ},
      7 ≤ k →
      0 < n → n ≤ 3 →
      0 < r →
      0 < a → a < b →
      b + 1 < L →
      TargetTwoHoleEquation k n r L a b →
      False
  large_source_impossible :
    ∀ {k n r L a b : ℕ},
      7 ≤ k →
      4 ≤ n →
      0 < r →
      0 < a → a < b →
      b + 1 < L →
      TargetTwoHoleEquation k n r L a b →
      False

/-- A2 から既知/有限部分を剥がした後に本当に残る residual package。 -/
structure TwoHoleResidualArithmetic : Prop where
  split_regular : SplitTwoRegularResidualArithmetic
  target : TargetTwoResidualArithmetic

end Mersenne
end Collatz3
