import CollatzLean.Collatz2.RecordFerrers.Deformation.InteriorPermutation

/-!
# Record–Ferrers RF-C1: 三ブロック交換と braid 型恒等式

三つのブロック `u,v,w` を隣接交換だけで並べ替えると、
`uvw` から `wvu` へ行く経路は二通りある。

既存の contextual swap law では各隣接交換差は

`正の外側因子 × blockExchangeDeterminant`

に分離される。

このファイルでは、その二経路の総変化が一致することを
三ブロックだけの exact 恒等式として取り出す。

重要なのは、途中で現れる別 permutation の word を最終結論に残さないことである。
最後には元の `u,v,w` の

* `coefficientGap`
* `blockExchangeDeterminant`

だけからなる局所恒等式が残る。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
`uvw → vuw → vwu → wvu` の三回の隣接交換に対応する総変化量。

各項の係数は contextual swap law に現れる外側因子から得られる。
-/
def braidLeftIncrement
    (u v w : Word) : ℤ :=
  ((3 : ℤ) ^ oddSteps w) * blockExchangeDeterminant u v +
    ((2 : ℤ) ^ twoSteps v) * blockExchangeDeterminant u w +
      ((3 : ℤ) ^ oddSteps u) * blockExchangeDeterminant v w

/--
`uvw → uwv → wuv → wvu` の三回の隣接交換に対応する総変化量。
-/
def braidRightIncrement
    (u v w : Word) : ℤ :=
  ((2 : ℤ) ^ twoSteps u) * blockExchangeDeterminant v w +
    ((3 : ℤ) ^ oddSteps v) * blockExchangeDeterminant u w +
      ((2 : ℤ) ^ twoSteps w) * blockExchangeDeterminant u v

/--
三ブロックを逆順へ運ぶ二つの隣接交換経路は、exact に同じ総変化を与える。

これは permutation の braid 整合性を
`blockExchangeDeterminant` の局所量だけで書いた形である。
-/
theorem braidLeftIncrement_eq_braidRightIncrement
    (u v w : Word) :
    braidLeftIncrement u v w = braidRightIncrement u v w := by
  unfold braidLeftIncrement braidRightIncrement
  unfold blockExchangeDeterminant coefficientGap
  ring

/--
三つの exchange determinant が満たす compact な三体恒等式。

`D(u,v) = blockExchangeDeterminant u v`,
`g(u) = coefficientGap (oddSteps u) (twoSteps u)`
と略記すると

`g(v) D(u,w) = g(w) D(u,v) + g(u) D(v,w)`。

別 permutation の word を完全に消去し、
元の三ブロックだけに残る制約である。
-/
theorem blockExchangeDeterminant_threeBlock
    (u v w : Word) :
    coefficientGap (oddSteps v) (twoSteps v) *
        blockExchangeDeterminant u w =
      coefficientGap (oddSteps w) (twoSteps w) *
          blockExchangeDeterminant u v +
        coefficientGap (oddSteps u) (twoSteps u) *
          blockExchangeDeterminant v w := by
  unfold blockExchangeDeterminant
  ring

/--
三体恒等式の零判定版。

二つの exchange determinant が 0 なら、
中央 gap を掛けた残りの determinant も 0 になる。
後で gap の正値性を組み合わせれば determinant 自身の零判定へ戻せる。
-/
theorem coefficientGap_mul_exchange_eq_zero_of_two_exchange_zero
    (u v w : Word)
    (hUV : blockExchangeDeterminant u v = 0)
    (hVW : blockExchangeDeterminant v w = 0) :
    coefficientGap (oddSteps v) (twoSteps v) *
        blockExchangeDeterminant u w = 0 := by
  rw [blockExchangeDeterminant_threeBlock u v w, hUV, hVW]
  ring

end RecordFerrers
end Collatz2
