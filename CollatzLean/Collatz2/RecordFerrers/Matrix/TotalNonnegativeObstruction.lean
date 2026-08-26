import CollatzLean.Collatz2.RecordFerrers.Matrix.ExchangeMinor

/-!
# Record–Ferrers RF-C4: 全非負性からの符号障害

既存の全非負行列理論では、全ての有限 minor の determinant は非負である。

RF-C3 により exchange 行列の 2×2 determinant は
`blockExchangeDeterminant` そのものなので、

* exchange 行列が全非負なら exchange determinant は非負
* exchange determinant が負なら全非負ではあり得ない
* 平面非交差経路網の証明書があるなら同じ符号制約を受ける

ことを exact に戻せる。

さらに既存の contextual swap law と合成し、
全非負性が実際の block swap の向きまで制約することを示す。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
2×2 行列が全非負なら、その全体 determinant も非負。

`Matrix.IsTotallyNonneg` の定義から 2×2 全 minor を取り出すだけの橋である。
-/
theorem finTwo_det_nonneg_of_totallyNonnegative
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M.IsTotallyNonneg) :
    0 ≤ M.det := by
  have hMinor :=
    hM
      (n := 2)
      (rows := fun i : Fin 2 => i)
      (cols := fun i : Fin 2 => i)
      (by
        intro a b hab
        exact hab)
      (by
        intro a b hab
        exact hab)
  change Int.le 0
    (M.submatrix
      (fun i : Fin 2 => i)
      (fun i : Fin 2 => i)).det at hMinor
  have hSub :
      M.submatrix
          (fun i : Fin 2 => i)
          (fun i : Fin 2 => i) =
        M := by
    ext i j
    rfl
  rw [hSub] at hMinor
  exact hMinor

/--
exchange 行列が全非負なら block exchange determinant は非負。
-/
theorem blockExchangeDeterminant_nonneg_of_totallyNonnegative
    (u v : Word)
    (hTN : (exchangePathMatrix u v).IsTotallyNonneg) :
    0 ≤ blockExchangeDeterminant u v := by
  rw [← exchangePathMatrix_det u v]
  exact finTwo_det_nonneg_of_totallyNonnegative hTN

/--
exchange determinant が負なら、その二ブロックは
全非負 exchange 行列を持つことができない。

これは符号一個だけで平面経路行列候補を排除する obstruction certificate。
-/
theorem not_totallyNonnegative_of_blockExchangeDeterminant_neg
    (u v : Word)
    (hNeg : blockExchangeDeterminant u v < 0) :
    ¬ (exchangePathMatrix u v).IsTotallyNonneg := by
  intro hTN
  have hNonneg :=
    blockExchangeDeterminant_nonneg_of_totallyNonnegative u v hTN
  linarith

/--
平面非交差経路網の証明書が与えられたなら、
block exchange determinant は必ず非負。

将来、実際の Record–Ferrers network 構成を追加したときの正式な出口。
-/
theorem blockExchangeDeterminant_nonneg_of_planarNetworkCertificate
    (u v : Word)
    (hPlanar : ExchangePlanarNetworkCertificate u v) :
    0 ≤ blockExchangeDeterminant u v :=
  blockExchangeDeterminant_nonneg_of_totallyNonnegative
    u v hPlanar.totallyNonnegative

/--
minimal blocks では四つの 1×1 成分はすでに非負である。
それにもかかわらず exchange determinant が負なら、
2×2 minor の符号だけで全非負性が破れる。
-/
theorem minimalBlocks_not_totallyNonnegative_of_negativeExchange
    {u v : Word}
    (hu : MinimalBlock u)
    (hv : MinimalBlock v)
    (hNeg : blockExchangeDeterminant u v < 0) :
    (0 ≤ exchangePathMatrix u v 0 0 ∧
      0 ≤ exchangePathMatrix u v 0 1 ∧
      0 ≤ exchangePathMatrix u v 1 0 ∧
      0 ≤ exchangePathMatrix u v 1 1) ∧
      ¬ (exchangePathMatrix u v).IsTotallyNonneg := by
  exact
    ⟨exchangePathMatrix_entries_nonneg_of_minimalBlocks hu hv,
      not_totallyNonnegative_of_blockExchangeDeterminant_neg u v hNeg⟩

/--
exchange 行列が全非負なら、任意の prefix / suffix context の中で
`u,v` を `v,u` へ交換したとき `affineConst` は減少しない。

つまり行列側の minor 符号が、実際の word の局所交換方向まで戻る。
-/
theorem affineConst_contextSwap_mono_of_totallyNonnegative
    (leftCtx u v suffix : Word)
    (hTN : (exchangePathMatrix u v).IsTotallyNonneg) :
    (affineConst ((leftCtx ++ (u ++ v)) ++ suffix) : ℤ) ≤
      (affineConst ((leftCtx ++ (v ++ u)) ++ suffix) : ℤ) := by
  have hD :
      0 ≤ blockExchangeDeterminant u v :=
    blockExchangeDeterminant_nonneg_of_totallyNonnegative u v hTN
  have hOuter :
      0 ≤
        ((2 : ℤ) ^ twoSteps leftCtx) *
          ((3 : ℤ) ^ oddSteps suffix) := by
    positivity
  have hProd :
      0 ≤
        (((2 : ℤ) ^ twoSteps leftCtx) *
            ((3 : ℤ) ^ oddSteps suffix)) *
          blockExchangeDeterminant u v :=
    mul_nonneg hOuter hD
  have hSwap :=
    affineConst_swap_two_in_context leftCtx u v suffix
  linarith

/--
実際の context 内 swap が `affineConst` を strict に下げるなら、
その二ブロックの exchange 行列は全非負ではあり得ない。

Collatz / Record–Ferrers 側の順序情報から
既存行列理論の仮定を直接否定できる逆向き obstruction。
-/
theorem not_totallyNonnegative_of_contextSwap_decreases
    (leftCtx u v suffix : Word)
    (hDec :
      (affineConst ((leftCtx ++ (v ++ u)) ++ suffix) : ℤ) <
        (affineConst ((leftCtx ++ (u ++ v)) ++ suffix) : ℤ)) :
    ¬ (exchangePathMatrix u v).IsTotallyNonneg := by
  intro hTN
  have hMono :=
    affineConst_contextSwap_mono_of_totallyNonnegative
      leftCtx u v suffix hTN
  linarith

end RecordFerrers
end Collatz2
