import CollatzLean.Collatz3.FixedFiber.UniversalExcess
import CollatzLean.Collatz3.Semantics.Predecessor

/-!
# Collatz3: 先頭指数を付けたときの fixed-fiber excess

`UniversalExcess` の `E_RF` に対して、指数 `e` を word の先頭へ付ける操作を調べる。
ここでは RecordFerrers を導入しない。

核心は、tail の odd-step 数を `q` としたとき

`E_RF (e :: w) + 2 * (3^q - 2^q) = 2^e * affineConst w`

となることである。
したがって同じ tail に入る逆向き枝で指数を `e` から `e+2` へ増やすと、
左辺の中心化座標は exact に 4 倍される。

実際の逆向き枝では `BackwardStep.add_two` により前駆点も
`x ↦ 4*x+1` と移るので、逆コラッツ木の同一分岐族と `E_RF` の 4 倍相似が一致する。
-/

namespace Collatz3
namespace Word

/--
fixed-fiber baseline `D_q = 3^q - 2^q` の 1 段再帰。

`D_(q+1) = 3^q + 2*D_q`

という形は、先頭指数を付けた affine translation
`3^q + 2^e * B` と比較するときに使う。
-/
theorem fixedFiberBaseline_succ (q : ℕ) :
    fixedFiberBaseline (q + 1) =
      3 ^ q + 2 * fixedFiberBaseline q := by
  have hPow : 2 ^ q ≤ 3 ^ q := by
    exact Nat.pow_le_pow_left (by decide : 2 ≤ (3 : ℕ)) _
  unfold fixedFiberBaseline
  rw [pow_succ, pow_succ]
  omega

/--
先頭指数 `e` と tail `w` に対する中心化 `E_RF` 座標。

`E_RF (e :: w)` そのものではなく、tail の fixed-fiber baseline `D_q` を
`2*D_q` だけ足した量を使う。この平行移動によって逆向き枝の伸縮が純粋な
`2^e` 倍として見える。
-/
def prependExcessCoordinate (e : ℕ) (w : Word) : ℕ :=
  universalExcess (e :: w) +
    2 * fixedFiberBaseline (oddSteps w)

/--
valid tail `w` の先頭に正指数 `e` を付けると、中心化 `E_RF` 座標は
`2^e * affineConst w` に exact に一致する。

これは `E_RF` の枝分かれ座標としての基本式である。
-/
theorem prependExcessCoordinate_eq_twoPow_mul_affineConst
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    prependExcessCoordinate e w =
      2 ^ e * affineConst w := by
  have hConsValid : Valid (e :: w) := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact he
    · exact hValid a ha
  have hCons :=
    affineConst_eq_fixedFiberBaseline_add_universalExcess hConsValid
  have hAffine := affineConst_cons e w
  have hBase := fixedFiberBaseline_succ (oddSteps w)
  unfold prependExcessCoordinate
  rw [oddSteps_cons] at hCons
  omega

/--
中心化 `E_RF` 座標を tail の `E_RF` だけで書いた形。

`q = oddSteps w`, `D_q = 3^q - 2^q` とすれば

`E_RF (e :: w) + 2*D_q = 2^e * (E_RF(w) + D_q)`。

この形は `affineConst` を消しているため、将来 RecordFerrers の面積座標へ
接続するときの直接 bridge として使える。
-/
theorem prependExcessCoordinate_eq_twoPow_mul_excess_add_baseline
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    prependExcessCoordinate e w =
      2 ^ e *
        (universalExcess w + fixedFiberBaseline (oddSteps w)) := by
  rw [prependExcessCoordinate_eq_twoPow_mul_affineConst
        (e := e) (w := w) he hValid]
  rw [affineConst_eq_fixedFiberBaseline_add_universalExcess hValid]
  ring

/--
先頭指数を付けたときの `E_RF` 更新則。

`q = oddSteps w`, `D_q = 3^q - 2^q` と書けば

`E_RF (e :: w) = 2^e * E_RF(w) + (2^e - 2) * D_q`。

指数 `e=1` では補正項が消え、単に `E_RF` が 2 倍される。
-/
theorem universalExcess_cons
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    universalExcess (e :: w) =
      2 ^ e * universalExcess w +
        (2 ^ e - 2) * fixedFiberBaseline (oddSteps w) := by
  have hCenter :=
    prependExcessCoordinate_eq_twoPow_mul_affineConst
      (e := e) (w := w) he hValid
  have hTail :=
    affineConst_eq_fixedFiberBaseline_add_universalExcess hValid
  have hTwo : 2 ≤ 2 ^ e :=
    two_le_twoPow_of_pos he
  have hScale :
      2 ^ e * fixedFiberBaseline (oddSteps w) =
        (2 ^ e - 2) * fixedFiberBaseline (oddSteps w) +
          2 * fixedFiberBaseline (oddSteps w) := by
    calc
      2 ^ e * fixedFiberBaseline (oddSteps w) =
          ((2 ^ e - 2) + 2) * fixedFiberBaseline (oddSteps w) := by
            rw [Nat.sub_add_cancel hTwo]
      _ =
          (2 ^ e - 2) * fixedFiberBaseline (oddSteps w) +
            2 * fixedFiberBaseline (oddSteps w) := by ring
  have hEq :
      universalExcess (e :: w) +
          2 * fixedFiberBaseline (oddSteps w) =
        (2 ^ e * universalExcess w +
            (2 ^ e - 2) * fixedFiberBaseline (oddSteps w)) +
          2 * fixedFiberBaseline (oddSteps w) := by
    change prependExcessCoordinate e w = _
    rw [hCenter, hTail, Nat.mul_add, hScale]
    ring
  exact Nat.add_right_cancel hEq

/--
指数 `1` を先頭へ付ける場合、`E_RF` は補正項なしに exact に 2 倍される。
-/
theorem universalExcess_one_cons
    {w : Word}
    (hValid : Valid w) :
    universalExcess (1 :: w) =
      2 * universalExcess w := by
  simpa using
    (universalExcess_cons (e := 1) (w := w) (by decide) hValid)

/--
同じ tail `w` に対して先頭指数を `e` から `e+2` に増やすと、
中心化 `E_RF` 座標は exact に 4 倍される。

これは fixed-fiber 側だけで見た逆枝の 4 倍相似である。
-/
theorem prependExcessCoordinate_add_two
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    prependExcessCoordinate (e + 2) w =
      4 * prependExcessCoordinate e w := by
  rw [prependExcessCoordinate_eq_twoPow_mul_affineConst
        (e := e + 2) (w := w) (by omega) hValid]
  rw [prependExcessCoordinate_eq_twoPow_mul_affineConst
        (e := e) (w := w) he hValid]
  rw [pow_add]
  norm_num
  ring

/--
実際の逆向き 1 step と同じ tail run を固定した 4 倍相似。

`x --e--> y` を逆向きに読んでいるとき、指数を `e+2` にした次の枝は
`4*x+1` から同じ `y` へ入る。さらに tail `w` をそのまま続ければ同じ終点 `z` に到達し、
その二つの word の中心化 `E_RF` 座標は exact に 4 倍の関係にある。

したがって

`x ↦ 4*x+1`

という逆コラッツ木の同一分岐族と

`centered E_RF ↦ 4 * centered E_RF`

という fixed-fiber 相似が同じ `e ↦ e+2` 操作から同時に導かれる。
-/
theorem backwardBranch_add_two_four_similarity
    {e x y z : ℕ}
    {w : Word}
    (hStep : BackwardStep e y x)
    (hTail : Runs w y z) :
    BackwardStep (e + 2) y (4 * x + 1) ∧
      Runs ((e + 2) :: w) (4 * x + 1) z ∧
      prependExcessCoordinate (e + 2) w =
        4 * prependExcessCoordinate e w := by
  have hValid : Valid w := Runs.valid hTail
  have he : 0 < e := BackwardStep.exponent_pos hStep
  have hNext : BackwardStep (e + 2) y (4 * x + 1) :=
    BackwardStep.add_two hStep
  refine ⟨hNext, Runs.cons hNext hTail, ?_⟩
  exact prependExcessCoordinate_add_two he hValid

end Word
end Collatz3
