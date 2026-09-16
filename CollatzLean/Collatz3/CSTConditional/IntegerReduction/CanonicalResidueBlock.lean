import CollatzLean.Collatz3.CSTConditional.IntegerReduction.CanonicalResidue
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: canonical residue の block transport

一歩ごとの canonical residue lift を、新しい residue solver を導入せず
任意の有限 block へ持ち上げる。

追加する薄い有限語座標は `streamWord` だけである。

* `streamWord e start r` は無限指数列 `e` の `[start,start+r)` 部分語。
* prefix word の加法分解、depth / affine translation の block 分解は derived theorem。
* canonical residue は block 全体を通して最初の法 `2^(D_start+1)` を保存する。
* 従って block lift index `Q` が一意に存在する。

actual orbit semantics は使わない。
-/

namespace Collatz3
namespace IntegerReduction

/-- 無限指数列の位置 `start` から長さ `r` を切り出した有限語。 -/
def streamWord
    (e : ℕ → ℕ)
    (start : ℕ) : ℕ → Word
  | 0 => []
  | r + 1 => streamWord e start r ++ [e (start + r)]

@[simp] theorem streamWord_zero
    (e : ℕ → ℕ)
    (start : ℕ) :
    streamWord e start 0 = [] := rfl

@[simp] theorem streamWord_succ
    (e : ℕ → ℕ)
    (start r : ℕ) :
    streamWord e start (r + 1) =
      streamWord e start r ++ [e (start + r)] := rfl

/-- `streamWord` の長さは指定長そのもの。 -/
@[simp] theorem streamWord_length
    (e : ℕ → ℕ)
    (start r : ℕ) :
    (streamWord e start r).length = r := by
  induction r with
  | zero => simp [streamWord]
  | succ r ih => simp [streamWord, ih]

/-- `streamWord` は隣接区間の連結に exact に一致する。 -/
theorem streamWord_add
    (e : ℕ → ℕ)
    (start a b : ℕ) :
    streamWord e start (a + b) =
      streamWord e start a ++ streamWord e (start + a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
      simp [streamWord, ih, List.append_assoc, Nat.add_assoc]

/-- 先頭から切った `streamWord` は既存 `prefixWord` と同じ。 -/
theorem streamWord_zero_eq_prefixWord
    (e : ℕ → ℕ)
    (m : ℕ) :
    streamWord e 0 m = prefixWord e m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [streamWord_succ, prefixWord_succ, ih]
      simp

/-- prefix word の block 分解。 -/
theorem prefixWord_add
    (e : ℕ → ℕ)
    (m r : ℕ) :
    prefixWord e (m + r) =
      prefixWord e m ++ streamWord e m r := by
  calc
    prefixWord e (m + r)
        = streamWord e 0 (m + r) := by
            symm
            exact streamWord_zero_eq_prefixWord e (m + r)
    _ = streamWord e 0 m ++ streamWord e (0 + m) r :=
      streamWord_add e 0 m r
    _ = prefixWord e m ++ streamWord e m r := by
      rw [streamWord_zero_eq_prefixWord]
      simp

/-- segment word の prefix は shorter segment word そのもの。 -/
theorem streamWord_take
    (e : ℕ → ℕ)
    (start r t : ℕ)
    (ht : t ≤ r) :
    (streamWord e start r).take t = streamWord e start t := by
  have hr : r = t + (r - t) := by omega
  rw [hr, streamWord_add]
  rw [List.take_append_of_le_length]
  · simp
  · simp

/-- segment word の prefix depth は shorter segment の total depth。 -/
theorem prefixTwoDepth_streamWord
    (e : ℕ → ℕ)
    (start r t : ℕ)
    (ht : t ≤ r) :
    Word.prefixTwoDepth (streamWord e start r) t =
      Word.twoSteps (streamWord e start t) := by
  unfold Word.prefixTwoDepth
  rw [streamWord_take e start r t ht]

/-- prefix depth の block 加法公式。 -/
theorem prefixDepth_add
    (e : ℕ → ℕ)
    (m r : ℕ) :
    prefixDepth e (m + r) =
      prefixDepth e m + Word.twoSteps (streamWord e m r) := by
  unfold prefixDepth
  rw [prefixWord_add, Word.twoSteps_append]

/-- prefix depth は index を前へ進めると減らない。 -/
theorem prefixDepth_le_add
    (e : ℕ → ℕ)
    (m r : ℕ) :
    prefixDepth e m ≤ prefixDepth e (m + r) := by
  rw [prefixDepth_add]
  omega

/-- prefix affine translation の block 加法公式。 -/
theorem prefixAffine_add
    (e : ℕ → ℕ)
    (m r : ℕ) :
    prefixAffine e (m + r) =
      3 ^ r * prefixAffine e m +
        2 ^ prefixDepth e m * Word.affineConst (streamWord e m r) := by
  unfold prefixAffine prefixDepth
  rw [prefixWord_add, Word.affineConst_append]
  have hOdd : Word.oddSteps (streamWord e m r) = r := by
    simp [Word.oddSteps]
  rw [hOdd]

/--
positive exponent 列では、任意の長さの先まで進めても
canonical residue は開始時の法 `2^(D_m+1)` で同じ合同類に残る。
-/
theorem canonicalResidue_add_modEq
    (e : ℕ → ℕ)
    (hPos : ∀ n : ℕ, 0 < e n)
    (m r : ℕ) :
    canonicalResidue e (m + r) ≡ canonicalResidue e m
      [MOD 2 ^ (prefixDepth e m + 1)] := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      have hStep := canonicalResidue_succ_modEq e hPos (m + r)
      have hDepthLe :
          prefixDepth e m + 1 ≤ prefixDepth e (m + r) + 1 := by
        have h := prefixDepth_le_add e m r
        omega
      have hDvd :
          2 ^ (prefixDepth e m + 1) ∣
            2 ^ (prefixDepth e (m + r) + 1) :=
        Nat.pow_dvd_pow 2 hDepthLe
      have hStepSmall := hStep.of_dvd hDvd
      have hIndex : m + (r + 1) = (m + r) + 1 := by omega
      rw [hIndex]
      exact hStepSmall.trans ih

/--
block 全体の canonical lift index `Q` が存在する。

`R_(m+r) = R_m + 2^(D_m+1) Q`。
-/
theorem exists_canonicalResidue_blockLift
    (e : ℕ → ℕ)
    (hPos : ∀ n : ℕ, 0 < e n)
    (m r : ℕ) :
    ∃ Q : ℕ,
      canonicalResidue e (m + r) =
        canonicalResidue e m +
          2 ^ (prefixDepth e m + 1) * Q := by
  let M := 2 ^ (prefixDepth e m + 1)
  let R := canonicalResidue e m
  let R' := canonicalResidue e (m + r)
  have hCong := canonicalResidue_add_modEq e hPos m r
  have hRlt : R < M := by
    dsimp [R, M]
    exact canonicalResidue_lt_modulus e m
  have hMod : R' % M = R := by
    change R' % M = R % M at hCong
    rw [Nat.mod_eq_of_lt hRlt] at hCong
    exact hCong
  refine ⟨R' / M, ?_⟩
  have hDecomp := Nat.mod_add_div R' M
  rw [hMod] at hDecomp
  dsimp [R, R', M]
  exact hDecomp.symm

/-- block lift index の表示は一意。 -/
theorem canonicalResidue_blockLift_unique
    (e : ℕ → ℕ)
    (m r Q₁ Q₂ : ℕ)
    (h₁ :
      canonicalResidue e (m + r) =
        canonicalResidue e m +
          2 ^ (prefixDepth e m + 1) * Q₁)
    (h₂ :
      canonicalResidue e (m + r) =
        canonicalResidue e m +
          2 ^ (prefixDepth e m + 1) * Q₂) :
    Q₁ = Q₂ := by
  have hMul :
      2 ^ (prefixDepth e m + 1) * Q₁ =
        2 ^ (prefixDepth e m + 1) * Q₂ := by
    omega
  exact Nat.mul_left_cancel (Arithmetic.twoPow_pos _) hMul

/-- block lift が `0` であることは、両端 canonical residue が等しいことと同値。 -/
theorem canonicalResidue_blockLift_zero_iff
    (e : ℕ → ℕ)
    (m r : ℕ) :
    (canonicalResidue e (m + r) =
        canonicalResidue e m +
          2 ^ (prefixDepth e m + 1) * 0) ↔
      canonicalResidue e (m + r) = canonicalResidue e m := by
  simp

end IntegerReduction
end Collatz3
