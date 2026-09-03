import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# 第3例探索 1: 左 collar の 2 進切断

巨大な affine 定数を最後まで構成せず、最初の固定幅だけで
開始値の `2^k` 剰余を決めるための純算術核を用意する。

`affineTail B xs` は、既に得られている prefix affine 定数 `B` に対し、
残りの位置 `xs` を順に

  B ↦ 3 B + 2^s

で付け足した値である。

すべての残り位置 `s` が `k ≤ s` を満たすなら、追加された `2^s` は
すべて `2^k` の倍数なので、最終値は

  3^(xs.length) * B + 2^k * R

と exact に分解できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
既知の prefix affine 定数 `B` に、後続位置を順に付け足す。
この定義は探索用の算術核であり、既存の `CSTMicro.affineConst` との bridge は
別ファイルで与えられる想定である。
-/
def affineTail (B : ℕ) : List ℕ → ℕ
  | [] => B
  | s :: ss => affineTail (3 * B + 2 ^ s) ss

/--
`k` より右にある affine 項は、まとめて `2^k` の倍数へ吸収できる。

これは

  B_full ≡ 3^r B_prefix  (mod 2^k)

の、剰余を使わない exact 分解版である。
-/
theorem affineTail_split_twoPow
    (k B : ℕ)
    (xs : List ℕ)
    (hLarge : ∀ s ∈ xs, k ≤ s) :
    ∃ R : ℕ,
      affineTail B xs =
        3 ^ xs.length * B + 2 ^ k * R := by
  induction xs generalizing B with
  | nil =>
      refine ⟨0, ?_⟩
      simp [affineTail]
  | cons s ss ih =>
      have hs : k ≤ s := hLarge s (by simp)
      have hTail : ∀ t ∈ ss, k ≤ t := by
        intro t ht
        exact hLarge t (by simp [ht])
      obtain ⟨R, hR⟩ := ih (B := 3 * B + 2 ^ s) hTail
      refine ⟨3 ^ ss.length * 2 ^ (s - k) + R, ?_⟩
      change affineTail (3 * B + 2 ^ s) ss = _
      rw [hR]
      have hsk : s = k + (s - k) := by omega
      have hpow : 2 ^ s = 2 ^ k * 2 ^ (s - k) := by
        rw [hsk, pow_add]
        simp
      rw [hpow]
      simp only [List.length_cons, pow_succ]
      ring

/--
左 collar 幅を `68` に固定した版。

後続の各 affine 位置が 68 以上なら、full affine 定数は

  3^(残り個数) * B68 + 2^68 * R

と書ける。したがって `mod 2^68` では左 68 側だけが残る。
-/
theorem affineConst_mod_twoPow_of_prefix
    (B68 : ℕ)
    (tailPositions : List ℕ)
    (hLarge : ∀ s ∈ tailPositions, 68 ≤ s) :
    ∃ R : ℕ,
      affineTail B68 tailPositions =
        3 ^ tailPositions.length * B68 + 2 ^ 68 * R := by
  exact affineTail_split_twoPow 68 B68 tailPositions hLarge

end ThirdExampleSearch
end CSTMicro
end Collatz2
