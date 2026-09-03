import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.CanonicalOstrowskiTransferFold

/-!
# 第3例探索: canonical Ostrowski decomposition の最小 rank 化

従来の `actualCriticalOstrowskiBlockScales n` は、正しさを簡潔にするため
`boundedActualCriticalOstrowskiExpansionChoice n n ...` を使っていた。
そのまま実行すると recursion parameter が prefix length `n` になり、
巨大 window では計算上不利である。

ここでは

  n < criticalPowerP (R + 3)

を初めて満たす `R` を、0 から順に停止判定しながら探す。
構造再帰のため fuel は `n+1` を与えるが、実行時には条件が成立した時点で停止する。
`self_lt_criticalPowerP_add_three n` により `R=n` までには必ず停止する。

得られた最小 rank を既存 bounded Ostrowski expansion に渡すことで、
数学的内容を変えずに canonical block decomposition の再帰深さを rank 程度へ落とす。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
`r` から右へ、`n < P_(r+3)` を初めて満たす rank を探す実行用ループ。
`fuel` は termination certificate であり、条件成立時には直ちに停止する。
-/
def actualCriticalOstrowskiRankAux
    (n r : ℕ) : ℕ → ℕ
  | 0 => r
  | fuel + 1 =>
      if n < criticalPowerP (r + 3) then
        r
      else
        actualCriticalOstrowskiRankAux n (r + 1) fuel

/--
十分右側に必ず成功点があるなら、rank search の返り値も実際に bound を満たす。
-/
theorem actualCriticalOstrowskiRankAux_spec
    (n r fuel : ℕ)
    (hFuel : 0 < fuel)
    (hBound : n < criticalPowerP (r + fuel + 2)) :
    n <
      criticalPowerP
        (actualCriticalOstrowskiRankAux n r fuel + 3) := by
  induction fuel generalizing r with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases hHere : n < criticalPowerP (r + 3)
      · simp [actualCriticalOstrowskiRankAux, hHere]
      · simp only [actualCriticalOstrowskiRankAux, hHere, ↓reduceIte]
        by_cases h0 : fuel = 0
        · subst fuel
          exfalso
          apply hHere
          simpa using hBound
        · apply ih (r := r + 1)
          · omega
          · have hIndex :
                r + 1 + fuel + 2 =
                  r + (fuel + 1) + 2 := by
              omega
            rw [hIndex]
            exact hBound

/--
search が `k` より右まで進んだなら、`k` ではまだ Ostrowski bound が成立していない。
これが「最初に成功する rank」であることの最小性。
-/
theorem actualCriticalOstrowskiRankAux_minimal
    (n r fuel k : ℕ)
    (hrk : r ≤ k)
    (hk : k < actualCriticalOstrowskiRankAux n r fuel) :
    ¬ n < criticalPowerP (k + 3) := by
  induction fuel generalizing r k with
  | zero =>
      simp [actualCriticalOstrowskiRankAux] at hk
      omega
  | succ fuel ih =>
      by_cases hHere : n < criticalPowerP (r + 3)
      · have hEq :
          actualCriticalOstrowskiRankAux n r (fuel + 1) = r := by
          simp [actualCriticalOstrowskiRankAux, hHere]
        rw [hEq] at hk
        omega
      · have hk' :
          k < actualCriticalOstrowskiRankAux n (r + 1) fuel := by
          simpa [actualCriticalOstrowskiRankAux, hHere] using hk
        by_cases hkr : k = r
        · subst k
          exact hHere
        · exact
            ih (r := r + 1) (k := k)
              (by omega) hk'

/--
`n` に必要な最小 Ostrowski rank。
`fuel=n+1` は単なる termination bound で、実際の評価は成功 rank で停止する。
-/
def actualCriticalOstrowskiRank
    (n : ℕ) : ℕ :=
  actualCriticalOstrowskiRankAux n 0 (n + 1)

/-- 最小 rank は実際に `n < P_(R+3)` を満たす。 -/
theorem actualCriticalOstrowskiRank_spec
    (n : ℕ) :
    n < criticalPowerP (actualCriticalOstrowskiRank n + 3) := by
  unfold actualCriticalOstrowskiRank
  apply actualCriticalOstrowskiRankAux_spec
  · omega
  · simpa using self_lt_criticalPowerP_add_three n

/-- 最小 rank より左では bound はまだ成立しない。 -/
theorem actualCriticalOstrowskiRank_minimal
    (n k : ℕ)
    (hk : k < actualCriticalOstrowskiRank n) :
    ¬ n < criticalPowerP (k + 3) := by
  unfold actualCriticalOstrowskiRank at hk
  exact
    actualCriticalOstrowskiRankAux_minimal
      n 0 (n + 1) k (Nat.zero_le k) hk

/-- 最小 rank は粗い安全上界 `n` を越えない。 -/
theorem actualCriticalOstrowskiRank_le
    (n : ℕ) :
    actualCriticalOstrowskiRank n ≤ n := by
  by_contra hnot
  have hnLt : n < actualCriticalOstrowskiRank n := by omega
  have hFail := actualCriticalOstrowskiRank_minimal n n hnLt
  exact hFail (self_lt_criticalPowerP_add_three n)

/--
最小 rank を使う高速 canonical scale-block list。
bounded expansion の数学的定義は既存のものをそのまま再利用する。
-/
def fastActualCriticalOstrowskiBlockScales
    (n : ℕ) : List ℕ :=
  boundedActualCriticalOstrowskiBlockScales
    (actualCriticalOstrowskiRank n)
    n
    (actualCriticalOstrowskiRank_spec n)

/-- 高速 block list も prefix length `n` を exact に覆う。 -/
theorem fastActualCriticalOstrowskiBlockScales_mass_eq
    (n : ℕ) :
    actualCriticalBlockScaleMass
        (fastActualCriticalOstrowskiBlockScales n) = n := by
  unfold fastActualCriticalOstrowskiBlockScales
  exact
    boundedActualCriticalOstrowskiBlockScales_mass_eq
      (actualCriticalOstrowskiRank n)
      n
      (actualCriticalOstrowskiRank_spec n)

/-- 高速 scale list を actual consecutive phase blocks へ展開する。 -/
def fastActualCriticalOstrowskiPhaseBlocks
    (n : ℕ) : List ActualCriticalPhaseBlock :=
  actualCriticalPhaseBlocksFrom 0
    (fastActualCriticalOstrowskiBlockScales n)

/--
最小 rank の canonical block list 全体を affine transfer にまとめた高速版。
-/
def fastActualCriticalOstrowskiTransfer
    (n : ℕ)
    (y : ℤ) : StandardBlockTransfer :=
  actualPhaseBlockTransferFold
    (fastActualCriticalOstrowskiPhaseBlocks n) y

/--
高速 transfer も zero state から full prefix defect を exact に生成する。
従って既存 `actualCriticalOstrowskiTransfer` と数学的な出力は同一である。
-/
theorem fastActualCriticalOstrowskiTransfer_apply_zero
    (n : ℕ)
    (y : ℤ) :
    (fastActualCriticalOstrowskiTransfer n y).apply 0 =
      criticalPrefixDefectZ n y := by
  unfold fastActualCriticalOstrowskiTransfer
    fastActualCriticalOstrowskiPhaseBlocks
  rw [actualPhaseBlockTransferFold_phaseBlocksFrom]
  calc
    (actualScaleTransferFrom
        0 (fastActualCriticalOstrowskiBlockScales n) y).apply 0 =
      (actualScaleTransferFrom
        0 (fastActualCriticalOstrowskiBlockScales n) y).apply
          (criticalPrefixDefectZ 0 y) := by
            simp
    _ = criticalPrefixDefectZ
          (0 + actualCriticalBlockScaleMass
            (fastActualCriticalOstrowskiBlockScales n)) y :=
          actualScaleTransferFrom_apply_prefixDefect
            0 (fastActualCriticalOstrowskiBlockScales n) y
    _ = criticalPrefixDefectZ n y := by
          rw [fastActualCriticalOstrowskiBlockScales_mass_eq]
          simp

/--
従来 canonical transfer と高速 transfer は、zero state に対して同じ full defect を返す。
探索器を高速版へ差し替えても証明対象は変わらない。
-/
theorem fastActualCriticalOstrowskiTransfer_apply_zero_eq_original
    (n : ℕ)
    (y : ℤ) :
    (fastActualCriticalOstrowskiTransfer n y).apply 0 =
      (actualCriticalOstrowskiTransfer n y).apply 0 := by
  rw [fastActualCriticalOstrowskiTransfer_apply_zero,
      actualCriticalOstrowskiTransfer_apply_zero]

end ThirdExampleSearch
end CSTMicro
end Collatz2
