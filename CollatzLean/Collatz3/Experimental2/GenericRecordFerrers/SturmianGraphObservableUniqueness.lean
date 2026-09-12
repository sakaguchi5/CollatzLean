import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphLazyBridge

/-!
# Collatz3 Experimental2: Sturmian graph path の観測的一意性

`SturmianGraphLazyBridge` では、同じ weight を持つ初期 Sturmian path は
`edgeCount` code が一致することを証明した。

本ファイルでは raw dependent path term の equality を要求せず、
RecordFerrers / Ostrowski 側から実際に観測する二つの量

* 終点 `terminal`,
* level ごとの `edgeCount`

が weight だけから一意に決まることを閉じる。

特に nonempty path では、最上位 level の edgeCount から終点を exact に復元する。
これにより後段では proof certificate の同一性ではなく、数学的に必要な
path observable を canonical code として扱える。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace SturmianPath

/--
全 edge level が `h` 以下で、始点も第 `h` boundary より左なら、終点もその boundary を越えない。
-/
theorem terminal_le_boundary_of_levelBound_le
    {W : UnitOstrowskiWeightSystem}
    {u z N h : ℕ}
    (P : SturmianPath W u z N)
    (hSource : u ≤ sturmianBoundary W h)
    (hBound : P.levelBound ≤ h + 1) :
    z ≤ sturmianBoundary W h := by
  induction P generalizing h with
  | nil =>
      simpa using hSource
  | @cons u v z w total edge tail ih =>
      have hEdgeLevel : edge.level ≤ h := by
        simp [SturmianPath.levelBound] at hBound
        omega
      have hTailBound : tail.levelBound ≤ h + 1 := by
        simp [SturmianPath.levelBound] at hBound
        omega
      have hTarget := edge.target_mem_levelBlock
      have hv : v ≤ sturmianBoundary W h := by
        exact le_trans hTarget.2
          (sturmianBoundary_mono W hEdgeLevel)
      exact ih (h := h) hv hTailBound

/-- levelBound が `0` の path は edge を持たず、終点は始点そのもの。 -/
theorem terminal_eq_source_of_levelBound_zero
    {W : UnitOstrowskiWeightSystem}
    {u z N : ℕ}
    (P : SturmianPath W u z N)
    (hZero : P.levelBound = 0) :
    z = u := by
  cases P with
  | nil => rfl
  | @cons u v z w total edge tail =>
      change max (edge.level + 1) tail.levelBound = 0 at hZero
      have hle : edge.level + 1 ≤ 0 := by
        exact le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hZero)
      omega

/--
nonempty 初期 path の終点は、最上位 level の block start とその level の edgeCount から exact に復元できる。
-/
theorem terminal_eq_blockStart_add_topEdgeCount
    {W : UnitOstrowskiWeightSystem}
    {z N : ℕ}
    (P : SturmianPath W 0 z N)
    (hPos : 0 < P.levelBound) :
    z = sturmianBlockStart W (P.levelBound - 1) +
      P.edgeCount (P.levelBound - 1) := by
  let h := P.levelBound - 1
  have hSucc : h + 1 = P.levelBound := by
    dsimp [h]
    omega
  have hNextZero : P.edgeCount (h + 1) = 0 := by
    apply P.edgeCount_eq_zero_of_levelBound_le
    rw [hSucc]
  have hCountEq := P.edgeCount_eq_progress_change_of_next_zero
    (h := h) hNextZero
  rw [sturmianProgress_zero_state] at hCountEq
  have hCountPos : 0 < P.edgeCount h := by
    simpa [h] using P.edgeCount_top_pos hPos
  have hTerminalLe : z ≤ sturmianBoundary W h := by
    apply P.terminal_le_boundary_of_levelBound_le (h := h)
    · exact Nat.zero_le _
    · rw [hSucc]
  have hStartLt : sturmianBlockStart W h < z := by
    by_contra hnot
    have hz : z ≤ sturmianBlockStart W h := by omega
    have hp := sturmianProgress_eq_zero_of_le_start W hz
    rw [hp] at hCountEq
    omega
  have hProgress :
      sturmianProgress W h z = z - sturmianBlockStart W h := by
    have hNotStart : ¬ z ≤ sturmianBlockStart W h := by omega
    simp [sturmianProgress, hNotStart, hTerminalLe]
  rw [hProgress] at hCountEq
  dsimp [h] at *
  omega

end SturmianPath

/--
同じ weight を持つ初期 path は終点も一致する。
raw proof object equality を使わず、lazy length と最上位 edgeCount から導く。
-/
theorem initialPaths_sameWeight_terminal_eq
    {W : UnitOstrowskiWeightSystem}
    {z₁ z₂ N : ℕ}
    (P : SturmianPath W 0 z₁ N)
    (Q : SturmianPath W 0 z₂ N) :
    z₁ = z₂ := by
  have hLP := initialPath_lazyLength_eq_levelBound P
  have hLQ := initialPath_lazyLength_eq_levelBound Q
  have hBoundEq : P.levelBound = Q.levelBound := by
    rw [hLP, hLQ]
  by_cases hZero : P.levelBound = 0
  · have hQZero : Q.levelBound = 0 := by
      rw [← hBoundEq]
      exact hZero
    have hPterm := P.terminal_eq_source_of_levelBound_zero hZero
    have hQterm := Q.terminal_eq_source_of_levelBound_zero hQZero
    omega
  · have hPPos : 0 < P.levelBound := Nat.pos_of_ne_zero hZero
    have hQPos : 0 < Q.levelBound := by
      rw [← hBoundEq]
      exact hPPos
    have hP := P.terminal_eq_blockStart_add_topEdgeCount hPPos
    have hQ := Q.terminal_eq_blockStart_add_topEdgeCount hQPos
    have hCounts := initialPaths_sameWeight_edgeCount_eq P Q
    calc
      z₁ = sturmianBlockStart W (P.levelBound - 1) +
          P.edgeCount (P.levelBound - 1) := hP
      _ = sturmianBlockStart W (Q.levelBound - 1) +
          Q.edgeCount (Q.levelBound - 1) := by
            rw [hBoundEq, hCounts]
      _ = z₂ := hQ.symm

/--
同じ weight の初期 path について、後段が観測する情報が同じであること。
-/
def InitialSturmianPathObservationallyEquivalent
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (P Q : InitialSturmianPathOfWeight W N) : Prop :=
  P.terminal = Q.terminal ∧
    P.path.edgeCount = Q.path.edgeCount

/-- weight を固定すると初期 path は terminal / edgeCount の意味で一意。 -/
theorem initialSturmianPath_observationallyUnique
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (P Q : InitialSturmianPathOfWeight W N) :
    InitialSturmianPathObservationallyEquivalent P Q := by
  constructor
  · exact initialPaths_sameWeight_terminal_eq P.path Q.path
  · exact initialPaths_sameWeight_edgeCount_eq P.path Q.path

end GenericRecordFerrers
end Experimental2
end Collatz3
