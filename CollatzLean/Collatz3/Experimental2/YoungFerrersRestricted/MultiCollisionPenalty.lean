import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.DiagonalSlackCollision

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Experimental2: 複数 boundary collision の加算ペナルティ

F13 の一衝突 lower bound を、同じ weighted slack を重複カウントせず
全 internal collision へ同時に拡張する。

`internalCollisionLevels` は internal diagonal slack が正になる level を
左から昇順に列挙する。positive width/drop code では F13 によりこれは exact に

`WidthBoundaryAt c t ∧ DropHeightBoundaryAt c t`

を満たす internal level の列である。

weighted slack では level `t` の slack は少なくとも重み `t` を持つので、

`sum collisionLevels ≤ weightedBasisExcess`

となる。従って Young 面積余剰は

`2 * sum collisionLevels`

以上である。

RecordFerrers ではさらに全 collision level が `rankDropGcd` の正の倍数なので、
K 個の collision があれば最小配置は `g,2g,...,Kg` であり、

`area gap ≥ g * K * (K+1)`

を得る。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- `0 + 1 + ... + (n-1)`。division を使わない再帰形。 -/
def staircaseNat : ℕ → ℕ
  | 0 => 0
  | n + 1 => staircaseNat n + n

/-- `1 + ... + n`。 -/
def triangularNat (n : ℕ) : ℕ :=
  staircaseNat n + n

/-- 三角数の一段再帰。 -/
theorem triangularNat_succ
    (n : ℕ) :
    triangularNat (n + 1) = triangularNat n + (n + 1) := by
  unfold triangularNat
  rw [staircaseNat]

/-- 再帰形の三角数は `2T_n = n(n+1)` を満たす。 -/
theorem two_mul_triangularNat
    (n : ℕ) :
    2 * triangularNat n = n * (n + 1) := by
  induction n with
  | zero =>
      simp [triangularNat, staircaseNat]
  | succ n ih =>
      rw [triangularNat_succ]
      rw [Nat.mul_add]
      rw [ih]
      ring

/--
区間 `[start, start+n)` のうち internal slack が正な diagonal level `i+1` を列挙する。
`n=1` の最後の一段は terminal slack なので列挙しない。
-/
def internalCollisionLevelsFrom
    (c : WidthDropCode) : ℕ → ℕ → List ℕ
  | _start, 0 => []
  | _start, 1 => []
  | start, n + 2 =>
      if 0 < internalDiagonalSlack c start then
        (start + 1) :: internalCollisionLevelsFrom c (start + 1) (n + 1)
      else
        internalCollisionLevelsFrom c (start + 1) (n + 1)

/-- whole Frobenius depth の internal collision levels。 -/
def internalCollisionLevels
    (c : WidthDropCode) : List ℕ :=
  internalCollisionLevelsFrom c 0 (frobeniusDepth c)

/-- internal collision level の総和。 -/
def internalCollisionLevelMass
    (c : WidthDropCode) : ℕ :=
  (internalCollisionLevels c).sum

/-- internal collision の個数。 -/
def internalCollisionCount
    (c : WidthDropCode) : ℕ :=
  (internalCollisionLevels c).length

/-- 列挙された level は指定した internal 区間の内部にある。 -/
theorem internalCollisionLevelsFrom_mem_bounds
    (c : WidthDropCode) :
    ∀ start n t,
      t ∈ internalCollisionLevelsFrom c start n →
      start < t ∧ t < start + n
  | _start, 0, t, ht => by
      simp [internalCollisionLevelsFrom] at ht
  | start, 1, t, ht => by
      simp [internalCollisionLevelsFrom] at ht
  | start, n + 2, t, ht => by
      by_cases hHead : 0 < internalDiagonalSlack c start
      · simp only [internalCollisionLevelsFrom, hHead, ↓reduceIte, List.mem_cons] at ht
        rcases ht with rfl | ht
        · omega
        · have hTail :=
            internalCollisionLevelsFrom_mem_bounds c (start + 1) (n + 1) t ht
          omega
      · simp only [internalCollisionLevelsFrom, hHead, ↓reduceIte] at ht
        have hTail :=
          internalCollisionLevelsFrom_mem_bounds c (start + 1) (n + 1) t ht
        omega

/-- 列挙 level は strict に昇順。 -/
theorem internalCollisionLevelsFrom_pairwise_lt
    (c : WidthDropCode) :
    ∀ start n,
      (internalCollisionLevelsFrom c start n).Pairwise (· < ·)
  | _start, 0 => by
      simp [internalCollisionLevelsFrom]
  | start, 1 => by
      simp [internalCollisionLevelsFrom]
  | start, n + 2 => by
      by_cases hHead : 0 < internalDiagonalSlack c start
      · simp only [internalCollisionLevelsFrom, hHead, ↓reduceIte]
        apply List.pairwise_cons.mpr
        constructor
        · intro t ht
          have hBounds :=
            internalCollisionLevelsFrom_mem_bounds
              c (start + 1) (n + 1) t ht
          omega
        · exact
            internalCollisionLevelsFrom_pairwise_lt
              c (start + 1) (n + 1)
      · simp only [internalCollisionLevelsFrom, hHead, ↓reduceIte]
        exact
          internalCollisionLevelsFrom_pairwise_lt
            c (start + 1) (n + 1)

/--
列挙 membership と local positive internal slack の exact 対応。
-/
theorem mem_internalCollisionLevelsFrom_iff
    (c : WidthDropCode) :
    ∀ start n t,
      t ∈ internalCollisionLevelsFrom c start n ↔
        start < t ∧
          t < start + n ∧
          0 < internalDiagonalSlack c (t - 1)
  | _start, 0, t => by
      simp [internalCollisionLevelsFrom]
      omega
  | start, 1, t => by
      simp [internalCollisionLevelsFrom]
      omega
  | start, n + 2, t => by
      by_cases hHead : 0 < internalDiagonalSlack c start
      · simp only [internalCollisionLevelsFrom, hHead, ↓reduceIte, List.mem_cons]
        constructor
        · intro ht
          rcases ht with rfl | ht
          · constructor
            · omega
            constructor
            · omega
            · simpa using hHead
          · have hTail :=
              (mem_internalCollisionLevelsFrom_iff
                c (start + 1) (n + 1) t).1 ht
            exact ⟨by omega, by omega, hTail.2.2⟩
        · rintro ⟨hStart, hEnd, hSlack⟩
          by_cases htEq : t = start + 1
          · exact Or.inl htEq
          · apply Or.inr
            apply
              (mem_internalCollisionLevelsFrom_iff
                c (start + 1) (n + 1) t).2
            exact ⟨by omega, by omega, hSlack⟩
      · simp only [internalCollisionLevelsFrom, hHead, ↓reduceIte]
        constructor
        · intro ht
          have hTail :=
            (mem_internalCollisionLevelsFrom_iff
              c (start + 1) (n + 1) t).1 ht
          exact ⟨by omega, by omega, hTail.2.2⟩
        · rintro ⟨hStart, hEnd, hSlack⟩
          have htNe : t ≠ start + 1 := by
            intro htEq
            subst t
            have : 0 < internalDiagonalSlack c start := by
              simpa using hSlack
            exact hHead this
          apply
            (mem_internalCollisionLevelsFrom_iff
              c (start + 1) (n + 1) t).2
          exact ⟨by omega, by omega, hSlack⟩

/-- whole-shape membership の local slack 版。 -/
theorem mem_internalCollisionLevels_iff
    (c : WidthDropCode)
    (t : ℕ) :
    t ∈ internalCollisionLevels c ↔
      0 < t ∧
        t < frobeniusDepth c ∧
        0 < internalDiagonalSlack c (t - 1) := by
  unfold internalCollisionLevels
  simpa using
    (mem_internalCollisionLevelsFrom_iff
      c 0 (frobeniusDepth c) t)

/--
positive width/drop code では列挙 membership は F13 の boundary collision と exact に一致する。
-/
theorem mem_internalCollisionLevels_iff_boundaryCollision
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (t : ℕ) :
    t ∈ internalCollisionLevels c ↔
      0 < t ∧
        t < frobeniusDepth c ∧
        WidthBoundaryAt c t ∧ DropHeightBoundaryAt c t := by
  rw [mem_internalCollisionLevels_iff]
  constructor
  · rintro ⟨ht, htD, hSlack⟩
    have hDepth : (t - 1) + 2 ≤ frobeniusDepth c := by
      omega
    have hC :=
      (internalDiagonalSlack_pos_iff_boundaryCollision
        c hPos (t - 1) hDepth).1 hSlack
    have htPred : (t - 1) + 1 = t := by
      omega
    rw [htPred] at hC
    exact ⟨ht, htD, hC.1, hC.2⟩
  · rintro ⟨ht, htD, hW, hD⟩
    have hDepth : (t - 1) + 2 ≤ frobeniusDepth c := by
      omega
    have htPred : (t - 1) + 1 = t := by omega
    have hC :
        WidthBoundaryAt c ((t - 1) + 1) ∧
          DropHeightBoundaryAt c ((t - 1) + 1) := by
      simpa [htPred] using ⟨hW, hD⟩
    have hSlack :=
      (internalDiagonalSlack_pos_iff_boundaryCollision
        c hPos (t - 1) hDepth).2 hC
    exact ⟨ht, htD, hSlack⟩

/--
start offset を含む weighted slack。
`start=0` なら通常の `weightedBasisSlack`。
-/
def absoluteWeightedBasisSlack
    (start : ℕ)
    (xs : List ℤ) : ℤ :=
  (start : ℤ) * xs.sum + weightedBasisSlack xs

/-- absolute weight の cons 再帰。 -/
theorem absoluteWeightedBasisSlack_cons
    (start : ℕ)
    (x : ℤ)
    (xs : List ℤ) :
    absoluteWeightedBasisSlack start (x :: xs) =
      ((start + 1 : ℕ) : ℤ) * x +
        absoluteWeightedBasisSlack (start + 1) xs := by
  unfold absoluteWeightedBasisSlack
  simp only [List.sum_cons, weightedBasisSlack]
  push_cast
  ring

/--
全 internal collision level の和は geometric weighted slack 以下。
一衝突 lower bound を足しているのではなく、weighted sum の各係数を一度だけ読む。
-/
theorem internalCollisionLevelsFrom_sum_le_absoluteWeightedDiagonalSlack
    (c : WidthDropCode) :
    ∀ start n,
      ((internalCollisionLevelsFrom c start n).sum : ℤ) ≤
        absoluteWeightedBasisSlack start
          (diagonalBasisSlackVectorFrom c start n)
  | _start, 0 => by
      simp [internalCollisionLevelsFrom,
        diagonalBasisSlackVectorFrom, absoluteWeightedBasisSlack,
        weightedBasisSlack]
  | start, 1 => by
      simp only [
        internalCollisionLevelsFrom,
        List.sum_nil,
        Nat.cast_zero,
        diagonalBasisSlackVectorFrom,
        absoluteWeightedBasisSlack,
        weightedBasisSlack,
        List.sum_singleton
      ]
      positivity
  | start, n + 2 => by
      have ih :=
        internalCollisionLevelsFrom_sum_le_absoluteWeightedDiagonalSlack
          c (start + 1) (n + 1)
      by_cases hHead : 0 < internalDiagonalSlack c start
      · have hSlackZ :
            (1 : ℤ) ≤ (internalDiagonalSlack c start : ℤ) := by
          exact_mod_cast hHead
        have hWeightNonneg :
            (0 : ℤ) ≤ ((start + 1 : ℕ) : ℤ) := by
          positivity
        have hHeadBound :
            ((start + 1 : ℕ) : ℤ) ≤
              ((start + 1 : ℕ) : ℤ) *
                (internalDiagonalSlack c start : ℤ) := by
          calc
            ((start + 1 : ℕ) : ℤ) =
                ((start + 1 : ℕ) : ℤ) * 1 := by ring
            _ ≤
                ((start + 1 : ℕ) : ℤ) *
                  (internalDiagonalSlack c start : ℤ) :=
              mul_le_mul_of_nonneg_left hSlackZ hWeightNonneg
        simp only [
          internalCollisionLevelsFrom,
          hHead,
          ↓reduceIte,
          List.sum_cons,
          Nat.cast_add,
          Nat.cast_one,
          diagonalBasisSlackVectorFrom
        ]
        rw [absoluteWeightedBasisSlack_cons]
        exact add_le_add hHeadBound ih
      · have hSlackZero : internalDiagonalSlack c start = 0 := by
          omega
        simp only [
          internalCollisionLevelsFrom,
          hHead,
          ↓reduceIte,
          diagonalBasisSlackVectorFrom
        ]
        rw [absoluteWeightedBasisSlack_cons, hSlackZero]
        simp only [Nat.cast_zero, mul_zero, zero_add]
        exact ih

/-- whole shape の collision-level mass は weighted basis excess 以下。 -/
theorem internalCollisionLevelMass_le_frobeniusWeightedBasisExcess
    (c : WidthDropCode) :
    (internalCollisionLevelMass c : ℤ) ≤
      frobeniusWeightedBasisExcess c := by
  unfold internalCollisionLevelMass internalCollisionLevels
  unfold frobeniusWeightedBasisExcess
  rw [frobeniusBasisSlacks_eq_diagonalBasisSlackVector]
  unfold diagonalBasisSlackVector
  have h :=
    internalCollisionLevelsFrom_sum_le_absoluteWeightedDiagonalSlack
      c 0 (frobeniusDepth c)
  simpa [absoluteWeightedBasisSlack] using h

/--
複数 internal collision の additive area penalty。
-/
theorem two_mul_internalCollisionLevelMass_le_codeArea_sub_basisWeightZ
    (c : WidthDropCode) :
    (2 : ℤ) * (internalCollisionLevelMass c : ℤ) ≤
      (codeArea c : ℤ) - basisWeightZ (successiveRankVector c) := by
  have hMass := internalCollisionLevelMass_le_frobeniusWeightedBasisExcess c
  have hTwo :=
    mul_le_mul_of_nonneg_left hMass (by norm_num : (0 : ℤ) ≤ 2)
  rw [codeArea_sub_basisWeightZ_eq_two_mul_weightedExcess]
  exact hTwo

/--
同じ `g` の倍数 `a`, `b` が strict 昇順に並ぶとき、
その差は少なくとも `g`。
-/
theorem add_dvdStep_le_of_lt_of_dvd
    {g a b : ℕ}
    (ha : g ∣ a)
    (hb : g ∣ b)
    (hab : a < b) :
    a + g ≤ b := by
  rcases ha with ⟨u, rfl⟩
  rcases hb with ⟨v, rfl⟩
  have huv : u < v := by
    by_contra h
    have hvu : v ≤ u := Nat.le_of_not_gt h
    have hmul : g * v ≤ g * u := Nat.mul_le_mul_left g hvu
    exact (not_lt_of_ge hmul) hab
  have huv' : u + 1 ≤ v := Nat.succ_le_iff.mpr huv
  have hmul := Nat.mul_le_mul_left g huv'
  simpa [Nat.mul_succ, Nat.add_comm] using hmul

/--
strict 昇順かつ `g` の倍数からなる list に対する arithmetic progression lower bound。
`L` は先頭の共通 lower bound。
-/
theorem staircase_sum_lower_bound
    (g : ℕ)
    (hg : 0 < g) :
    ∀ (L : ℕ) (xs : List ℕ),
      xs.Pairwise (· < ·) →
      (∀ x ∈ xs, g ∣ x) →
      (∀ x ∈ xs, L ≤ x) →
      xs.length * L + g * staircaseNat xs.length ≤ xs.sum
  | _L, [], _hPair, _hDvd, _hLower => by
      simp [staircaseNat]
  | L, a :: xs, hPair, hDvd, hLower => by
      have hPairData := List.pairwise_cons.mp hPair
      have haDvd : g ∣ a := hDvd a (by simp)
      have haLower : L ≤ a := hLower a (by simp)
      have hTailDvd : ∀ x ∈ xs, g ∣ x := by
        intro x hx
        exact hDvd x (by simp [hx])
      have hTailLower : ∀ x ∈ xs, L + g ≤ x := by
        intro x hx
        have hax : a < x := hPairData.1 x hx
        have hxDvd : g ∣ x := hTailDvd x hx
        have hGap := add_dvdStep_le_of_lt_of_dvd haDvd hxDvd hax
        omega
      have ih :=
        staircase_sum_lower_bound g hg (L + g) xs
          hPairData.2 hTailDvd hTailLower
      simp only [List.length_cons, List.sum_cons]
      have hEq :
          (xs.length + 1) * L + g * staircaseNat (xs.length + 1) =
            L + (xs.length * (L + g) + g * staircaseNat xs.length) := by
        rw [staircaseNat]
        ring
      rw [hEq]
      exact Nat.add_le_add haLower ih

/--
strict 昇順の正の `g` 倍列の和は `g(1+...+K)` 以上。
-/
theorem gcd_mul_triangular_length_le_sum
    {g : ℕ}
    (hg : 0 < g)
    (xs : List ℕ)
    (hPair : xs.Pairwise (· < ·))
    (hPos : ∀ x ∈ xs, 0 < x)
    (hDvd : ∀ x ∈ xs, g ∣ x) :
    g * triangularNat xs.length ≤ xs.sum := by
  have hLower : ∀ x ∈ xs, g ≤ x := by
    intro x hx
    exact Nat.le_of_dvd (hPos x hx) (hDvd x hx)
  have h := staircase_sum_lower_bound g hg g xs hPair hDvd hLower
  have hEq :
      xs.length * g + g * staircaseNat xs.length =
        g * triangularNat xs.length := by
    unfold triangularNat
    ring
  rw [hEq] at h
  exact h

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/--
RecordFerrers の collision-level list に現れる各 level は rank-drop gcd の倍数。
-/
theorem rankDropGcd_dvd_of_mem_internalCollisionLevels
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : t ∈ internalCollisionLevels R.plateauWidthDropCode) :
    rankDropGcd β m ∣ t := by
  have hInfo :=
    (mem_internalCollisionLevels_iff_boundaryCollision
      R.plateauWidthDropCode
      R.plateauWidthDropCode_positiveWidthDropCode t).1 ht
  have hCanonical : R.HasCanonicalBoundaryCollision t :=
    (R.hasCanonicalBoundaryCollision_iff t).2 hInfo.2.2
  exact R.hasCanonicalBoundaryCollision_rankDropGcd_dvd_nat hCanonical

/--
RecordFerrers の全 internal collision level の和に対する additive area penalty。
-/
theorem two_mul_internalCollisionLevelMass_le_youngCellCount_sub_basisWeightZ
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    (2 : ℤ) *
        (internalCollisionLevelMass R.plateauWidthDropCode : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  unfold youngCellCount successiveRanks
  exact
    two_mul_internalCollisionLevelMass_le_codeArea_sub_basisWeightZ
      R.plateauWidthDropCode

/--
K 個の distinct internal collision は gcd-quantization により
`g,2g,...,Kg` 以上の level mass を持つ。
-/
theorem rankDropGcd_mul_triangular_collisionCount_le_collisionLevelMass
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    rankDropGcd β m *
        triangularNat (internalCollisionCount R.plateauWidthDropCode) ≤
      internalCollisionLevelMass R.plateauWidthDropCode := by
  let xs := internalCollisionLevels R.plateauWidthDropCode
  have hPair : xs.Pairwise (· < ·) := by
    dsimp [xs]
    unfold internalCollisionLevels
    exact
      internalCollisionLevelsFrom_pairwise_lt
        R.plateauWidthDropCode 0 (frobeniusDepth R.plateauWidthDropCode)
  have hPos : ∀ x ∈ xs, 0 < x := by
    intro x hx
    have hBounds :=
      internalCollisionLevelsFrom_mem_bounds
        R.plateauWidthDropCode 0 (frobeniusDepth R.plateauWidthDropCode) x
        (by simpa [xs, internalCollisionLevels] using hx)
    exact hBounds.1
  have hDvd : ∀ x ∈ xs, rankDropGcd β m ∣ x := by
    intro x hx
    exact R.rankDropGcd_dvd_of_mem_internalCollisionLevels
      (by simpa [xs] using hx)
  have h :=
    gcd_mul_triangular_length_le_sum
      (rankDropGcd_pos β m) xs hPair hPos hDvd
  simpa [
    xs,
    internalCollisionCount,
    internalCollisionLevelMass
  ] using h

/--
複数 collision の最終 quadratic penalty。

`K = internalCollisionCount` とすると

`area gap ≥ g * K * (K+1)`。
-/
theorem rankDropGcd_mul_collisionCount_mul_succ_le_youngCellCount_sub_basisWeightZ
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    (rankDropGcd β m : ℤ) *
        (internalCollisionCount R.plateauWidthDropCode : ℤ) *
        ((internalCollisionCount R.plateauWidthDropCode + 1 : ℕ) : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  let K := internalCollisionCount R.plateauWidthDropCode
  let M := internalCollisionLevelMass R.plateauWidthDropCode
  let g := rankDropGcd β m
  have hTriNat : g * triangularNat K ≤ M := by
    simpa [K, M, g] using
      R.rankDropGcd_mul_triangular_collisionCount_le_collisionLevelMass
  have hTri : (g * triangularNat K : ℕ) ≤ M := hTriNat
  have hTriZ :
      ((g * triangularNat K : ℕ) : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast hTri
  have hTwice :
      (2 : ℤ) * ((g * triangularNat K : ℕ) : ℤ) ≤
        (2 : ℤ) * (M : ℤ) :=
    mul_le_mul_of_nonneg_left hTriZ (by norm_num)
  have hArea :
      (2 : ℤ) * (M : ℤ) ≤
        (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
    simpa [M] using
      R.two_mul_internalCollisionLevelMass_le_youngCellCount_sub_basisWeightZ
  have hTwoTriNat := two_mul_triangularNat K
  have hTwoTriZ :
      (2 : ℤ) * (triangularNat K : ℤ) =
        (K : ℤ) * ((K + 1 : ℕ) : ℤ) := by
    exact_mod_cast hTwoTriNat
  calc
    (rankDropGcd β m : ℤ) *
          (internalCollisionCount R.plateauWidthDropCode : ℤ) *
          ((internalCollisionCount R.plateauWidthDropCode + 1 : ℕ) : ℤ) =
        (g : ℤ) * (K : ℤ) * ((K + 1 : ℕ) : ℤ) := by
          simp [g, K]
    _ = (g : ℤ) *
          ((K : ℤ) * ((K + 1 : ℕ) : ℤ)) := by
          ring
    _ = (g : ℤ) *
          ((2 : ℤ) * (triangularNat K : ℤ)) := by
          rw [← hTwoTriZ]
    _ = (2 : ℤ) * ((g * triangularNat K : ℕ) : ℤ) := by
          push_cast
          ring
    _ ≤ (2 : ℤ) * (M : ℤ) := hTwice
    _ ≤ (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := hArea

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
