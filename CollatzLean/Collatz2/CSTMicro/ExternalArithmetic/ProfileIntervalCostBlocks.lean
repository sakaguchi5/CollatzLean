import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileBlockReduction
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnLayerCostDynamics

/-!
# Profile interval cost blocks

Stage 6 では profile numerator を maximal layer intervals と Ostrowski phase endpoints に
分解した。本ファイルでは同じ profile cells を positive cell-cost 側から読む。

canonical cell `(k,j)` に対して signed cost

  C(k,j) = G - D(k,j)

を取り、local inverse equationから pure に

  3^m C(k,j)
    = G T(k,j) + 2^(beta_k-j-1) 3^(m-k-1)

を得る。従って fixed layer interval `[a,b)` では

  3^m C_I = G T_I + W_I Phi[a,b],

  W_I = 2^(beta_a-j-1) 3^(m-b).

さらに

  Phi[a,b] = F[a,b](y) + Gamma[a,b] y

と

  W_I Gamma[a,b]
    = boundary(b) - boundary(a)

を組み合わせ、interval cost を

* interior affine defect,
* two endpoint boundary terms

へ exact に分離する。

最後に全 profile cells を足して

  3^m C(h) = G T(h) + N(h)

を得て、Stage 5 の tiny-lift equationと合成し

  Psi(m) - G (y - T(h))
    = 3^m (q + C(h))

という positive-cost normal formを公開する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-! ## 1. pure canonical cell cost coordinates -/

/-- canonical column/layer cell の tail dyadic depth。 -/
def profileCellTailDepth
    (H k j : ℕ) : ℕ :=
  H - columnLayerPosition k j

/-- small modulus `2^d` での local inverse representative。 -/
def profileCellLocalInverse
    (H k j : ℕ) : ℕ :=
  (invThreePow (profileCellTailDepth H k j) (k + 1)).val

/-- `3^(k+1) u = 1 + 2^d q` の local quotient。 -/
def profileCellLocalQuotient
    (H k j : ℕ) : ℕ :=
  (3 ^ (k + 1) * profileCellLocalInverse H k j) /
    (2 ^ profileCellTailDepth H k j)

/-- right odd exponent まで掛けた full-scale quotient。 -/
def profileCellScaledQuotient
    (H m k j : ℕ) : ℤ :=
  (profileCellLocalQuotient H k j : ℤ) *
    (3 : ℤ) ^ (m - (k + 1))

/-- canonical Farey residue の terminal-gap complement を signed integer で読む。 -/
def profileSignedCellCost
    (H m k j : ℕ) : ℤ :=
  (columnLayerGap H m : ℤ) -
    columnLayerFareyResidue H m k j

private theorem one_lt_twoPow_of_pos
    {d : ℕ}
    (hd : 0 < d) :
    1 < 2 ^ d := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [pow_succ]
  have hp : 0 < 2 ^ t := by positivity
  nlinarith

/-- local inverse representative は small modulus 未満。 -/
theorem profileCellLocalInverse_lt
    {H k j : ℕ} :
    profileCellLocalInverse H k j <
      2 ^ profileCellTailDepth H k j := by
  have : NeZero (2 ^ profileCellTailDepth H k j) :=
    ⟨by positivity⟩
  unfold profileCellLocalInverse
  exact ZMod.val_lt _

/-- local inverse を cast し直すと `invThreePow` に戻る。 -/
theorem profileCellLocalInverse_cast
    {H k j : ℕ} :
    ((profileCellLocalInverse H k j : ℕ) :
        ZMod (2 ^ profileCellTailDepth H k j)) =
      invThreePow (profileCellTailDepth H k j) (k + 1) := by
  have : NeZero (2 ^ profileCellTailDepth H k j) :=
    ⟨by positivity⟩
  unfold profileCellLocalInverse
  exact ZMod.natCast_zmod_val _

/-- small modulus 上で `3^(k+1) u = 1`。 -/
theorem threePow_mul_profileCellLocalInverse_cast
    {H k j : ℕ} :
    (3 : ZMod (2 ^ profileCellTailDepth H k j)) ^ (k + 1) *
        ((profileCellLocalInverse H k j : ℕ) :
          ZMod (2 ^ profileCellTailDepth H k j)) = 1 := by
  rw [profileCellLocalInverse_cast]
  exact
    threePow_mul_invThreePow
      (profileCellTailDepth H k j) (k + 1)

/-- ordinary remainder として local inverse equation を読む。 -/
theorem profileCellLocalInverse_mod_eq_one
    {H k j : ℕ}
    (hd : 0 < profileCellTailDepth H k j) :
    (3 ^ (k + 1) * profileCellLocalInverse H k j) %
        (2 ^ profileCellTailDepth H k j) = 1 := by
  have hCast :
      (((3 ^ (k + 1) * profileCellLocalInverse H k j : ℕ)) :
          ZMod (2 ^ profileCellTailDepth H k j)) =
        ((1 : ℕ) : ZMod (2 ^ profileCellTailDepth H k j)) := by
    push_cast
    simpa using
      (threePow_mul_profileCellLocalInverse_cast
        (H := H) (k := k) (j := j))
  have hVal := congrArg ZMod.val hCast
  have hOne : 1 < 2 ^ profileCellTailDepth H k j :=
    one_lt_twoPow_of_pos hd
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hOne] using hVal

/--
local Euclidean division の exact equation。

  3^(k+1) u = 1 + 2^d q.
-/
theorem threePow_mul_profileCellLocalInverse_eq_one_add
    {H k j : ℕ}
    (hd : 0 < profileCellTailDepth H k j) :
    3 ^ (k + 1) * profileCellLocalInverse H k j =
      1 + 2 ^ profileCellTailDepth H k j *
        profileCellLocalQuotient H k j := by
  have hmod :=
    profileCellLocalInverse_mod_eq_one
      (H := H) (k := k) (j := j) hd
  have hdiv :=
    Nat.mod_add_div
      (3 ^ (k + 1) * profileCellLocalInverse H k j)
      (2 ^ profileCellTailDepth H k j)
  rw [hmod] at hdiv
  unfold profileCellLocalQuotient
  exact hdiv.symm

/-! ## 2. occupied profile cell の exact positive cost law -/

/-- occupied cell の standard position は terminal time より前。 -/
theorem profileCell_position_lt_terminal
    {H m k j : ℕ}
    (hTerminal : H = beattyIndex m + 1)
    (hk : k < m)
    (hj : j < beattyIndex k) :
    columnLayerPosition k j < H := by
  have hkPos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := by omega
    subst k
    simp at hj
  have hPosEq :
      columnLayerPosition k j = beattyIndex k - j - 1 := by
    unfold columnLayerPosition
    rw [← beattyIndex_eq_wordCriticalHeight hkPos]
  have hiLtBeta : columnLayerPosition k j < beattyIndex k := by
    rw [hPosEq]
    omega
  have hBeta := beattyIndex_strictMono hk
  rw [hTerminal]
  omega

/-- occupied cell の tail depth は positive。 -/
theorem profileCellTailDepth_pos
    {H m k j : ℕ}
    (hTerminal : H = beattyIndex m + 1)
    (hk : k < m)
    (hj : j < beattyIndex k) :
    0 < profileCellTailDepth H k j := by
  unfold profileCellTailDepth
  exact Nat.sub_pos_of_lt
    (profileCell_position_lt_terminal hTerminal hk hj)

/--
一つの occupied canonical cell の exact full odd-scale law。
-/
theorem threePow_mul_profileSignedCellCost_eq_gap_mul_quotient_add_term
    {H m k j : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1)
    (hk : k < m)
    (hj : j < beattyIndex k) :
    (3 : ℤ) ^ m * profileSignedCellCost H m k j =
      (columnLayerGap H m : ℤ) *
          profileCellScaledQuotient H m k j +
        (profileDyadicCellTerm m k j : ℤ) := by
  let i := columnLayerPosition k j
  let d := profileCellTailDepth H k j
  let a := k + 1
  let r := m - (k + 1)
  let u := profileCellLocalInverse H k j
  let q := profileCellLocalQuotient H k j
  have hiLt : i < H := by
    simpa [i] using profileCell_position_lt_terminal hTerminal hk hj
  have hiLe : i ≤ H := Nat.le_of_lt hiLt
  have hdPos : 0 < d := by
    simpa [d] using profileCellTailDepth_pos hTerminal hk hj
  have haLe : a ≤ m := by
    dsimp [a]
    omega
  have hHsplit : H = i + d := by
    dsimp [d, profileCellTailDepth]
    omega
  have hMsplit : m = a + r := by
    dsimp [a, r]
    omega
  have hULt : u < 2 ^ d := by
    simpa [u, d] using
      profileCellLocalInverse_lt
        (H := H) (k := k) (j := j)
  have hULe : u ≤ 2 ^ d := Nat.le_of_lt hULt
  have hLocalNat :
      3 ^ a * u = 1 + 2 ^ d * q := by
    simpa [a, u, q, d] using
      threePow_mul_profileCellLocalInverse_eq_one_add
        (H := H) (k := k) (j := j)
        (by simpa [d] using hdPos)
  have hLocalInt :
      (3 : ℤ) ^ a * (u : ℤ) =
        1 + (2 : ℤ) ^ d * (q : ℤ) := by
    exact_mod_cast hLocalNat
  have hContract : 3 ^ m < 2 ^ H := by
    unfold columnLayerGap at hGap
    exact Nat.sub_pos_iff_lt.mp hGap
  have hGapCast :
      (columnLayerGap H m : ℤ) =
        (2 : ℤ) ^ H - (3 : ℤ) ^ m := by
    unfold columnLayerGap
    rw [Nat.cast_sub (Nat.le_of_lt hContract)]
    push_cast
    rfl
  have hResidue :
      columnLayerFareyResidue H m k j =
        (2 : ℤ) ^ i * ((2 : ℤ) ^ d - (u : ℤ)) -
          (3 : ℤ) ^ r * ((3 : ℤ) ^ a - (q : ℤ)) := by
    unfold columnLayerFareyResidue columnLayerLeftExponent
    unfold ferrersCellResidueWeight
    dsimp [i, d, a, r, u, q,
      profileCellTailDepth, profileCellLocalInverse,
      profileCellLocalQuotient]
    rw [Nat.cast_sub]
    · push_cast
      rfl
    · change u ≤ 2 ^ d
      exact hULe
  have hTerm :
      (profileDyadicCellTerm m k j : ℤ) =
        (2 : ℤ) ^ i * (3 : ℤ) ^ r := by
    have h :=
      columnLayerScaledPowerTerm_eq_profileDyadicCellTerm_cast m k j
    rw [← h]
    unfold columnLayerScaledPowerTerm
    rfl
  have hTwoPowSplit :
      (2 : ℤ) ^ H =
        (2 : ℤ) ^ i * (2 : ℤ) ^ d := by
    calc
      (2 : ℤ) ^ H =
          (2 : ℤ) ^ (i + d) := by
            exact congrArg (fun n : ℕ => (2 : ℤ) ^ n) hHsplit
      _ =
          (2 : ℤ) ^ i * (2 : ℤ) ^ d := by
            exact pow_add (2 : ℤ) i d
  have hThreePowSplit :
      (3 : ℤ) ^ m =
        (3 : ℤ) ^ a * (3 : ℤ) ^ r := by
    calc
      (3 : ℤ) ^ m =
          (3 : ℤ) ^ (a + r) := by
            exact congrArg (fun n : ℕ => (3 : ℤ) ^ n) hMsplit
      _ =
          (3 : ℤ) ^ a * (3 : ℤ) ^ r := by
            exact pow_add (3 : ℤ) a r
  unfold profileSignedCellCost profileCellScaledQuotient
  rw [hGapCast, hResidue, hTerm]
  change
    (3 : ℤ) ^ m *
        (((2 : ℤ) ^ H - (3 : ℤ) ^ m) -
          ((2 : ℤ) ^ i * ((2 : ℤ) ^ d - (u : ℤ)) -
            (3 : ℤ) ^ r * ((3 : ℤ) ^ a - (q : ℤ)))) =
      ((2 : ℤ) ^ H - (3 : ℤ) ^ m) *
          ((q : ℤ) * (3 : ℤ) ^ r) +
        (2 : ℤ) ^ i * (3 : ℤ) ^ r
  rw [hTwoPowSplit, hThreePowSplit]
  calc
    _ =
        (2 : ℤ) ^ i * (3 : ℤ) ^ r *
            ((3 : ℤ) ^ a * (u : ℤ)) -
          ((3 : ℤ) ^ a * (3 : ℤ) ^ r) *
            ((q : ℤ) * (3 : ℤ) ^ r) := by
      ring
    _ =
        (2 : ℤ) ^ i * (3 : ℤ) ^ r *
            (1 + (2 : ℤ) ^ d * (q : ℤ)) -
          ((3 : ℤ) ^ a * (3 : ℤ) ^ r) *
            ((q : ℤ) * (3 : ℤ) ^ r) := by
      rw [hLocalInt]
    _ =
        ((2 : ℤ) ^ i * (2 : ℤ) ^ d -
            (3 : ℤ) ^ a * (3 : ℤ) ^ r) *
          ((q : ℤ) * (3 : ℤ) ^ r) +
        (2 : ℤ) ^ i * (3 : ℤ) ^ r := by
      ring

/-- occupied canonical cell cost は strict positive。 -/
theorem profileSignedCellCost_pos
    {H m k j : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1)
    (hk : k < m)
    (hj : j < beattyIndex k) :
    0 < profileSignedCellCost H m k j := by
  have hEq :=
    threePow_mul_profileSignedCellCost_eq_gap_mul_quotient_add_term
      hGap hTerminal hk hj
  have hGapZ : 0 < (columnLayerGap H m : ℤ) := by
    exact_mod_cast hGap
  have hQ : 0 ≤ profileCellScaledQuotient H m k j := by
    unfold profileCellScaledQuotient
    positivity
  have hGQ :
      0 ≤ (columnLayerGap H m : ℤ) *
        profileCellScaledQuotient H m k j :=
    mul_nonneg (le_of_lt hGapZ) hQ
  have hTerm : 0 < (profileDyadicCellTerm m k j : ℤ) := by
    rw [← columnLayerScaledPowerTerm_eq_profileDyadicCellTerm_cast m k j]
    unfold columnLayerScaledPowerTerm
    positivity
  have hRhs :
      0 < (columnLayerGap H m : ℤ) *
          profileCellScaledQuotient H m k j +
        (profileDyadicCellTerm m k j : ℤ) :=
    add_pos_of_nonneg_of_pos hGQ hTerm
  have hPow : 0 < (3 : ℤ) ^ m := by positivity
  nlinarith

/-- signed cost は existing natural canonical cell cost の cast と一致する。 -/
theorem profileSignedCellCost_eq_columnLayerCellCostNat_cast
    {H m k j : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1)
    (hk : k < m)
    (hj : j < beattyIndex k) :
    profileSignedCellCost H m k j =
      (columnLayerCellCostNat H m k j : ℤ) := by
  have hPos := profileSignedCellCost_pos hGap hTerminal hk hj
  unfold profileSignedCellCost columnLayerCellCostNat
  exact (Int.toNat_of_nonneg (le_of_lt hPos)).symm

/-! ## 3. fixed-layer interval cost blocks -/

/-- interval `[a,b)` の signed cell-cost sum。 -/
def profileIntervalSignedCost
    (H m j a b : ℕ) : ℤ :=
  Finset.sum (Finset.Ico a b)
    (fun k => profileSignedCellCost H m k j)

/-- interval `[a,b)` の full-scale local quotient sum。 -/
def profileIntervalScaledQuotient
    (H m j a b : ℕ) : ℤ :=
  Finset.sum (Finset.Ico a b)
    (fun k => profileCellScaledQuotient H m k j)

/-- interval numerator form の exact cost block equation。 -/
theorem threePow_mul_profileIntervalSignedCost_eq_gap_mul_quotient_add_numerator
    {H m j a b : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1)
    (hbm : b ≤ m)
    (hj : j < beattyIndex a) :
    (3 : ℤ) ^ m * profileIntervalSignedCost H m j a b =
      (columnLayerGap H m : ℤ) *
          profileIntervalScaledQuotient H m j a b +
        (profileDyadicIntervalNumerator m j a b : ℤ) := by
  classical
  have hCell :
      ∀ k ∈ Finset.Ico a b,
        (3 : ℤ) ^ m * profileSignedCellCost H m k j =
          (columnLayerGap H m : ℤ) *
              profileCellScaledQuotient H m k j +
            (profileDyadicCellTerm m k j : ℤ) := by
    intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    have hkLtM : k < m := lt_of_lt_of_le hkIco.2 hbm
    have hBeta : beattyIndex a ≤ beattyIndex k := by
      by_cases hEq : a = k
      · subst k
        exact le_rfl
      · exact le_of_lt (beattyIndex_strictMono (by omega))
    have hjk : j < beattyIndex k := lt_of_lt_of_le hj hBeta
    exact
      threePow_mul_profileSignedCellCost_eq_gap_mul_quotient_add_term
        hGap hTerminal hkLtM hjk
  have hTermCast :
      Finset.sum (Finset.Ico a b)
          (fun k => (profileDyadicCellTerm m k j : ℤ)) =
        (profileDyadicIntervalNumerator m j a b : ℤ) := by
    unfold profileDyadicIntervalNumerator
    push_cast
    rfl
  unfold profileIntervalSignedCost profileIntervalScaledQuotient
  rw [Finset.mul_sum]
  calc
    Finset.sum (Finset.Ico a b)
        (fun k => (3 : ℤ) ^ m * profileSignedCellCost H m k j)
        =
      Finset.sum (Finset.Ico a b)
        (fun k =>
          (columnLayerGap H m : ℤ) *
              profileCellScaledQuotient H m k j +
            (profileDyadicCellTerm m k j : ℤ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hCell k hk
    _ =
      (columnLayerGap H m : ℤ) *
          Finset.sum (Finset.Ico a b)
            (fun k => profileCellScaledQuotient H m k j) +
        Finset.sum (Finset.Ico a b)
          (fun k => (profileDyadicCellTerm m k j : ℤ)) := by
            rw [Finset.sum_add_distrib]
            rw [Finset.mul_sum]
    _ =
      (columnLayerGap H m : ℤ) *
          Finset.sum (Finset.Ico a b)
            (fun k => profileCellScaledQuotient H m k j) +
        (profileDyadicIntervalNumerator m j a b : ℤ) := by
          rw [hTermCast]

/-- interval factor `W_I = 2^(beta_a-j-1) 3^(m-b)`。 -/
def profileIntervalScaleZ
    (m j a b : ℕ) : ℤ :=
  (2 : ℤ) ^ (beattyIndex a - j - 1) *
    (3 : ℤ) ^ (m - b)

/-- interval equation を `W_I * Phi[a,b]` まで factor した形。 -/
theorem threePow_mul_profileIntervalSignedCost_eq_gap_mul_quotient_add_scaledPhi
    {H m j a b : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1)
    (hbm : b ≤ m)
    (hj : j < beattyIndex a) :
    (3 : ℤ) ^ m * profileIntervalSignedCost H m j a b =
      (columnLayerGap H m : ℤ) *
          profileIntervalScaledQuotient H m j a b +
        profileIntervalScaleZ m j a b *
          criticalIntervalPhiZ a b := by
  have hBase :=
    threePow_mul_profileIntervalSignedCost_eq_gap_mul_quotient_add_numerator
      hGap hTerminal hbm hj
  have hNat :=
    profileDyadicIntervalNumerator_eq_scaledCriticalIntervalPhi
      (m := m) (j := j) (a := a) (b := b) hbm hj
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hZ
  rw [criticalIntervalPhi_cast_eq] at hZ
  unfold profileIntervalScaleZ
  rw [hZ] at hBase
  exact hBase

/-! ## 4. interval gap term = endpoint boundary difference -/

/-- layer `j` における endpoint boundary monomial。 -/
def profileLayerBoundaryTermZ
    (m j n : ℕ) : ℤ :=
  (2 : ℤ) ^ (beattyIndex n - j - 1) *
    (3 : ℤ) ^ (m - n)

/--
interval scale times power gap は exact に right-left boundary difference。
-/
theorem profileIntervalScaleZ_mul_criticalIntervalGapZ_eq_boundary_sub
    {m j a b : ℕ}
    (hab : a ≤ b)
    (hbm : b ≤ m)
    (hj : j < beattyIndex a) :
    profileIntervalScaleZ m j a b * criticalIntervalGapZ a b =
      profileLayerBoundaryTermZ m j b -
        profileLayerBoundaryTermZ m j a := by
  have hBeta : beattyIndex a ≤ beattyIndex b := by
    by_cases hEq : a = b
    · subst b
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hTwoExp :
      beattyIndex b - j - 1 =
        (beattyIndex a - j - 1) +
          (beattyIndex b - beattyIndex a) := by
    omega
  have hThreeExp :
      m - a = (m - b) + (b - a) := by
    omega
  unfold profileIntervalScaleZ profileLayerBoundaryTermZ
    criticalIntervalGapZ
  rw [hTwoExp, hThreeExp, pow_add, pow_add]
  ring

/--
scaled interval numerator を interior defect + endpoint boundary terms に分離する。
-/
theorem profileIntervalScaleZ_mul_phi_eq_defect_add_boundary
    {m j a b : ℕ}
    (hab : a ≤ b)
    (hbm : b ≤ m)
    (hj : j < beattyIndex a)
    (y : ℤ) :
    profileIntervalScaleZ m j a b * criticalIntervalPhiZ a b =
      profileIntervalScaleZ m j a b *
          criticalIntervalDefectZ a b y +
        (profileLayerBoundaryTermZ m j b -
          profileLayerBoundaryTermZ m j a) * y := by
  have hGap :=
    profileIntervalScaleZ_mul_criticalIntervalGapZ_eq_boundary_sub
      hab hbm hj
  unfold criticalIntervalDefectZ
  rw [← hGap]
  ring

/-- cost block の final interior/boundary normal form。 -/
theorem threePow_mul_profileIntervalSignedCost_eq_defectBlock_add_boundary
    {H m j a b : ℕ}
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1)
    (hab : a ≤ b)
    (hbm : b ≤ m)
    (hj : j < beattyIndex a)
    (y : ℤ) :
    (3 : ℤ) ^ m * profileIntervalSignedCost H m j a b =
      (columnLayerGap H m : ℤ) *
          profileIntervalScaledQuotient H m j a b +
        profileIntervalScaleZ m j a b *
          criticalIntervalDefectZ a b y +
        (profileLayerBoundaryTermZ m j b -
          profileLayerBoundaryTermZ m j a) * y := by
  have hBlock :=
    threePow_mul_profileIntervalSignedCost_eq_gap_mul_quotient_add_scaledPhi
      hGap hTerminal hbm hj
  have hSplit :=
    profileIntervalScaleZ_mul_phi_eq_defect_add_boundary
      hab hbm hj y
  rw [hSplit] at hBlock
  linarith

/-! ## 5. maximal profile intervals inherit the cost-block law -/

namespace PureBProfileObstruction

/-- maximal layer interval の exact `G*T + W*Phi` cost block。 -/
theorem maximalInterval_costBlock_scaledPhi
    (P : PureBProfileObstruction)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals P.m P.h j) :
    (3 : ℤ) ^ P.m *
        profileIntervalSignedCost P.H P.m j ab.1 ab.2 =
      (P.gap : ℤ) *
          profileIntervalScaledQuotient P.H P.m j ab.1 ab.2 +
        profileIntervalScaleZ P.m j ab.1 ab.2 *
          criticalIntervalPhiZ ab.1 ab.2 := by
  have hGeom := P.maximalInterval_geometry hab
  have hj := P.maximalInterval_layer_lt_leftBeatty hab
  have h :=
    threePow_mul_profileIntervalSignedCost_eq_gap_mul_quotient_add_scaledPhi
      P.gap_pos P.terminal_beatty hGeom.2.1 hj
  simpa [PureBProfileObstruction.gap] using h

/-- maximal layer interval の interior defect + exposed endpoint form。 -/
theorem maximalInterval_costBlock_defect_boundary
    (P : PureBProfileObstruction)
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals P.m P.h j) :
    (3 : ℤ) ^ P.m *
        profileIntervalSignedCost P.H P.m j ab.1 ab.2 =
      (P.gap : ℤ) *
          profileIntervalScaledQuotient P.H P.m j ab.1 ab.2 +
        profileIntervalScaleZ P.m j ab.1 ab.2 *
          criticalIntervalDefectZ ab.1 ab.2 P.y +
        (profileLayerBoundaryTermZ P.m j ab.2 -
          profileLayerBoundaryTermZ P.m j ab.1) * P.y := by
  have hGeom := P.maximalInterval_geometry hab
  have hj := P.maximalInterval_layer_lt_leftBeatty hab
  have h :=
    threePow_mul_profileIntervalSignedCost_eq_defectBlock_add_boundary
      P.gap_pos P.terminal_beatty
      (Nat.le_of_lt hGeom.1) hGeom.2.1 hj P.y
  simpa [PureBProfileObstruction.gap] using h

end PureBProfileObstruction

/-! ## 6. full profile positive-cost normal form -/

/-- 全 occupied profile cells の signed cost sum。 -/
def profileSignedCostSum
    (H m : ℕ)
    (h : ℕ → ℕ) : ℤ :=
  columnProfileSum m h
    (fun k j => profileSignedCellCost H m k j)

/-- 全 occupied profile cells の full-scale quotient sum。 -/
def profileScaledQuotientSum
    (H m : ℕ)
    (h : ℕ → ℕ) : ℤ :=
  columnProfileSum m h
    (fun k j => profileCellScaledQuotient H m k j)

/--
全 profile cell exact law。

  3^m C(h) = G T(h) + N(h).
-/
theorem threePow_mul_profileSignedCostSum_eq_gap_mul_quotientSum_add_numerator
    {H m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    (hGap : 0 < columnLayerGap H m)
    (hTerminal : H = beattyIndex m + 1) :
    (3 : ℤ) ^ m * profileSignedCostSum H m h =
      (columnLayerGap H m : ℤ) *
          profileScaledQuotientSum H m h +
        (profileDyadicCellNumerator m h : ℤ) := by
  classical
  have hTermCast :
      Finset.sum (Finset.range m)
          (fun k =>
            Finset.sum (Finset.range (h k))
              (fun j => (profileDyadicCellTerm m k j : ℤ))) =
        (profileDyadicCellNumerator m h : ℤ) := by
    unfold profileDyadicCellNumerator columnProfileSum
    push_cast
    rfl
  unfold profileSignedCostSum profileScaledQuotientSum columnProfileSum
  rw [Finset.mul_sum]
  calc
    Finset.sum (Finset.range m)
        (fun k =>
          (3 : ℤ) ^ m *
            Finset.sum (Finset.range (h k))
              (fun j => profileSignedCellCost H m k j))
        =
      Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range (h k))
            (fun j =>
              (3 : ℤ) ^ m * profileSignedCellCost H m k j)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
    _ =
      Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range (h k))
            (fun j =>
              (columnLayerGap H m : ℤ) *
                  profileCellScaledQuotient H m k j +
                (profileDyadicCellTerm m k j : ℤ))) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkLt : k < m := Finset.mem_range.mp hk
          apply Finset.sum_congr rfl
          intro j hjMem
          have hjLt : j < h k := Finset.mem_range.mp hjMem
          have hjBeta : j < beattyIndex k :=
            lt_of_lt_of_le hjLt (A.depth_le hkLt)
          exact
            threePow_mul_profileSignedCellCost_eq_gap_mul_quotient_add_term
              hGap hTerminal hkLt hjBeta
    _ =
      Finset.sum (Finset.range m)
          (fun k =>
            (columnLayerGap H m : ℤ) *
                Finset.sum (Finset.range (h k))
                  (fun j => profileCellScaledQuotient H m k j) +
              Finset.sum (Finset.range (h k))
                (fun j => (profileDyadicCellTerm m k j : ℤ))) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_add_distrib]
          rw [Finset.mul_sum]
    _ =
      (columnLayerGap H m : ℤ) *
          Finset.sum (Finset.range m)
            (fun k =>
              Finset.sum (Finset.range (h k))
                (fun j => profileCellScaledQuotient H m k j)) +
        Finset.sum (Finset.range m)
          (fun k =>
            Finset.sum (Finset.range (h k))
              (fun j => (profileDyadicCellTerm m k j : ℤ))) := by
          rw [Finset.sum_add_distrib]
          rw [Finset.mul_sum]
    _ =
      (columnLayerGap H m : ℤ) *
          Finset.sum (Finset.range m)
            (fun k =>
              Finset.sum (Finset.range (h k))
                (fun j => profileCellScaledQuotient H m k j)) +
        (profileDyadicCellNumerator m h : ℤ) := by
          rw [hTermCast]

namespace PureBProfileObstruction

/--
pure B deep equation と full positive-cost equation を合成した normal form。

  Psi(m) - G (y - T(h)) = 3^m (q + C(h)).
-/
theorem criticalPrefixPhiZ_cost_normal_form
    (P : PureBProfileObstruction) :
    criticalPrefixPhiZ P.m -
        (P.gap : ℤ) *
          (P.y - profileScaledQuotientSum P.H P.m P.h) =
      (3 : ℤ) ^ P.m *
        ((P.q : ℤ) + profileSignedCostSum P.H P.m P.h) := by
  have hCost :=
    threePow_mul_profileSignedCostSum_eq_gap_mul_quotientSum_add_numerator
      P.admissible P.gap_pos P.terminal_beatty
  unfold PureBProfileObstruction.gap at hCost ⊢
  linear_combination P.deep_profile_defect - hCost

/-- full profile signed cost sum は nonnegative。 -/
theorem profileSignedCostSum_nonneg
    (P : PureBProfileObstruction) :
    0 ≤ profileSignedCostSum P.H P.m P.h := by
  classical
  unfold profileSignedCostSum columnProfileSum
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro j hj
  have hkLt : k < P.m := Finset.mem_range.mp hk
  have hjLt : j < P.h k := Finset.mem_range.mp hj
  have hjBeta : j < beattyIndex k :=
    lt_of_lt_of_le hjLt (P.admissible.depth_le hkLt)
  exact le_of_lt
    (profileSignedCellCost_pos
      P.gap_pos P.terminal_beatty hkLt hjBeta)

/-- positive-cost normal form の right quotient は元の tiny q 以上。 -/
theorem q_le_q_add_profileSignedCostSum
    (P : PureBProfileObstruction) :
    (P.q : ℤ) ≤
      (P.q : ℤ) + profileSignedCostSum P.H P.m P.h := by
  linarith [P.profileSignedCostSum_nonneg]

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
