import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.IrrationalRotationRoof
import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridor
import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalGreedy
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: 任意回転の canonical Ostrowski 座標

第12段階では、任意の無理回転 `α ∈ (0,1)` から

`β_α(n) = n + floor(n α)`

という標準 lifted roof を構成し、その phase が `fract(n α)` と exact に一致することを示した。

このファイルでは、同じ `α` に対する Ostrowski 座標を Collatz 固有定数から切り離す。

直接 `α` の continued fraction engine を再実装するのではなく、lifted slope

`σ = 1 + α`

を上下から交互に挟む shifted convergent certificate だけを
`RotationOstrowskiSystem α` に保存する。

重要な点は horizontal weight の最初の扱いである。
任意の `α` では最初の partial quotient `a₀` は `1` とは限らない。
そこで

* `a₀ = 1` なら重複する `P₀=P₁=1` を一つ落として `P₁,P₂,...`、
* `a₀ > 1` なら `P₀,P₁,...` をそのまま使い、最初の digit bound だけ `a₀-1`

とする。

この二分岐を既存 `UnitOstrowskiWeightSystem` へ正規化することで、
canonical greedy digits・再構成・一意性を再実装せず再利用する。

最終的に任意の自然数 `N` について

`N α = integer(N) + error(N)`

という exact canonical Ostrowski decomposition と

`fract(N α) = fract(error(N))`

を得る。第12段階の phase theorem と合わせると、
`irrationalRotationRoof α` の mechanical phase は canonical Ostrowski error の fractional part だけで読める。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
回転 `α` の shifted regular-convergent certificate。

`conv.P/conv.Q` は inverse lifted slope `1/(1+α)` 側の convergent と考え、
同値な direct-slope 表現 `conv.Q/conv.P` が `1+α` を上下から交互に挟むことだけを保存する。

continued fraction の生成アルゴリズム自体は primitive data に含めない。
-/
structure RotationOstrowskiSystem (α : ℝ) where
  conv : UnitOstrowskiConvergentSystem
  lowerBracket : ∀ n, n % 2 = 0 →
    IsLowerFareyBracket (1 + α)
      (conv.P n) (conv.Q n) (conv.P (n + 1)) (conv.Q (n + 1))
  upperBracket : ∀ n, n % 2 = 1 →
    IsUpperFareyBracket (1 + α)
      (conv.P n) (conv.Q n) (conv.P (n + 1)) (conv.Q (n + 1))

namespace RotationOstrowskiSystem

/--
最初の partial quotient が `1` の場合に、重複した先頭 `P₀=P₁=1` を落とした weight system。
-/
private def shiftedHorizontalWeights
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (hOne : D.conv.a 0 = 1) :
    UnitOstrowskiWeightSystem where
  a n := D.conv.a (n + 1)
  Q n := D.conv.P (n + 1)
  a_pos n := D.conv.a_pos (n + 1)
  q_zero := by
    rw [D.conv.p_one, hOne]
  q_one := by
    rw [D.conv.p_rec 0, D.conv.p_one, D.conv.p_zero, hOne]
    simp
  q_rec n := by
    simpa [Nat.add_assoc] using D.conv.p_rec (n + 1)

/--
最初の partial quotient が `1` より大きい場合の horizontal weight system。

weight は `P₀,P₁,...` をそのまま使う。
既存 `UnitOstrowskiWeightSystem` の初期式 `Q₁=a₀+1` に合わせるため、
新しい最初の digit bound を元の `a₀-1` とする。
-/
private def unshiftedHorizontalWeights
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (hNotOne : D.conv.a 0 ≠ 1) :
    UnitOstrowskiWeightSystem where
  a
    | 0 => D.conv.a 0 - 1
    | n + 1 => D.conv.a (n + 1)
  Q n := D.conv.P n
  a_pos := by
    intro n
    cases n with
    | zero =>
        have hPos := D.conv.a_pos 0
        have hTwo : 2 ≤ D.conv.a 0 := by
          omega
        change 0 < D.conv.a 0 - 1
        omega
    | succ n =>
        exact D.conv.a_pos (n + 1)
  q_zero := by
    exact D.conv.p_zero
  q_one := by
    rw [D.conv.p_one]
    have hPos := D.conv.a_pos 0
    have hTwo : 2 ≤ D.conv.a 0 := by
      omega
    change D.conv.a 0 = (D.conv.a 0 - 1) + 1
    omega
  q_rec n := by
    simpa using D.conv.p_rec n

/--
任意回転に使う horizontal Ostrowski weight system。

`a₀=1` のときだけ一段 shift し、それ以外は先頭 digit bound を `a₀-1` に直す。
この normalization により既存 canonical greedy theory をそのまま利用できる。
-/
def horizontalWeights
    {α : ℝ}
    (D : RotationOstrowskiSystem α) :
    UnitOstrowskiWeightSystem :=
  if hOne : D.conv.a 0 = 1 then
    shiftedHorizontalWeights D hOne
  else
    unshiftedHorizontalWeights D hOne

/--
horizontal weight `n` が参照する元の convergent index。
-/
def horizontalIndex
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) : ℕ :=
  if D.conv.a 0 = 1 then n + 1 else n

/-- horizontal index は一段進めると必ず一つ増える。 -/
theorem horizontalIndex_succ
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) :
    D.horizontalIndex (n + 1) = D.horizontalIndex n + 1 := by
  by_cases hOne : D.conv.a 0 = 1
  · simp [horizontalIndex, hOne]
  · simp [horizontalIndex, hOne]

/-- horizontal weight は対応する convergent の `P` 座標そのもの。 -/
@[simp] theorem horizontalWeights_Q
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) :
    D.horizontalWeights.Q n = D.conv.P (D.horizontalIndex n) := by
  by_cases hOne : D.conv.a 0 = 1
  · simp [horizontalWeights, shiftedHorizontalWeights, horizontalIndex, hOne]
  · simp [horizontalWeights, unshiftedHorizontalWeights, horizontalIndex, hOne]

/-- 次の horizontal weight も次の convergent `P` 座標に一致する。 -/
@[simp] theorem horizontalWeights_Q_succ
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) :
    D.horizontalWeights.Q (n + 1) =
      D.conv.P (D.horizontalIndex n + 1) := by
  rw [D.horizontalWeights_Q, D.horizontalIndex_succ]

/-- horizontal canonical Ostrowski digits。 -/
def horizontalOstrowskiDigits
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) : ℕ → ℕ :=
  canonicalOstrowskiDigits D.horizontalWeights N

/-- horizontal canonical digits は元の自然数を exact に再構成する。 -/
theorem horizontalOstrowskiDigits_reconstruct
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    ostrowskiPrefixSum D.horizontalWeights.Q
        (D.horizontalOstrowskiDigits N) (N + 1) = N := by
  simpa [horizontalOstrowskiDigits] using
    canonicalOstrowskiDigits_reconstruct D.horizontalWeights N

/-- horizontal canonical digits は canonical normal form を満たす。 -/
theorem horizontalOstrowskiDigits_canonical
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    IsCanonicalOstrowskiDigits D.horizontalWeights
      (D.horizontalOstrowskiDigits N) := by
  simpa [horizontalOstrowskiDigits] using
    canonicalOstrowskiDigits_canonical D.horizontalWeights N

/--
一つの horizontal convergent weight に対応する整数近似。

`P_i * α ≈ Q_i - P_i`。
-/
def horizontalRotationInteger
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) : ℤ :=
  (D.conv.Q (D.horizontalIndex n) : ℤ) -
    (D.conv.P (D.horizontalIndex n) : ℤ)

/--
一つの horizontal convergent weightにおける pure rotation return error。
-/
noncomputable def horizontalRotationReturnError
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) : ℝ :=
  (D.horizontalWeights.Q n : ℝ) * α -
    (D.horizontalRotationInteger n : ℝ)

/--
rotation error は direct lifted slope `1+α` の convergent error と exact に同じ。
-/
theorem horizontalRotationReturnError_eq_directSlopeError
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) :
    D.horizontalRotationReturnError n =
      (D.conv.P (D.horizontalIndex n) : ℝ) * (1 + α) -
        (D.conv.Q (D.horizontalIndex n) : ℝ) := by
  unfold horizontalRotationReturnError horizontalRotationInteger
  rw [D.horizontalWeights_Q]
  push_cast
  ring

/--
Farey determinant `±1` により、basic horizontal rotation error は
次の horizontal weight の逆数より strict に小さい。
-/
theorem abs_horizontalRotationReturnError_lt_inv_nextWeight
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (n : ℕ) :
    |D.horizontalRotationReturnError n| <
      1 / (D.horizontalWeights.Q (n + 1) : ℝ) := by
  rw [D.horizontalRotationReturnError_eq_directSlopeError]
  rw [D.horizontalWeights_Q_succ]
  let i := D.horizontalIndex n
  have hmod : i % 2 = 0 ∨ i % 2 = 1 := by
    have hlt := Nat.mod_lt i (by omega : 0 < 2)
    omega
  rcases hmod with hEven | hOdd
  · rcases D.lowerBracket i hEven with
      ⟨hP, hPn, hCurrent, hNext, hDet⟩
    have hPR : (0 : ℝ) < (D.conv.P i : ℝ) := by
      exact_mod_cast hP
    have hPnR : (0 : ℝ) < (D.conv.P (i + 1) : ℝ) := by
      exact_mod_cast hPn
    have hCurrentMul :
        (D.conv.Q i : ℝ) <
          (1 + α) * (D.conv.P i : ℝ) :=
      (div_lt_iff₀ hPR).1 hCurrent
    have hNextMul :
        (1 + α) * (D.conv.P (i + 1) : ℝ) <
          (D.conv.Q (i + 1) : ℝ) :=
      (lt_div_iff₀ hPnR).1 hNext
    have hNextScaled :=
      mul_lt_mul_of_pos_left hNextMul hPR
    have hDetR :
        (D.conv.P (i + 1) : ℝ) * (D.conv.Q i : ℝ) + 1 =
          (D.conv.P i : ℝ) * (D.conv.Q (i + 1) : ℝ) := by
      exact_mod_cast hDet
    have hErrPos :
        0 < (D.conv.P i : ℝ) * (1 + α) -
          (D.conv.Q i : ℝ) := by
      nlinarith
    have hErrUpper :
        (D.conv.P i : ℝ) * (1 + α) -
            (D.conv.Q i : ℝ) <
          1 / (D.conv.P (i + 1) : ℝ) := by
      apply (lt_div_iff₀ hPnR).2
      nlinarith [hNextScaled, hDetR]
    change
      |(D.conv.P i : ℝ) * (1 + α) - (D.conv.Q i : ℝ)| <
        1 / (D.conv.P (i + 1) : ℝ)
    rw [abs_of_pos hErrPos]
    exact hErrUpper
  · rcases D.upperBracket i hOdd with
      ⟨hP, hPn, hNext, hCurrent, hDet⟩
    have hPR : (0 : ℝ) < (D.conv.P i : ℝ) := by
      exact_mod_cast hP
    have hPnR : (0 : ℝ) < (D.conv.P (i + 1) : ℝ) := by
      exact_mod_cast hPn
    have hCurrentMul :
        (1 + α) * (D.conv.P i : ℝ) <
          (D.conv.Q i : ℝ) :=
      (lt_div_iff₀ hPR).1 hCurrent
    have hNextMul :
        (D.conv.Q (i + 1) : ℝ) <
          (1 + α) * (D.conv.P (i + 1) : ℝ) :=
      (div_lt_iff₀ hPnR).1 hNext
    have hNextScaled :=
      mul_lt_mul_of_pos_left hNextMul hPR
    have hDetR :
        (D.conv.P i : ℝ) * (D.conv.Q (i + 1) : ℝ) + 1 =
          (D.conv.P (i + 1) : ℝ) * (D.conv.Q i : ℝ) := by
      exact_mod_cast hDet
    have hErrNeg :
        (D.conv.P i : ℝ) * (1 + α) -
          (D.conv.Q i : ℝ) < 0 := by
      nlinarith
    have hAbsUpper :
        (D.conv.Q i : ℝ) -
            (D.conv.P i : ℝ) * (1 + α) <
          1 / (D.conv.P (i + 1) : ℝ) := by
      apply (lt_div_iff₀ hPnR).2
      nlinarith [hNextScaled, hDetR]
    change
      |(D.conv.P i : ℝ) * (1 + α) - (D.conv.Q i : ℝ)| <
        1 / (D.conv.P (i + 1) : ℝ)
    rw [abs_of_neg hErrNeg]
    nlinarith

/-- 任意 digit prefix の整数部分。 -/
def rotationIntegerPrefix
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (d : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      rotationIntegerPrefix D d n +
        (d n : ℤ) * D.horizontalRotationInteger n

/-- 任意 digit prefix の composite rotation error。 -/
noncomputable def rotationErrorPrefix
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (d : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      rotationErrorPrefix D d n +
        (d n : ℝ) * D.horizontalRotationReturnError n

/-- basic error bound を digit-weighted に足し上げた安全な上界。 -/
noncomputable def rotationErrorCapPrefix
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (d : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      rotationErrorCapPrefix D d n +
        (d n : ℝ) / (D.horizontalWeights.Q (n + 1) : ℝ)

/--
任意 finite digit prefix の exact rotation decomposition。

canonicality は不要で、weighted sum の再帰だけを使う。
-/
theorem rotationPrefix_decomposition
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (d : ℕ → ℕ) :
    ∀ t : ℕ,
      (ostrowskiPrefixSum D.horizontalWeights.Q d t : ℝ) * α =
        ((D.rotationIntegerPrefix d t : ℤ) : ℝ) +
          D.rotationErrorPrefix d t := by
  intro t
  induction t with
  | zero =>
      simp [rotationIntegerPrefix, rotationErrorPrefix]
  | succ n ih =>
      have hAtom :
          (D.horizontalWeights.Q n : ℝ) * α =
            ((D.horizontalRotationInteger n : ℤ) : ℝ) +
              D.horizontalRotationReturnError n := by
        unfold horizontalRotationReturnError
        ring
      rw [ostrowskiPrefixSum_succ]
      rw [rotationIntegerPrefix, rotationErrorPrefix]
      push_cast
      rw [add_mul]
      rw [ih]
      calc
        _ =
            (↑(D.rotationIntegerPrefix d n) +
              D.rotationErrorPrefix d n) +
            (d n : ℝ) *
              ((D.horizontalWeights.Q n : ℝ) * α) := by
          ring
        _ = _ := by
          rw [hAtom]
          ring

/-- arbitrary digit prefix の composite error は cap 以下。 -/
theorem abs_rotationErrorPrefix_le_cap
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (d : ℕ → ℕ) :
    ∀ t : ℕ,
      |D.rotationErrorPrefix d t| ≤
        D.rotationErrorCapPrefix d t := by
  intro t
  induction t with
  | zero =>
      simp [rotationErrorPrefix, rotationErrorCapPrefix]
  | succ n ih =>
      have hErr :
          |D.horizontalRotationReturnError n| ≤
            1 / (D.horizontalWeights.Q (n + 1) : ℝ) :=
        le_of_lt (D.abs_horizontalRotationReturnError_lt_inv_nextWeight n)
      have hd : (0 : ℝ) ≤ (d n : ℝ) := by positivity
      have hTerm :
          |(d n : ℝ) * D.horizontalRotationReturnError n| ≤
            (d n : ℝ) /
              (D.horizontalWeights.Q (n + 1) : ℝ) := by
        rw [abs_mul, abs_of_nonneg hd]
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hErr hd
      rw [rotationErrorPrefix, rotationErrorCapPrefix]
      calc
        |D.rotationErrorPrefix d n +
            (d n : ℝ) * D.horizontalRotationReturnError n|
            ≤ |D.rotationErrorPrefix d n| +
                |(d n : ℝ) * D.horizontalRotationReturnError n| :=
          abs_add_le _ _
        _ ≤ D.rotationErrorCapPrefix d n +
              (d n : ℝ) /
                (D.horizontalWeights.Q (n + 1) : ℝ) :=
          add_le_add ih hTerm

/-- canonical decomposition の整数部分。 -/
def rotationBlockInteger
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) : ℤ :=
  D.rotationIntegerPrefix (D.horizontalOstrowskiDigits N) (N + 1)

/-- canonical decomposition の composite error。 -/
noncomputable def rotationBlockError
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) : ℝ :=
  D.rotationErrorPrefix (D.horizontalOstrowskiDigits N) (N + 1)

/-- canonical composite error の安全な上界。 -/
noncomputable def rotationBlockErrorCap
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) : ℝ :=
  D.rotationErrorCapPrefix (D.horizontalOstrowskiDigits N) (N + 1)

/--
任意自然数 `N` の canonical Ostrowski decomposition による exact rotation law。
-/
theorem rotationBlock_decomposition
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    (N : ℝ) * α =
      ((D.rotationBlockInteger N : ℤ) : ℝ) +
        D.rotationBlockError N := by
  have h :=
    D.rotationPrefix_decomposition (D.horizontalOstrowskiDigits N) (N + 1)
  rw [D.horizontalOstrowskiDigits_reconstruct N] at h
  simpa [rotationBlockInteger, rotationBlockError] using h

/--
canonical block の pure rotation fractional part は composite Ostrowski error だけで決まる。
-/
theorem fract_mul_rotation_eq_fract_blockError
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    Int.fract ((N : ℝ) * α) =
      Int.fract (D.rotationBlockError N) := by
  rw [D.rotationBlock_decomposition N]
  calc
    Int.fract
        (((D.rotationBlockInteger N : ℤ) : ℝ) +
          D.rotationBlockError N) =
      Int.fract
        (D.rotationBlockError N +
          ((D.rotationBlockInteger N : ℤ) : ℝ)) := by
        rw [add_comm]
    _ = Int.fract (D.rotationBlockError N) := by
      rw [Int.fract_add_intCast]

/-- canonical block composite error の absolute bound。 -/
theorem abs_rotationBlockError_le_cap
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    |D.rotationBlockError N| ≤ D.rotationBlockErrorCap N := by
  simpa [rotationBlockError, rotationBlockErrorCap] using
    D.abs_rotationErrorPrefix_le_cap
      (D.horizontalOstrowskiDigits N) (N + 1)

/--
第12段階の irrational rotation roof phase を canonical Ostrowski error だけで読む exact dictionary。
-/
theorem irrationalRotationRoof_phase_eq_fract_rotationBlockError
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (N : ℕ) :
    roofPhase (irrationalRotationRoof α) (1 + α) N =
      Int.fract (D.rotationBlockError N) := by
  rw [irrationalRotationRoof_phase_eq_fract A.nonneg N]
  exact D.fract_mul_rotation_eq_fract_blockError N

end RotationOstrowskiSystem

end GenericRecordFerrers
end Experimental2
end Collatz3
