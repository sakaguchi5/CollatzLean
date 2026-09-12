import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordRankFerrersShape
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RotationOstrowskiExistence
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: Ostrowski 桁と rank-envelope Ferrers / Young 図形の exact bridge

前段までで二つの側が独立に閉じた。

* 任意の無理回転 `α ∈ (0,1)` は canonical な `RotationOstrowskiSystem α` を持ち、
  任意の自然数 `N` は horizontal canonical Ostrowski digits から exact に復元できる。
* 完成 `RecordFerrers` の `canonicalRecordLengths` は rank-envelope Ferrers shape の
  水平 block 長を与え、各 block の縦落差は `rankDropInt` で exact に決まる。

このファイルでは両者を直接接続する。

中心となる等式は、canonical Ostrowski decomposition

`N α = rotationBlockInteger(N) + rotationBlockError(N)`

から得られる

`floor(N α) = rotationBlockInteger(N) + floor(rotationBlockError(N))`

である。これを `irrationalRotationRoof α` の critical depth に代入すると、
幅 `r` の block の rank drop は同じ horizontal Ostrowski digits だけから計算できる。

従って、各 canonical block について

* 横幅 `r` は horizontal Ostrowski weighted sum、
* 縦落差は同じ digits の rotation integer / error、

という exact dictionary が得られる。
最後にこの Ostrowski drop から直接 Ferrers shape を作り、前段の
`RecordFerrers.rankFerrersShape` と exact に一致することを証明する。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RotationOstrowskiSystem

/--
canonical horizontal Ostrowski decomposition から `floor(N α)` を exact に読む。
整数部分はそのまま、残りは composite rotation error の floor になる。
-/
theorem floor_mul_rotation_eq_blockInteger_add_floor_error
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    ⌊(N : ℝ) * α⌋ =
      D.rotationBlockInteger N + ⌊D.rotationBlockError N⌋ := by
  rw [D.rotationBlock_decomposition N]
  exact Int.floor_intCast_add _ _

/--
`irrationalRotationRoof α` の critical depth を horizontal canonical Ostrowski data だけで読む。

`criticalDepth β N = β N + 1` と
`β(N)=N+floor(N α)` を上の floor 分解へ代入した形である。
-/
theorem criticalDepth_irrationalRotationRoof_cast_eq_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (N : ℕ) :
    (criticalDepth (irrationalRotationRoof α) N : ℤ) =
      (N : ℤ) + D.rotationBlockInteger N +
        ⌊D.rotationBlockError N⌋ + 1 := by
  unfold criticalDepth
  rw [irrationalRotationRoof_eq]
  have hx : 0 ≤ (N : ℝ) * α :=
    mul_nonneg (Nat.cast_nonneg N) A.nonneg
  have hNatFloor :
      ((⌊(N : ℝ) * α⌋₊ : ℕ) : ℤ) =
        ⌊(N : ℝ) * α⌋ :=
    Int.natCast_floor_eq_floor hx
  push_cast
  rw [hNatFloor, D.floor_mul_rotation_eq_blockInteger_add_floor_error N]
  ring

/--
Ostrowski 側だけで書いた、幅 `m`・block 長 `r` の rank drop。

`rotationBlockInteger` と `rotationBlockError` はともに
`horizontalOstrowskiDigits` から構成されるため、この量は horizontal Ostrowski code だけで決まる。
-/
noncomputable def ostrowskiRankDropInt
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m r : ℕ) : ℤ :=
  (m : ℤ) *
      (D.rotationBlockInteger r + ⌊D.rotationBlockError r⌋ + 1) -
    (r : ℤ) *
      (D.rotationBlockInteger m + ⌊D.rotationBlockError m⌋ + 1)

/-- Ostrowski rank drop の自然数表示。 -/
noncomputable def ostrowskiRankDropNat
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m r : ℕ) : ℕ :=
  (D.ostrowskiRankDropInt m r).toNat

/--
`ostrowskiRankDropInt` を primitive な digit-prefix data まで展開した形。
横幅 `r` と全体幅 `m` の双方で、同じ horizontal canonical digits を用いる。
-/
theorem ostrowskiRankDropInt_eq_digitFormula
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m r : ℕ) :
    D.ostrowskiRankDropInt m r =
      (m : ℤ) *
        (D.rotationIntegerPrefix (D.horizontalOstrowskiDigits r) (r + 1) +
          ⌊D.rotationErrorPrefix (D.horizontalOstrowskiDigits r) (r + 1)⌋ + 1) -
      (r : ℤ) *
        (D.rotationIntegerPrefix (D.horizontalOstrowskiDigits m) (m + 1) +
          ⌊D.rotationErrorPrefix (D.horizontalOstrowskiDigits m) (m + 1)⌋ + 1) := by
  rfl

/--
無理回転 roof の一般 `rankDropInt` は Ostrowski 側の rank drop と exact に一致する。
`m*r` の線形項が相殺され、純粋な回転整数部・誤差だけが残る。
-/
theorem rankDropInt_irrationalRotationRoof_eq_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m r : ℕ) :
    rankDropInt (irrationalRotationRoof α) m r =
      D.ostrowskiRankDropInt m r := by
  unfold rankDropInt ostrowskiRankDropInt
  rw [D.criticalDepth_irrationalRotationRoof_cast_eq_ostrowski A r]
  rw [D.criticalDepth_irrationalRotationRoof_cast_eq_ostrowski A m]
  ring

/-- 自然数化した rank drop も両側で exact に一致する。 -/
theorem rankDropNat_irrationalRotationRoof_eq_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m r : ℕ) :
    rankDropNat (irrationalRotationRoof α) m r =
      D.ostrowskiRankDropNat m r := by
  unfold rankDropNat ostrowskiRankDropNat
  rw [D.rankDropInt_irrationalRotationRoof_eq_ostrowski A m r]

/--
横幅 `r` は horizontal canonical Ostrowski digits の weighted sum そのもの。
これは Young/Ferrers block の水平辺を digits から読む exact dictionary である。
-/
theorem horizontalWidth_eq_ostrowskiDigits
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (r : ℕ) :
    r =
      ostrowskiPrefixSum D.horizontalWeights.Q
        (D.horizontalOstrowskiDigits r) (r + 1) := by
  exact (D.horizontalOstrowskiDigits_reconstruct r).symm

/-- Ostrowski rank drop の suffix sum。 -/
noncomputable def ostrowskiRankDropNatSum
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs =>
      D.ostrowskiRankDropNat m r + D.ostrowskiRankDropNatSum m rs

/-- Ostrowski drop の suffix sum は一般 rank-drop suffix sum と一致する。 -/
theorem ostrowskiRankDropNatSum_eq_rankDropNatSum
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ) :
    ∀ rs : List ℕ,
      D.ostrowskiRankDropNatSum m rs =
        rankDropNatSum (irrationalRotationRoof α) m rs
  | [] => by
      rfl
  | r :: rs => by
      simp only [ostrowskiRankDropNatSum, rankDropNatSum]
      rw [← D.rankDropNat_irrationalRotationRoof_eq_ostrowski A m r]
      rw [D.ostrowskiRankDropNatSum_eq_rankDropNatSum A m rs]

/--
Ostrowski data だけから作る rank-envelope Ferrers 列高。
各 block の水平長は `r`、高さは Ostrowski rank drop の suffix sum である。
-/
noncomputable def ostrowskiFerrersColumnHeightFromLengths
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, k =>
      if k < r then
        D.ostrowskiRankDropNatSum m (r :: rs)
      else
        D.ostrowskiFerrersColumnHeightFromLengths m rs (k - r)

/-- Ostrowski 版の列高は前段の rank-envelope 列高と一点ごとに一致する。 -/
theorem ostrowskiFerrersColumnHeightFromLengths_eq_rank
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ) :
    ∀ (rs : List ℕ) (k : ℕ),
      D.ostrowskiFerrersColumnHeightFromLengths m rs k =
        rankFerrersColumnHeightFromLengths
          (irrationalRotationRoof α) m rs k
  | [], _k => by
      rfl
  | r :: rs, k => by
      by_cases hk : k < r
      · simp [ostrowskiFerrersColumnHeightFromLengths,
          rankFerrersColumnHeightFromLengths, hk,
          D.ostrowskiRankDropNatSum_eq_rankDropNatSum A m]
      · simp [ostrowskiFerrersColumnHeightFromLengths,
          rankFerrersColumnHeightFromLengths, hk,
          D.ostrowskiFerrersColumnHeightFromLengths_eq_rank A m rs (k - r)]

/-- Ostrowski 版の列高は右へ進むほど増えない。 -/
theorem ostrowskiFerrersColumnHeightFromLengths_antitone
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (rs : List ℕ) :
    Antitone (D.ostrowskiFerrersColumnHeightFromLengths m rs) := by
  intro i j hij
  rw [D.ostrowskiFerrersColumnHeightFromLengths_eq_rank A m rs i]
  rw [D.ostrowskiFerrersColumnHeightFromLengths_eq_rank A m rs j]
  exact
    rankFerrersColumnHeightFromLengths_antitone
      (irrationalRotationRoof α) m rs hij

/--
任意の length code を、horizontal Ostrowski data から直接
古典 Ferrers / Young shape として読む。
-/
noncomputable def ostrowskiRankFerrersShapeFromLengths
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (rs : List ℕ) :
    Combinatorics.FerrersShape (m - 1) :=
  ⟨fun k => D.ostrowskiFerrersColumnHeightFromLengths m rs k.1,
    by
      intro i j hij
      exact D.ostrowskiFerrersColumnHeightFromLengths_antitone A m rs hij⟩

/--
Ostrowski data から作った Ferrers shape は、前段の rank-drop から作った shape と exact に一致する。
従って Ostrowski 表現は Young/Ferrers 図形の外形を失わずに符号化する。
-/
theorem ostrowskiRankFerrersShapeFromLengths_eq_rankFerrersShapeFromLengths
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (rs : List ℕ) :
    D.ostrowskiRankFerrersShapeFromLengths A m rs =
      rankFerrersShapeFromLengths (irrationalRotationRoof α) m rs := by
  apply Subtype.ext
  funext k
  exact D.ostrowskiFerrersColumnHeightFromLengths_eq_rank A m rs k.1

/--
選ぶ `RotationOstrowskiSystem` が異なっても、得られる Ferrers shape は同じ。
形は回転 `α` と length code だけに依存し、continued-fraction certificate の選び方には依存しない。
-/
theorem ostrowskiRankFerrersShapeFromLengths_independent
    {α : ℝ}
    (D E : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    (m : ℕ)
    (rs : List ℕ) :
    D.ostrowskiRankFerrersShapeFromLengths A m rs =
      E.ostrowskiRankFerrersShapeFromLengths A m rs := by
  rw [D.ostrowskiRankFerrersShapeFromLengths_eq_rankFerrersShapeFromLengths A m rs]
  rw [E.ostrowskiRankFerrersShapeFromLengths_eq_rankFerrersShapeFromLengths A m rs]

end RotationOstrowskiSystem

/-- `PositiveRankDrops` の code に現れる各 block の rank drop は正。 -/
theorem positiveRankDrop_of_mem
    {β : ℕ → ℕ}
    {m r : ℕ} :
    ∀ {rs : List ℕ},
      PositiveRankDrops β m rs →
      r ∈ rs →
        0 < rankDropInt β m r
  | [], _P, hr => by
      simp at hr
  | x :: xs, P, hr => by
      simp only [PositiveRankDrops] at P
      simp only [List.mem_cons] at hr
      rcases hr with hEq | hMem
      · subst x
        exact P.1
      · exact positiveRankDrop_of_mem P.2 hMem

namespace RecordFerrers

/--
完成 RecordFerrers の一つの canonical block について、
横幅と縦落差を同じ horizontal Ostrowski code で同時に読む。

第一成分は横幅の weighted-sum 復元、第二成分は縦落差の exact 同定、
第三成分は canonical record block なのでその落差が strict に正であることを表す。
-/
theorem canonicalBlock_ostrowski_width_drop
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    {m r : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m)
    (hr : r ∈ canonicalRecordLengths
      (irrationalRotationRoof α) m R.height) :
    r =
        ostrowskiPrefixSum D.horizontalWeights.Q
          (D.horizontalOstrowskiDigits r) (r + 1) ∧
      rankDropNat (irrationalRotationRoof α) m r =
        D.ostrowskiRankDropNat m r ∧
      0 < D.ostrowskiRankDropInt m r := by
  refine ⟨D.horizontalWidth_eq_ostrowskiDigits r, ?_, ?_⟩
  · exact D.rankDropNat_irrationalRotationRoof_eq_ostrowski A m r
  · have hPos :
        0 < rankDropInt (irrationalRotationRoof α) m r :=
      positiveRankDrop_of_mem R.positiveRankDrops hr
    rw [D.rankDropInt_irrationalRotationRoof_eq_ostrowski A m r] at hPos
    exact hPos

/--
与えられた Ostrowski system から、完成 RecordFerrers に対応する Ferrers shape を直接作る。
この shape は canonical length code と horizontal Ostrowski digits だけから計算される。
-/
noncomputable def ostrowskiRankFerrersShape
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    Combinatorics.FerrersShape (m - 1) :=
  D.ostrowskiRankFerrersShapeFromLengths A m
    (canonicalRecordLengths (irrationalRotationRoof α) m R.height)

/--
Ostrowski data から直接作った shape は、RecordFerrers の rank-envelope shape そのもの。
-/
theorem ostrowskiRankFerrersShape_eq_rankFerrersShape
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    R.ostrowskiRankFerrersShape D A = R.rankFerrersShape := by
  unfold ostrowskiRankFerrersShape RecordFerrers.rankFerrersShape
  exact
    D.ostrowskiRankFerrersShapeFromLengths_eq_rankFerrersShapeFromLengths
      A m (canonicalRecordLengths (irrationalRotationRoof α) m R.height)

/--
存在定理で構成した canonical `RotationOstrowskiSystem` を使う Ferrers shape。
外部 certificate を引数として残さない公開版。
-/
noncomputable def canonicalOstrowskiRankFerrersShape
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    Combinatorics.FerrersShape (m - 1) :=
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  R.ostrowskiRankFerrersShape D A

/-- canonical existence construction を使っても、得られる shape は元の rank-envelope shape と一致する。 -/
theorem canonicalOstrowskiRankFerrersShape_eq_rankFerrersShape
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    R.canonicalOstrowskiRankFerrersShape A = R.rankFerrersShape := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  change R.ostrowskiRankFerrersShape D A = R.rankFerrersShape
  exact R.ostrowskiRankFerrersShape_eq_rankFerrersShape D A

/--
任意の無理回転上の完成 RecordFerrers について、
Ostrowski digits から構成した Ferrers shape が存在し、それは rank-envelope shape と exact に一致する。
-/
theorem exists_ostrowskiRankFerrersShape_eq_rankFerrersShape
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m) :
    ∃ D : RotationOstrowskiSystem α,
      R.ostrowskiRankFerrersShape D A = R.rankFerrersShape := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  exact ⟨D, R.ostrowskiRankFerrersShape_eq_rankFerrersShape D A⟩

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
