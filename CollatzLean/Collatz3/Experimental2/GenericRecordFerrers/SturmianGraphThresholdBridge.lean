import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphYoungCodeComparison
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.OstrowskiRecordFerrers

/-!
# Collatz3 Experimental2: Sturmian path code による RecordFerrers threshold law

S1--S5 までで、canonical block length `r` は

* canonical greedy Ostrowski code、
* actual Sturmian graph path の `edgeCount` code

のどちらからも lossless に復元でき、両 code は canonical image 上で exact に
相互変換できることを閉じた。

本ファイルでは、これまで canonical Ostrowski phase で書いていた
RecordFerrers の threshold / carry 条件を actual Sturmian path code 側へ移す。

重要なのは、greedy digit と lazy/path digit を直接同一視しないことである。
Sturmian path code はまず自身の weight を復号し、その weight の canonical
Ostrowski phase を読む。canonical path code 上ではこの phase は元の block length の
`ostrowskiPhase` と exact に一致する。

中心結果は

`CanonicalOstrowskiThresholdCompatible`
`<-> CanonicalSturmianPathThresholdCompatible`

および

`IsRecordFerrersPath`
`<-> admissible / width / CanonicalSturmianPathThresholdCompatible`

である。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RotationOstrowskiSystem

/--
actual Sturmian path edge-count code から、その path の weight を読む。
canonical code でない入力には既存 decoder と同様 `0` が返る。
-/
noncomputable def sturmianPathCodeWeight
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (code : ℕ → ℕ) : ℕ :=
  canonicalSturmianPathWeight D.horizontalWeights code

/-- canonical weight-`N` path code を復号すると `N` に戻る。 -/
@[simp] theorem sturmianPathCodeWeight_code
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.sturmianPathCodeWeight (D.sturmianPathCodeOfWeight N) = N := by
  simp only [sturmianPathCodeWeight, sturmianPathCodeOfWeight, canonicalSturmianPathWeight_code]


/--
Sturmian path code が表す block weight の mechanical / Ostrowski phase。

phase の primitive data は増やさず、path code -> weight -> 既存 `ostrowskiPhase`
という derived coordinate とする。
-/
noncomputable def sturmianPathPhase
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (code : ℕ → ℕ) : ℝ :=
  D.ostrowskiPhase (D.sturmianPathCodeWeight code)

/-- canonical weight-`N` path code の phase は元の `ostrowskiPhase N` と exact に一致する。 -/
@[simp] theorem sturmianPathPhase_code
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.sturmianPathPhase (D.sturmianPathCodeOfWeight N) =
      D.ostrowskiPhase N := by
  simp [sturmianPathPhase]

/--
proper local prefix で禁止する path-code 版の wrap event。

現在 block の長さは actual Sturmian path code `rCode` から復号する。
anchor `a` と proper prefix `j` の phase も、それぞれ canonical path code を経由して読む。
従って threshold 側では greedy digit を一切参照しない。
-/
noncomputable def NoPrematureSturmianPathWrapRoofReturn
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a : ℕ)
    (rCode : ℕ → ℕ) : Prop :=
  ∀ j : ℕ,
    0 < j →
    j < D.sturmianPathCodeWeight rCode →
    ¬ (IsProperRoofCut (irrationalRotationRoof α) m height (a + j) ∧
      1 ≤
        D.sturmianPathPhase (D.sturmianPathCodeOfWeight a) +
          D.sturmianPathPhase (D.sturmianPathCodeOfWeight j))

/--
canonical weight-`r` path code 上では、path-code 版 premature-wrap 禁止条件と
既存 canonical Ostrowski 版は exact に同値。
-/
theorem noPrematureSturmianPathWrapRoofReturn_code_iff_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    {height : ℕ → ℕ}
    (a r : ℕ) :
    D.NoPrematureSturmianPathWrapRoofReturn
        m height a (D.sturmianPathCodeOfWeight r) ↔
      D.NoPrematureOstrowskiWrapRoofReturn m height a r := by
  simp [
    NoPrematureSturmianPathWrapRoofReturn,
    NoPrematureOstrowskiWrapRoofReturn
  ]

/--
canonical block path-code 列に沿う contextual threshold compatibility。

anchor 自体は RecordFerrers chain 上の位置なので自然数のまま保持する。
各 block length と各 mechanical phase は actual Sturmian path code から読む。
-/
noncomputable def SturmianPathThresholdCompatibleFrom
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List (ℕ → ℕ) → Prop
  | _a, [] => False
  | a, [rCode] =>
      D.NoPrematureSturmianPathWrapRoofReturn m height a rCode ∧
        D.sturmianPathPhase (D.sturmianPathCodeOfWeight a) +
            D.sturmianPathPhase rCode < 1
  | a, rCode :: sCode :: rest =>
      D.NoPrematureSturmianPathWrapRoofReturn m height a rCode ∧
        D.SturmianPathThresholdCompatibleFrom
          m height (a + D.sturmianPathCodeWeight rCode) (sCode :: rest)

/--
任意 block length 列を canonical path-code 列へ写した像では、
既存 Ostrowski threshold law と path-code threshold law は exact に同値。
-/
theorem ostrowskiThresholdCompatibleFrom_iff_sturmianPathCode
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      D.OstrowskiThresholdCompatibleFrom m height a rs ↔
        D.SturmianPathThresholdCompatibleFrom
          m height a (D.sturmianPathLengthCode rs)
  | _a, [] => by
      simp [
        OstrowskiThresholdCompatibleFrom,
        SturmianPathThresholdCompatibleFrom,
        sturmianPathLengthCode
      ]
  | a, [r] => by
      simp only [
        OstrowskiThresholdCompatibleFrom,
        SturmianPathThresholdCompatibleFrom,
        sturmianPathLengthCode,
        List.map_cons,
        List.map_nil
      ]
      exact and_congr
        (D.noPrematureSturmianPathWrapRoofReturn_code_iff_ostrowski
          (m := m) (height := height) a r).symm
        (by simp)
  | a, r :: s :: rs => by
      simp only [
        OstrowskiThresholdCompatibleFrom,
        SturmianPathThresholdCompatibleFrom,
        sturmianPathLengthCode,
        List.map_cons
      ]
      have hLocal :=
        (D.noPrematureSturmianPathWrapRoofReturn_code_iff_ostrowski
          (m := m) (height := height) a r).symm
      have hTail :=
        D.ostrowskiThresholdCompatibleFrom_iff_sturmianPathCode
          (m := m) (height := height) (a + r) (s :: rs)
      simpa [
        sturmianPathLengthCode,
        sturmianPathCodeWeight,
        sturmianPathCodeOfWeight
      ] using and_congr hLocal hTail

/-- deterministic canonical RecordFerrers partition 上の Sturmian path threshold law。 -/
noncomputable def CanonicalSturmianPathThresholdCompatible
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  D.SturmianPathThresholdCompatibleFrom
    m height canonicalAnchor
      (D.sturmianPathLengthCode
        (canonicalRecordLengths (irrationalRotationRoof α) m height))

/-- canonical Ostrowski threshold と canonical Sturmian path threshold は exact に同値。 -/
theorem canonicalOstrowskiThresholdCompatible_iff_sturmianPath
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    D.CanonicalOstrowskiThresholdCompatible m height ↔
      D.CanonicalSturmianPathThresholdCompatible m height := by
  unfold CanonicalOstrowskiThresholdCompatible
  unfold CanonicalSturmianPathThresholdCompatible
  exact
    D.ostrowskiThresholdCompatibleFrom_iff_sturmianPathCode
      canonicalAnchor
      (canonicalRecordLengths (irrationalRotationRoof α) m height)

/-- canonical carry law を actual Sturmian path-code threshold だけで特徴付ける。 -/
theorem canonicalCarryCompatible_iff_sturmianPath
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    CanonicalCarryCompatible (irrationalRotationRoof α) m height ↔
      D.CanonicalSturmianPathThresholdCompatible m height := by
  exact
    (D.canonicalCarryCompatible_iff_ostrowski Arot).trans
      D.canonicalOstrowskiThresholdCompatible_iff_sturmianPath

/--
canonical path-code threshold law は、
admissible path 上で canonical local critical geometry と exact に同値。
-/
theorem canonicalSturmianPathThresholdCompatible_iff_localRoofCriticalBlocks
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath (irrationalRotationRoof α) m height)
    (hm : 1 < m) :
    D.CanonicalSturmianPathThresholdCompatible m height ↔
      LocalRoofCriticalBlocksFrom
        (irrationalRotationRoof α) m height canonicalAnchor
        (canonicalRecordLengths (irrationalRotationRoof α) m height) := by
  exact
    D.canonicalOstrowskiThresholdCompatible_iff_sturmianPath.symm.trans
      (D.canonicalOstrowskiThresholdCompatible_iff_localRoofCriticalBlocks
        Arot A hm)

/--
任意無理回転 roof 上の完成 RecordFerrers path を、actual Sturmian path-code threshold だけで特徴付ける。
-/
theorem isRecordFerrersPath_iff_sturmianPath
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    IsRecordFerrersPath (irrationalRotationRoof α) m height ↔
      IsAdmissibleRoofPath (irrationalRotationRoof α) m height ∧
        1 < m ∧
          D.CanonicalSturmianPathThresholdCompatible m height := by
  have hRF := isRecordFerrersPath_iff_ostrowski D Arot (m := m) (height := height)
  constructor
  · intro R
    have h := hRF.1 R
    exact
      ⟨h.1, h.2.1,
        D.canonicalOstrowskiThresholdCompatible_iff_sturmianPath.1 h.2.2⟩
  · rintro ⟨A, hm, S⟩
    apply hRF.2
    exact
      ⟨A, hm,
        D.canonicalOstrowskiThresholdCompatible_iff_sturmianPath.2 S⟩

end RotationOstrowskiSystem

namespace RecordFerrers

/--
完成 RecordFerrers は、その canonical block actual Sturmian path-code 列上で
canonical path threshold law を自動的に満たす。
-/
theorem sturmianPathThresholdCompatible
    {α : ℝ}
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m)
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α) :
    D.CanonicalSturmianPathThresholdCompatible m R.height := by
  exact
    D.canonicalOstrowskiThresholdCompatible_iff_sturmianPath.1
      (R.ostrowskiThresholdCompatible D Arot)

/--
完成 RecordFerrers の canonical local critical geometry を path-code threshold law から回収する。
-/
theorem localCriticalBlocks_of_sturmianPath
    {α : ℝ}
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m)
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α) :
    LocalRoofCriticalBlocksFrom
      (irrationalRotationRoof α) m R.height canonicalAnchor
      (canonicalRecordLengths (irrationalRotationRoof α) m R.height) := by
  exact
    (D.canonicalSturmianPathThresholdCompatible_iff_localRoofCriticalBlocks
      Arot R.admissible R.one_lt_width).1
      (R.sturmianPathThresholdCompatible D Arot)

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
