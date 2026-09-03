import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ExactGapOneBeattyCertificate
import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicActualWord

/-!
# independent critical defect profile から minimal FirstCrossing word への逆構成

これまでの `AdmissibleCriticalDefectProfile w` は、既に存在する word `w` の性質だった。
第3例を設計するには、word より先に Ferrers geometry を選びたい。

ここでは odd-step 数 `p` に対して、word を一切保持しない独立データ

* prefix height `height k`,
* critical roof からの差 `defect k`,

を持つ。隣接 height の差

  e_k = height(k+1) - height(k)

を exponent として word を生成する。

proper cuts が critical roof 以下、height が strict に増加、terminal が roof+1
という条件から、生成 word が valid minimal FirstCrossing であることを復元する。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

/-- 高さ列の隣接差から長さ `p` の exponent word を作る。 -/
def wordFromHeight (height : ℕ → ℕ) (p : ℕ) : Word :=
  (List.range p).map (fun k => height (k + 1) - height k)

@[simp] theorem oddSteps_wordFromHeight
    (height : ℕ → ℕ)
    (p : ℕ) :
    Word.oddSteps (wordFromHeight height p) = p := by
  simp [wordFromHeight, Word.oddSteps]

/-- strict increasing な高さ列から作った exponent word は valid。 -/
theorem valid_wordFromHeight
    (height : ℕ → ℕ)
    (p : ℕ)
    (hStep : ∀ k : ℕ, k < p → height k < height (k + 1)) :
    Word.Valid (wordFromHeight height p) := by
  intro e he
  unfold wordFromHeight at he
  rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
  have hkLt : k < p := by
    simpa using hk
  exact Nat.sub_pos_of_lt (hStep k hkLt)

/-- 隣接差の総和は、開始高さ0なら terminal height そのもの。 -/
theorem twoSteps_wordFromHeight
    (height : ℕ → ℕ)
    (p : ℕ)
    (hZero : height 0 = 0)
    (hStep : ∀ k : ℕ, k < p → height k < height (k + 1)) :
    Word.twoSteps (wordFromHeight height p) = height p := by
  unfold Word.twoSteps wordFromHeight
  revert hStep
  induction p with
  | zero =>
      intro hStep
      simp [hZero]
  | succ p ih =>
      intro hStep
      have hPrev : ∀ k : ℕ, k < p → height k < height (k + 1) := by
        intro k hk
        exact hStep k (by omega)
      have hIH := ih hPrev
      have hLast := hStep p (by omega)
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      rw [hIH]
      omega

/-- `k ≤ p` なら生成 word の prefix depth は指定 height `k` に戻る。 -/
theorem prefixTwoDepth_wordFromHeight
    (height : ℕ → ℕ)
    (p : ℕ)
    (hZero : height 0 = 0)
    (hStep : ∀ i : ℕ, i < p → height i < height (i + 1))
    {k : ℕ}
    (hk : k ≤ p) :
    Word.prefixTwoDepth (wordFromHeight height p) k = height k := by
  unfold Word.prefixTwoDepth wordFromHeight
  rw [← List.map_take]
  rw [List.take_range, Nat.min_eq_left hk]
  exact twoSteps_wordFromHeight height k hZero
    (fun i hi => hStep i (lt_of_lt_of_le hi hk))

/--
word から独立した critical defect geometry。

`height_eq_roof_sub_defect` と `defect_le_roof` により proper geometry を保持し、
`strict_step` が exponent positivity、`terminal_height` が exact first-crossing depth を表す。
-/
structure IndependentCriticalDefectProfile (p : ℕ) where
  height : ℕ → ℕ
  defect : ℕ → ℕ
  height_zero : height 0 = 0
  defect_le_roof : ∀ k : ℕ, k < p → defect k ≤ Word.criticalHeight k
  height_eq_roof_sub_defect : ∀ k : ℕ, k < p →
    height k = Word.criticalHeight k - defect k
  strict_step : ∀ k : ℕ, k < p → height k < height (k + 1)
  terminal_height : height p = Word.criticalHeight p + 1
  terminal_contracting : 3 ^ p < 2 ^ height p

/-- 独立 profile が生成する exponent word。 -/
def IndependentCriticalDefectProfile.toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p) : Word :=
  wordFromHeight D.height p

@[simp] theorem IndependentCriticalDefectProfile.oddSteps_toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p) :
    Word.oddSteps D.toWord = p := by
  exact oddSteps_wordFromHeight D.height p

/-- 独立 profile は `p=0` では存在しない。 -/
theorem IndependentCriticalDefectProfile.p_pos
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p) :
    0 < p := by
  by_contra hnot
  have hp0 : p = 0 := Nat.eq_zero_of_not_pos hnot
  subst p
  have hTerminal := D.terminal_height
  rw [D.height_zero] at hTerminal
  simp [Word.criticalHeight] at hTerminal

/-- 生成 word は valid。 -/
theorem IndependentCriticalDefectProfile.valid_toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p) :
    Word.Valid D.toWord := by
  exact valid_wordFromHeight D.height p D.strict_step

/-- 生成 word の prefix depth は指定した independent height と exact に一致。 -/
theorem IndependentCriticalDefectProfile.prefixTwoDepth_toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p)
    {k : ℕ}
    (hk : k ≤ p) :
    Word.prefixTwoDepth D.toWord k = D.height k := by
  exact prefixTwoDepth_wordFromHeight D.height p
    D.height_zero D.strict_step hk

/-- 生成 word の terminal 2-depth は critical roof + 1。 -/
theorem IndependentCriticalDefectProfile.twoSteps_toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p) :
    Word.twoSteps D.toWord = Word.criticalHeight p + 1 := by
  calc
    Word.twoSteps D.toWord = D.height p :=
      twoSteps_wordFromHeight D.height p D.height_zero D.strict_step
    _ = Word.criticalHeight p + 1 := D.terminal_height

/-- proper cut で指定 defect を actual `Word.criticalDefect` として完全復元する。 -/
theorem IndependentCriticalDefectProfile.criticalDefect_toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p)
    {k : ℕ}
    (hk : k < p) :
    Word.criticalDefect D.toWord k = D.defect k := by
  unfold Word.criticalDefect
  rw [D.prefixTwoDepth_toWord (Nat.le_of_lt hk)]
  rw [D.height_eq_roof_sub_defect k hk]
  have hLe := D.defect_le_roof k hk
  omega

/-- 独立 profile から生成した word は minimal FirstCrossing。 -/
theorem IndependentCriticalDefectProfile.firstCrossing_toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p) :
    Word.FirstCrossing D.toWord := by
  refine {
    nonempty := ?_
    properPositive := ?_
    terminalNegative := ?_
  }
  · have hp : 0 < p := D.p_pos
    apply List.ne_nil_of_length_pos
    simpa [IndependentCriticalDefectProfile.toWord, wordFromHeight] using hp
  · intro k hkPos hkLt
    have hLen : D.toWord.length = p := by
      simpa [Word.oddSteps] using D.oddSteps_toWord
    have hkLtP : k < p := by
      simpa [hLen] using hkLt
    have hHeightEq := D.height_eq_roof_sub_defect k hkLtP
    have hDepthEq := D.prefixTwoDepth_toWord (Nat.le_of_lt hkLtP)
    have hDepthLe :
        Word.prefixTwoDepth D.toWord k ≤ Word.criticalHeight k := by
      rw [hDepthEq, hHeightEq]
      omega
    have hPowLe :
        2 ^ Word.prefixTwoDepth D.toWord k ≤ 2 ^ Word.criticalHeight k :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepthLe
    have hRoof : 2 ^ Word.criticalHeight k < 3 ^ k :=
      Word.criticalHeight_pow_lt_threePow hkPos
    have hPow : 2 ^ Word.prefixTwoDepth D.toWord k < 3 ^ k :=
      lt_of_le_of_lt hPowLe hRoof
    have hkLe : k ≤ D.toWord.length := Nat.le_of_lt hkLt
    have hTakeLen : (D.toWord.take k).length = k :=
      List.length_take_of_le hkLe
    apply (Word.expanding_iff_twoPow_lt_threePow).2
    simpa [Word.prefixTwoDepth, Word.oddSteps, hTakeLen] using hPow
  · apply (Word.contracting_iff_threePow_lt_twoPow).2
    rw [D.oddSteps_toWord]
    have hTwo : Word.twoSteps D.toWord = D.height p :=
      twoSteps_wordFromHeight D.height p D.height_zero D.strict_step
    rw [hTwo]
    exact D.terminal_contracting

/-- 独立 profile から valid minimal block が得られる。 -/
theorem IndependentCriticalDefectProfile.validMinimalCrossingBlock_toWord
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p) :
    ValidMinimalCrossingBlock D.toWord :=
  ⟨D.valid_toWord, D.firstCrossing_toWord⟩

/--
既存の exact-terminal minimal word から independent defect profile を取り出す。
これは逆方向の extraction map。
-/
def independentCriticalDefectProfileOfWord
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (hTerminal :
      Word.twoSteps w = Word.criticalHeight (Word.oddSteps w) + 1) :
    IndependentCriticalDefectProfile (Word.oddSteps w) where
  height := fun k => Word.prefixTwoDepth w k
  defect := fun k => Word.criticalDefect w k
  height_zero := by simp [Word.prefixTwoDepth]
  defect_le_roof := by
    intro k hk
    unfold Word.criticalDefect
    omega
  height_eq_roof_sub_defect := by
    intro k hk
    have hDepth : Word.prefixTwoDepth w k ≤ Word.criticalHeight k := by
      by_cases hk0 : k = 0
      · subst k
        simp [Word.prefixTwoDepth]
      · exact C.2.prefixTwoDepth_le_criticalHeight
          (Nat.pos_of_ne_zero hk0) hk
    unfold Word.criticalDefect
    omega
  strict_step := by
    intro k hk
    exact Word.prefixTwoDepth_lt_of_valid C.1
      (i := k) (j := k + 1) (by omega) (by omega)
  terminal_height := by
    simpa [Word.prefixTwoDepth, Word.oddSteps] using hTerminal
  terminal_contracting := by
    have hC := (Word.contracting_iff_threePow_lt_twoPow).1 C.2.terminalContracting
    simpa [Word.prefixTwoDepth, Word.oddSteps] using hC

/--
独立 defect profile が存在することと、terminal depth が roof+1 の
valid minimal FirstCrossing word が存在することは同値。

これが探索側で使う object-level の inverse-construction equivalence。
-/
theorem independentCriticalDefectProfile_nonempty_iff_exists_minimalWord
    (p : ℕ) :
    Nonempty (IndependentCriticalDefectProfile p) ↔
      ∃ w : Word,
        ValidMinimalCrossingBlock w ∧
        Word.oddSteps w = p ∧
        Word.twoSteps w = Word.criticalHeight p + 1 := by
  constructor
  · rintro ⟨D⟩
    refine ⟨D.toWord, D.validMinimalCrossingBlock_toWord,
      D.oddSteps_toWord, ?_⟩
    exact D.twoSteps_toWord
  · rintro ⟨w, hMinimal, hp, hTerminal⟩
    have hTerminal' :
        Word.twoSteps w = Word.criticalHeight (Word.oddSteps w) + 1 := by
      rw [hp]
      exact hTerminal
    let D := independentCriticalDefectProfileOfWord hMinimal hTerminal'
    have D' : IndependentCriticalDefectProfile p := by
      simpa [hp] using D
    exact ⟨D'⟩

end DoubleDecomposition
end CSTMicro
end Collatz2
