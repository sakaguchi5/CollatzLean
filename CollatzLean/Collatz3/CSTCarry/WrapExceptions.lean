import CollatzLean.Collatz3.CSTCarry.FerrersCarry


/-!
# Collatz3 CSTCarry: 一時 wrap の例外分類

`CarryBelowModulus` は final carry だけを要求する。
途中 carry まで常に modulus 未満である必要はなく、実際には一時的な wrap が起こり得る。

このファイルでは、その例外を pure carry arithmetic として切り出す。

row recurrence

  E + d + M*a = 3*E'

に対して、row defect が

  2*d < M

を満たす場合、次が成り立つ。

* modulus 未満から初めて wrap する digit は必ず `2`。
* 初回 wrap の overhang `E'-M` は `M/4` 未満。
* wrap 中に digit `2` が続く限り、この `M/4` bound は保存される。
* wrap 中に digit `0` または `1` が現れれば、次 carry は必ず modulus 未満へ戻る。

従って途中 wrap は「禁止」ではなく、bounded exception として扱える。
RecordFerrers との最終的な接続は別 bridge の責務とし、ここでは仮定しない。
-/

namespace Collatz3
namespace CSTCarry

namespace FerrersRow

/-- Ferrers defect は boundary の 2 冪より strict に小さい。 -/
theorem defect_lt_twoPow_boundary (R : FerrersRow) :
    R.defect < 2 ^ R.boundary := by
  have hPow :
      2 ^ R.actual ≤ 2 ^ R.boundary :=
    Nat.pow_le_pow_right
      (by decide : 0 < (2 : ℕ))
      R.actual_le_boundary
  have hPos : 0 < 2 ^ R.actual :=
    pow_pos (by decide : 0 < (2 : ℕ)) R.actual
  unfold defect
  omega
/--
row boundary が bit width `H` より手前なら defect は modulus の半分未満。

`2 * defect < 2^H`
-/
theorem two_mul_defect_lt_twoPow_of_boundary_lt
    (R : FerrersRow)
    {H : ℕ}
    (hBoundary : R.boundary < H) :
    2 * R.defect < 2 ^ H := by
  have hDefect := R.defect_lt_twoPow_boundary
  have hTwice :
      2 * R.defect < 2 * (2 ^ R.boundary) :=
    (Nat.mul_lt_mul_left (by decide : 0 < (2 : ℕ))).2 hDefect
  have hPowStep :
      2 * R.defect < 2 ^ (R.boundary + 1) := by
    simpa [pow_succ, Nat.mul_comm] using hTwice
  have hExp : R.boundary + 1 ≤ H := by
    omega
  have hPowLe :
      2 ^ (R.boundary + 1) ≤ 2 ^ H :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hExp
  exact lt_of_lt_of_le hPowStep hPowLe

end FerrersRow

/-- row defect が modulus の半分未満であるという局所条件。 -/
def SmallDefect (M d : ℕ) : Prop :=
  2 * d < M

/-- row list 全体が `SmallDefect` を満たす。 -/
def RowsSmallForModulus
    (M : ℕ)
    (rows : List FerrersRow) : Prop :=
  ∀ R ∈ rows, SmallDefect M R.defect

/-- 全 row boundary が H-bit terminal boundary より strict に手前にある。 -/
def RowsInsideBitWidth
    (H : ℕ)
    (rows : List FerrersRow) : Prop :=
  ∀ R ∈ rows, R.boundary < H

/-- actual row boundary 条件から `2*defect < 2^H` を一括して得る。 -/
theorem rowsSmallForPow_of_insideBitWidth
    {H : ℕ}
    {rows : List FerrersRow}
    (hRows : RowsInsideBitWidth H rows) :
    RowsSmallForModulus (2 ^ H) rows := by
  intro R hR
  exact R.two_mul_defect_lt_twoPow_of_boundary_lt (hRows R hR)

/--
carry が modulus 未満、または modulus を越えていても overhang が `M/4` 未満、
という一時 wrap を許した安全状態。
-/
def CarrySafeState (M E : ℕ) : Prop :=
  E < M ∨
    (M ≤ E ∧ 4 * (E - M) < M)

/-- safe state が modulus 以上なら、その overhang は `M/4` 未満。 -/
theorem carrySafeState_overhang_lt_quarter
    {M E : ℕ}
    (hSafe : CarrySafeState M E)
    (hWrap : M ≤ E) :
    4 * (E - M) < M := by
  rcases hSafe with hBelow | hWrapped
  · omega
  · exact hWrapped.2

/--
modulus 未満から modulus 以上へ初めて移る row では、
`d < M` の下で digit は必ず `2`。
-/
theorem first_wrap_digit_eq_two
    {M E d a E' : ℕ}
    (hBelow : E < M)
    (hDefect : d < M)
    (ha : a < 3)
    (hEq : E + d + M * a = 3 * E')
    (hWrap : M ≤ E') :
    a = 2 := by
  have hCases : a = 0 ∨ a = 1 ∨ a = 2 := by
    omega
  rcases hCases with hZero | hOne | hTwo
  · subst a
    simp at hEq
    omega
  · subst a
    simp at hEq
    omega
  · exact hTwo

/--
正常状態から次 step が wrap する条件の exact 分解。

`M ≤ E'` なら digit は `2` で、defect は current headroom を食い切る。
逆に digit `2` かつ `M-E ≤ d` なら次 carry は wrap する。
-/
theorem next_wrap_iff_digit_two_and_gap_le_defect
    {M E d a E' : ℕ}
    (hBelow : E < M)
    (hDefect : d < M)
    (ha : a < 3)
    (hEq : E + d + M * a = 3 * E') :
    M ≤ E' ↔
      a = 2 ∧ M - E ≤ d := by
  constructor
  · intro hWrap
    have haTwo := first_wrap_digit_eq_two hBelow hDefect ha hEq hWrap
    subst a
    constructor
    · rfl
    · omega
  · rintro ⟨rfl, hGap⟩
    omega

/--
初回 wrap では defect が

`current headroom + 3 * next overhang`

へ exact に分解される。
-/
theorem first_wrap_defect_decomposition
    {M E d E' : ℕ}
    (hBelow : E < M)
    (hEq : E + d + M * 2 = 3 * E')
    (hWrap : M ≤ E') :
    d = (M - E) + 3 * (E' - M) := by
  omega

/-- wrap 中の digit `2` step では overhang recurrence が exact に閉じる。 -/
theorem wrapped_two_overhang_recurrence
    {M E d E' : ℕ}
    (hWrap : M ≤ E)
    (hEq : E + d + M * 2 = 3 * E')
    (hNextWrap : M ≤ E') :
    3 * (E' - M) = (E - M) + d := by
  omega

/-- `SmallDefect` 版の first-wrap digit 分類。 -/
theorem first_wrap_digit_eq_two_of_smallDefect
    {M E d a E' : ℕ}
    (hBelow : E < M)
    (hDefect : SmallDefect M d)
    (ha : a < 3)
    (hEq : E + d + M * a = 3 * E')
    (hWrap : M ≤ E') :
    a = 2 := by
  have hdLt : d < M := by
    unfold SmallDefect at hDefect
    omega
  exact first_wrap_digit_eq_two hBelow hdLt ha hEq hWrap

/--
初回 wrap は digit `2` でしか起こらず、その直後の overhang は実際には `M/6` 未満。
後続の safe-state invariant では、この強い bound から `M/4` bound を導いて使う。
-/
theorem first_wrap_overhang_lt_sixth
    {M E d E' : ℕ}
    (hBelow : E < M)
    (hDefect : SmallDefect M d)
    (hEq : E + d + M * 2 = 3 * E')
    (hWrap : M ≤ E') :
    6 * (E' - M) < M := by
  have hDecomp := first_wrap_defect_decomposition hBelow hEq hWrap
  unfold SmallDefect at hDefect
  omega

/-- 初回 wrap の `M/6` bound から、後続不変量に使う `M/4` bound を得る。 -/
theorem first_wrap_overhang_lt_quarter
    {M E d E' : ℕ}
    (hBelow : E < M)
    (hDefect : SmallDefect M d)
    (hEq : E + d + M * 2 = 3 * E')
    (hWrap : M ≤ E') :
    4 * (E' - M) < M := by
  have hSixth := first_wrap_overhang_lt_sixth hBelow hDefect hEq hWrap
  omega

/--
wrap 中に digit `2` が続き、次も wrap 中なら、`M/4` overhang bound は保存される。
-/
theorem wrapped_two_preserves_overhang_lt_quarter
    {M E d E' : ℕ}
    (hWrap : M ≤ E)
    (hOverhang : 4 * (E - M) < M)
    (hDefect : SmallDefect M d)
    (hEq : E + d + M * 2 = 3 * E')
    (hNextWrap : M ≤ E') :
    4 * (E' - M) < M := by
  unfold SmallDefect at hDefect
  omega

/--
`M/4` 未満の一時 wrap 中に digit `0` または `1` が来れば、
次 carry は必ず modulus 未満へ戻る。
-/
theorem wrapped_recovers_of_digit_lt_two
    {M E d a E' : ℕ}
    (hWrap : M ≤ E)
    (hOverhang : 4 * (E - M) < M)
    (hDefect : SmallDefect M d)
    (ha : a < 2)
    (hEq : E + d + M * a = 3 * E') :
    E' < M := by
  unfold SmallDefect at hDefect
  have hCases : a = 0 ∨ a = 1 := by
    omega
  rcases hCases with hZero | hOne
  · subst a
    simp at hEq
    omega
  · subst a
    simp at hEq
    omega

/--
安全状態から一 step 進めても、small-defect row なら安全状態が保存される。

これが「途中 wrap を禁止する」のではなく
「例外 wrap を bounded state として閉じ込める」中心補題。
-/
theorem carrySafeState_step
    {M E d a E' : ℕ}
    (hSafe : CarrySafeState M E)
    (hDefect : SmallDefect M d)
    (ha : a < 3)
    (hEq : E + d + M * a = 3 * E') :
    CarrySafeState M E' := by
  by_cases hBelowNext : E' < M
  · exact Or.inl hBelowNext
  have hNextWrap : M ≤ E' := by
    omega
  rcases hSafe with hBelow | hWrapped
  · have haTwo := first_wrap_digit_eq_two_of_smallDefect
      hBelow hDefect ha hEq hNextWrap
    subst a
    exact Or.inr ⟨hNextWrap,
      first_wrap_overhang_lt_quarter hBelow hDefect hEq hNextWrap⟩
  · rcases hWrapped with ⟨hWrap, hOverhang⟩
    by_cases haTwo : a = 2
    · subst a
      exact Or.inr ⟨hNextWrap,
        wrapped_two_preserves_overhang_lt_quarter
          hWrap hOverhang hDefect hEq hNextWrap⟩
    · have haLtTwo : a < 2 := by
        omega
      have hRecover := wrapped_recovers_of_digit_lt_two
        hWrap hOverhang hDefect haLtTwo hEq
      omega

/--
安全状態から一 step 後も wrap 中なら、その digit は必ず `2`。
これは「terminal wrapped interval は 2-run である」ことの局所形。
-/
theorem digit_eq_two_of_safe_to_wrapped
    {M E d a E' : ℕ}
    (hSafe : CarrySafeState M E)
    (hDefect : SmallDefect M d)
    (ha : a < 3)
    (hEq : E + d + M * a = 3 * E')
    (hNextWrap : M ≤ E') :
    a = 2 := by
  rcases hSafe with hBelow | hWrapped
  · exact first_wrap_digit_eq_two_of_smallDefect
      hBelow hDefect ha hEq hNextWrap
  · rcases hWrapped with ⟨hWrap, hOverhang⟩
    by_contra hNotTwo
    have haLtTwo : a < 2 := by
      omega
    have hRecover := wrapped_recovers_of_digit_lt_two
      hWrap hOverhang hDefect haLtTwo hEq
    omega

namespace CarryRealizes

/--
`CarryRealizes` 全体へ safe-state invariant を持ち上げる。
途中で wrap しても、常に bounded exception の範囲に留まる。
-/
theorem safeState_final
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F)
    (hRows : RowsSmallForModulus M rows)
    (hSafe : CarrySafeState M E) :
    CarrySafeState M F := by
  induction h with
  | nil E =>
      exact hSafe
  | cons R Rs E a E' F digits ha hEq hTail ih =>
      have hDefect : SmallDefect M R.defect :=
        hRows R (by simp)
      have hNextSafe : CarrySafeState M E' :=
        carrySafeState_step hSafe hDefect ha hEq
      have hRowsTail : RowsSmallForModulus M Rs := by
        intro Q hQ
        exact hRows Q (by simp [hQ])
      exact ih hRowsTail hNextSafe

/-- modulus が正なら初期 carry `0` は安全状態。 -/
theorem zero_safeState
    {M : ℕ}
    (hM : 0 < M) :
    CarrySafeState M 0 := by
  exact Or.inl hM

/--
初期 carry `0` から始めた small-defect recurrence の final carry は、
modulus 未満か、`M/4` 未満の bounded wrap のどちらか。
-/
theorem final_below_or_small_wrap
    {M : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes M rows 0 digits F)
    (hM : 0 < M)
    (hRows : RowsSmallForModulus M rows) :
    F < M ∨
      (M ≤ F ∧ 4 * (F - M) < M) := by
  exact h.safeState_final hRows (zero_safeState hM)

/--
H-bit row boundary 条件から直接得る `2^H` 版。
actual first-passage bridge では、この `RowsInsideBitWidth` を供給すればよい。
-/
theorem final_below_or_small_wrap_of_insideBitWidth
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows) :
    F < 2 ^ H ∨
      (2 ^ H ≤ F ∧ 4 * (F - 2 ^ H) < 2 ^ H) := by
  apply h.final_below_or_small_wrap
  · exact pow_pos (by decide : 0 < (2 : ℕ)) H
  · exact rowsSmallForPow_of_insideBitWidth hRows

/--
非空 recurrence が safe state から始まり final wrap で終わるなら、
最後の digit は `2`。

これは terminal wrapped interval の末尾が必ず 2-run に属することを、
carry trace を新しい巨大 structure にせず表した最小の suffix 定理。
-/
theorem final_wrap_endsWithTwo
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F)
    (hRows : RowsSmallForModulus M rows)
    (hSafe : CarrySafeState M E)
    (hFinalWrap : M ≤ F)
    (hNonempty : rows ≠ []) :
    ∃ initDigits : List ℕ, digits = initDigits ++ [2] := by
  induction h with
  | nil E =>
      exact False.elim (hNonempty rfl)
  | cons R Rs E a E' F digits ha hEq hTail ih =>
      have hDefect : SmallDefect M R.defect :=
        hRows R (by simp)
      have hNextSafe : CarrySafeState M E' :=
        carrySafeState_step hSafe hDefect ha hEq
      have hRowsTail : RowsSmallForModulus M Rs := by
        intro Q hQ
        exact hRows Q (by simp [hQ])
      by_cases hTailEmpty : Rs = []
      · subst Rs
        cases hTail
        have haTwo := digit_eq_two_of_safe_to_wrapped
          hSafe hDefect ha hEq hFinalWrap
        subst a
        exact ⟨[], by simp⟩
      · rcases ih hRowsTail hNextSafe hFinalWrap hTailEmpty with
          ⟨initDigits, hInitDigits⟩
        exact ⟨a :: initDigits, by simp [hInitDigits]⟩

/--
初期 carry `0` の H-bit recurrence が final wrap で終わるなら、
最後の digit は必ず `2`。
-/
theorem final_wrap_endsWithTwo_of_insideBitWidth
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows)
    (hFinalWrap : 2 ^ H ≤ F) :
    ∃ initDigits : List ℕ, digits = initDigits ++ [2] := by
  have hNonempty : rows ≠ [] := by
    intro hNil
    subst rows
    cases h
    simp at hFinalWrap
  exact h.final_wrap_endsWithTwo
    (rowsSmallForPow_of_insideBitWidth hRows)
    (zero_safeState (pow_pos (by decide : 0 < (2 : ℕ)) H))
    hFinalWrap
    hNonempty

end CarryRealizes
end CSTCarry
end Collatz3
