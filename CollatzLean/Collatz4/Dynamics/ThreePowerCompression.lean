import CollatzLean.Collatz4.Dynamics.MergeCompression

/-!
# Collatz4.Dynamics.ThreePowerCompression

`3^n - 1` を時刻 `n` から開始する標準候補族に対して、
`SynchronizedCompression` を使いやすい形へ特殊化する。

各候補指数 `candidateN i` に代表指数 `representativeN (representativeOf i)` を割り当て、
両者が共通終端時刻 `T` までに同期合流することを certificate として保持する。

M=7 の `2179 -> 97` のような圧縮は、この構造の具体例として置く。
ここ自体には M 固有定数も代表数も置かない。
-/

namespace Collatz4.Dynamics

/-- `3^n-1` 候補族の代表圧縮 certificate。 -/
structure ThreePowerCompression (ι ρ : Type) (T : ℕ) where
  candidateN : ι → ℕ
  representativeN : ρ → ℕ
  representativeOf : ι → ρ
  merges : ∀ i : ι,
    ThreePowerMergesBy T
      (candidateN i)
      (representativeN (representativeOf i))

namespace ThreePowerCompression

/-- 一般の同期圧縮構造として読む。 -/
def toSynchronizedCompression
    {ι ρ : Type} {T : ℕ}
    (C : ThreePowerCompression ι ρ T) :
    SynchronizedCompression ι ρ T where
  candidateStart := C.candidateN
  candidateInitial := fun i => 3 ^ C.candidateN i - 1
  representativeStart := C.representativeN
  representativeInitial := fun r => 3 ^ C.representativeN r - 1
  representativeOf := C.representativeOf
  merges := C.merges

/-- 候補 `i` の共通終端時刻 `T` における値。 -/
def candidateTerminal
    {ι ρ : Type} {T : ℕ}
    (C : ThreePowerCompression ι ρ T) (i : ι) : ℕ :=
  threePowerAt (C.candidateN i) T

/-- 代表 `r` の共通終端時刻 `T` における値。 -/
def representativeTerminal
    {ι ρ : Type} {T : ℕ}
    (C : ThreePowerCompression ι ρ T) (r : ρ) : ℕ :=
  threePowerAt (C.representativeN r) T

/--
各候補の終点は、割り当てられた代表の終点と正確に一致する。
-/
theorem candidateTerminal_eq_representative
    {ι ρ : Type} {T : ℕ}
    (C : ThreePowerCompression ι ρ T) (i : ι) :
    C.candidateTerminal i =
      C.representativeTerminal (C.representativeOf i) := by
  exact threePowerAt_eq_of_mergesBy (C.merges i)

/--
代表終点について性質 `P` を証明すれば、全候補終点にも同じ性質が成り立つ。
-/
theorem terminal_property_of_representatives
    {ι ρ : Type} {T : ℕ}
    (C : ThreePowerCompression ι ρ T)
    (P : ℕ → Prop)
    (hrep : ∀ r : ρ, P (C.representativeTerminal r)) :
    ∀ i : ι, P (C.candidateTerminal i) := by
  intro i
  rw [C.candidateTerminal_eq_representative i]
  exact hrep (C.representativeOf i)

/--
候補終点として値 `z` が現れるなら、代表終点としても `z` が現れる。
-/
theorem exists_representative_of_exists_candidate_terminal
    {ι ρ : Type} {T z : ℕ}
    (C : ThreePowerCompression ι ρ T)
    (h : ∃ i : ι, C.candidateTerminal i = z) :
    ∃ r : ρ, C.representativeTerminal r = z := by
  rcases h with ⟨i, hi⟩
  refine ⟨C.representativeOf i, ?_⟩
  rw [← C.candidateTerminal_eq_representative i]
  exact hi

/--
代表の 2 進指数がすべて開区間 `(lower, upper)` の外側なら、
元候補についても同じ禁止帯が成立する。

`OutsideOpenInterval` には依存せず、論理形を直接公開する。
-/
theorem terminal_v2_gap_of_representatives
    {ι ρ : Type} {T lower upper : ℕ}
    (C : ThreePowerCompression ι ρ T)
    (hrep : ∀ r : ρ,
      accumulatedV2 (C.representativeTerminal r) ≤ lower ∨
        upper ≤ accumulatedV2 (C.representativeTerminal r)) :
    ∀ i : ι,
      accumulatedV2 (C.candidateTerminal i) ≤ lower ∨
        upper ≤ accumulatedV2 (C.candidateTerminal i) := by
  intro i
  rw [C.candidateTerminal_eq_representative i]
  exact hrep (C.representativeOf i)

end ThreePowerCompression

end Collatz4.Dynamics
