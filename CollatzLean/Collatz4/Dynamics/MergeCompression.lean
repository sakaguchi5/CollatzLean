import CollatzLean.Collatz4.Dynamics.SynchronizedMerge

/-!
# Collatz4.Dynamics.MergeCompression

多数の時刻付き累積 Collatz 軌道を、少数の代表軌道へ圧縮するための一般層。

候補型 `ι`、代表型 `ρ`、共通終端時刻 `T` を固定する。
各候補 `i : ι` に代表 `representativeOf i : ρ` を割り当て、候補軌道が
その代表軌道へ時刻 `T` までに同期合流することを保持する。

この構造を一度作れば、終端時刻 `T` での候補値は対応する代表値と必ず一致する。
したがって終点に関する任意の性質は、代表についてだけ証明すれば全候補へ転送できる。

ここには `3^n-1` や M 固有定数を置かない。
-/

namespace Collatz4.Dynamics

/--
時刻付き累積軌道の代表圧縮 certificate。

`candidateStart` / `candidateInitial` が元候補、
`representativeStart` / `representativeInitial` が代表軌道を表す。
-/
structure SynchronizedCompression (ι ρ : Type) (T : ℕ) where
  candidateStart : ι → ℕ
  candidateInitial : ι → ℕ
  representativeStart : ρ → ℕ
  representativeInitial : ρ → ℕ
  representativeOf : ι → ρ
  merges : ∀ i : ι,
    SynchronizedMergesBy T
      (candidateStart i) (candidateInitial i)
      (representativeStart (representativeOf i))
      (representativeInitial (representativeOf i))

namespace SynchronizedCompression

/-- 候補 `i` の終端時刻 `T` における値。 -/
def candidateTerminal
    {ι ρ : Type} {T : ℕ}
    (C : SynchronizedCompression ι ρ T) (i : ι) : ℕ :=
  accumulatedAt (C.candidateStart i) T (C.candidateInitial i)

/-- 代表 `r` の終端時刻 `T` における値。 -/
def representativeTerminal
    {ι ρ : Type} {T : ℕ}
    (C : SynchronizedCompression ι ρ T) (r : ρ) : ℕ :=
  accumulatedAt (C.representativeStart r) T (C.representativeInitial r)

/--
圧縮 certificate がある候補は、終端時刻で対応する代表と正確に一致する。
-/
theorem candidateTerminal_eq_representative
    {ι ρ : Type} {T : ℕ}
    (C : SynchronizedCompression ι ρ T) (i : ι) :
    C.candidateTerminal i =
      C.representativeTerminal (C.representativeOf i) := by
  exact accumulatedAt_eq_of_synchronizedMergesBy (C.merges i)

/--
代表終点がすべて性質 `P` を満たすなら、元候補の終点もすべて `P` を満たす。

合流圧縮後に代表だけを検証すればよいことの一般的な転送定理。
-/
theorem terminal_property_of_representatives
    {ι ρ : Type} {T : ℕ}
    (C : SynchronizedCompression ι ρ T)
    (P : ℕ → Prop)
    (hrep : ∀ r : ρ, P (C.representativeTerminal r)) :
    ∀ i : ι, P (C.candidateTerminal i) := by
  intro i
  rw [C.candidateTerminal_eq_representative i]
  exact hrep (C.representativeOf i)

/--
ある候補終点が値 `z` なら、その候補に対応する代表終点も同じ `z` である。
-/
theorem representative_of_candidate_terminal_eq
    {ι ρ : Type} {T z : ℕ}
    (C : SynchronizedCompression ι ρ T)
    {i : ι}
    (hi : C.candidateTerminal i = z) :
    C.representativeTerminal (C.representativeOf i) = z := by
  rw [← C.candidateTerminal_eq_representative i]
  exact hi

/--
候補終点として現れる値は、必ず代表終点としても現れる。

終点集合の包含を `Set` を導入せず存在量化だけで表した形。
-/
theorem exists_representative_of_exists_candidate_terminal
    {ι ρ : Type} {T z : ℕ}
    (C : SynchronizedCompression ι ρ T)
    (h : ∃ i : ι, C.candidateTerminal i = z) :
    ∃ r : ρ, C.representativeTerminal r = z := by
  rcases h with ⟨i, hi⟩
  exact ⟨C.representativeOf i,
    C.representative_of_candidate_terminal_eq hi⟩

end SynchronizedCompression

end Collatz4.Dynamics
