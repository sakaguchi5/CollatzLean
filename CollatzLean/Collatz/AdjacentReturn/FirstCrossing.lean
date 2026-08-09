import CollatzLean.Collatz.AdjacentReturn.Bounds

/-!
# contracting adjacent return内のfirst crossing

`Nat.find`で値をAPIへ固定せず、first-crossing証人を明示Typeデータとして保持する。
同じadjacent word内のFirstCrossing長は一意なので、このデータは実質的に最小長を表す。
Stateが既に持つfuture-minimum性・非有界性・標準隣接性は再保持せず、
FirstCrossingDataはfirst-crossing固有のlength/crossing情報だけを追加する。
-/

namespace Collatz
namespace AdjacentReturn

/-- contracting adjacent word内のactual first crossing。 -/
structure FirstCrossingData {O : OddOrbit} (R : State O) where
  length : ℕ
  le_adjacent : length ≤ R.length
  crossing : Word.FirstCrossing (R.word.take length)

namespace FirstCrossingData

/-- first-crossing wordの長さ。 -/
@[simp] theorem word_length
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    (R.word.take F.length).length = F.length := by
  apply List.length_take_of_le
  rw [R.word_length]
  exact F.le_adjacent


/-- first-crossing長は正。 -/
theorem length_pos
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    0 < F.length := by
  have hpos :
      0 < (R.word.take F.length).length :=
    List.length_pos_of_ne_nil F.crossing.nonempty
  simpa only [F.word_length] using hpos


/-- first-crossing wordのodd step数。 -/
@[simp] theorem oddSteps_word
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    Word.oddSteps (R.word.take F.length) = F.length := by
  unfold Word.oddSteps
  exact F.word_length


/-- first-crossing wordはactual prefix segmentそのもの。 -/
theorem word_eq_segment
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    R.word.take F.length =
      O.segment R.startIndex F.length := by
  exact R.word_take_eq_segment F.le_adjacent


/-- first-crossing actual prefixの実現式。 -/
theorem realizes
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    Word.Realizes
      (R.word.take F.length)
      R.startValue
      (O.value (R.startIndex + F.length)) := by
  rw [F.word_eq_segment]
  simpa [State.startValue] using
    O.realizesSegment R.startIndex F.length


/-- first-crossing endpoint。 -/
def endpointValue
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : ℕ :=
  O.value (R.startIndex + F.length)


/-- first-crossing return gap。 -/
def returnGap
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : ℕ :=
  F.endpointValue - R.startValue


/-- first-crossing総2進指数。 -/
def totalExponent
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : ℕ :=
  Word.twoSteps (R.word.take F.length)


/-- contracting multiplicative gap `2^H-3^p`。 -/
def multiplicativeGap
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : ℕ :=
  2 ^ F.totalExponent - 3 ^ F.length


/-- first-crossing affine定数。 -/
def affine
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : ℕ :=
  Word.affineConst (R.word.take F.length)

/-- Stateのfuture-minimum性によりfirst-crossing endpointは開始値以上。 -/
theorem start_le_endpoint
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    R.startValue ≤ F.endpointValue := by
  exact R.startFutureMinimum.le_segment_end F.length

/-- 非有界軌道ではfirst-crossing endpointは開始値より真に大きい。 -/
theorem start_lt_endpoint
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    R.startValue < F.endpointValue := by
  have hle := F.start_le_endpoint
  have hne : R.startValue ≠ F.endpointValue := by
    unfold State.startValue endpointValue
    exact O.value_ne_of_lt_of_unbounded R.unbounded (by
      have := F.length_pos
      omega)
  omega

/-- return gapは正。 -/
theorem returnGap_pos
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    0 < F.returnGap := by
  unfold returnGap
  exact Nat.sub_pos_of_lt F.start_lt_endpoint

/-- adjacent値差はfirst-crossing return gap以下。 -/
theorem valueGap_le_returnGap
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    R.valueGap ≤ F.returnGap := by
  unfold returnGap endpointValue
  exact R.valueGap_le_endpointGap F.length_pos F.start_le_endpoint

/-- first-crossing return gapは少なくとも4。 -/
theorem four_le_returnGap
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    4 ≤ F.returnGap :=
  le_trans R.four_le_valueGap F.valueGap_le_returnGap

/-- 同じadjacent state内のFirstCrossing長は一意。 -/
theorem length_unique
    {O : OddOrbit} {R : State O}
    (F G : FirstCrossingData R) :
    F.length = G.length := by
  rcases lt_trichotomy F.length G.length with hFG | hEq | hGF
  · have hExp :
        Word.Expanding
          ((R.word.take G.length).take F.length) := by
      apply G.crossing.properExpanding F.length F.length_pos
      rw [G.word_length]
      exact hFG
    have hExp' :
        Word.Expanding (R.word.take F.length) := by
      simpa [
        List.take_take,
        Nat.min_eq_left (Nat.le_of_lt hFG)
      ] using hExp
    have hCon :
        Word.Contracting (R.word.take F.length) :=
      F.crossing.terminalContracting
    change
      2 ^ Word.twoSteps (R.word.take F.length) <
        3 ^ Word.oddSteps (R.word.take F.length)
      at hExp'
    change
      3 ^ Word.oddSteps (R.word.take F.length) <
        2 ^ Word.twoSteps (R.word.take F.length)
      at hCon
    omega
  · exact hEq
  · have hExp :
        Word.Expanding
          ((R.word.take F.length).take G.length) := by
      apply F.crossing.properExpanding G.length G.length_pos
      rw [F.word_length]
      exact hGF
    have hExp' :
        Word.Expanding (R.word.take G.length) := by
      simpa [
        List.take_take,
        Nat.min_eq_left (Nat.le_of_lt hGF)
      ] using hExp
    have hCon :
        Word.Contracting (R.word.take G.length) :=
      G.crossing.terminalContracting
    change
      2 ^ Word.twoSteps (R.word.take G.length) <
        3 ^ Word.oddSteps (R.word.take G.length)
      at hExp'
    change
      3 ^ Word.oddSteps (R.word.take G.length) <
        2 ^ Word.twoSteps (R.word.take G.length)
      at hCon
    omega

/-- first crossingはadjacent全長exactか、その手前late。 -/
theorem exact_or_late
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    F.length = R.length ∨ F.length < R.length := by
  rcases lt_or_eq_of_le F.le_adjacent with hlt | heq
  · exact Or.inr hlt
  · exact Or.inl heq

/-- exact-adjacency。 -/
def IsExact {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : Prop :=
  F.length = R.length

/-- late-next-minimum。 -/
def IsLate {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : Prop :=
  F.length < R.length

end FirstCrossingData

namespace State

/-- contracting adjacent stateはFirstCrossingDataを持つ。 -/
theorem existsFirstCrossingData
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    Nonempty (FirstCrossingData R) := by
  obtain ⟨p, hp, hCross⟩ := R.existsFirstCrossing hC
  exact ⟨⟨p, hp, hCross⟩⟩

end State

/-- contracting towerの各項にfirst-crossing証人を付けたTypeデータ。 -/
structure ContractingFirstCrossingTower
    {O : OddOrbit} (T : ContractingTower O) where
  crossing : ∀ n : ℕ, FirstCrossingData (T.tower_at n)

namespace ContractingFirstCrossingTower

/-- tower第n項のfirst crossing。 -/
def tower_at
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) (n : ℕ) :
    FirstCrossingData (T.tower_at n) := F.crossing n

/-- 第n項のfirst-crossing長。 -/
def length
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) (n : ℕ) : ℕ :=
  (F.tower_at n).length

/-- exact項。 -/
def ExactAt
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) (n : ℕ) : Prop :=
  (F.tower_at n).IsExact

/-- late項。 -/
def LateAt
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) (n : ℕ) : Prop :=
  (F.tower_at n).IsLate

/-- 各項はexactまたはlate。 -/
theorem exact_or_late
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) (n : ℕ) :
    F.ExactAt n ∨ F.LateAt n := by
  exact (F.tower_at n).exact_or_late

end ContractingFirstCrossingTower

namespace ContractingTower

/-- contracting towerには項ごとのfirst crossingを同時に付けられる。 -/
theorem existsFirstCrossingTower
    {O : OddOrbit} (T : ContractingTower O) :
    Nonempty (ContractingFirstCrossingTower T) := by
  classical
  have h : ∀ n : ℕ, Nonempty (FirstCrossingData (T.tower_at n)) := by
    intro n
    exact (T.tower_at n).existsFirstCrossingData (T.at_contracting n)
  exact ⟨⟨fun n => Classical.choice (h n)⟩⟩

end ContractingTower

end AdjacentReturn
end Collatz
