import CollatzLean.Collatz2.CSTMicro.Residue

/-!
# General CST as one micro-geometric object

同じ first-passage path `P` から

* Sturmian / Ferrers geometry
* rational endpoint rank
* weighted affine functional `B(P)`
* Archimedean capacity `Cap(P)`
* parity-cylinder representative `R(P)`

を同時に読む。

標準 parity-cylinder theory の最後の bridge
`R(P)` 自身が exact trace を実現することを field として保持し、
その上で

  CST on P
    ↔ B(P) < G(P) * R(P)
    ↔ Cap(P) < R(P)

を証明する。
-/

namespace Collatz2
namespace CSTMicro

/--
一つの general CST micro object。

`representative_exact` は標準 parity cylinder の
canonical representative が実際に同じ parity trace を持つ、
という 2-adic realization bridge。
-/
structure MicroObject where
  path : FirstPassagePath
  representative_exact :
    ∃ y : ℕ,
      ExactRealizes path.word
        (leastRepresentative path.word) y

namespace MicroObject

/-- `B(P)`。 -/
def B (M : MicroObject) : ℕ :=
  affineConst M.path.word

/-- `G(P)=2^k-3^m`。 -/
def G (M : MicroObject) : ℕ :=
  M.path.terminalGap

/-- `R(P)`。 -/
def R (M : MicroObject) : ℕ :=
  leastRepresentative M.path.word

/-- numerical Archimedean capacity `Cap(P)=B/G`。 -/
def Cap (M : MicroObject) : ℕ :=
  M.B / M.G

/--
この path 上の CST statement。

first coefficient crossing の terminal では
すべての exact realization が strict descent する。
-/
def CSTHolds (M : MicroObject) : Prop :=
  ∀ x y : ℕ,
    ExactRealizes M.path.word x y →
      y < x

/--
pure inequality。

2-adic least representative が weighted capacity を越えることを
division-free に書いたもの。
-/
def PureSeparation (M : MicroObject) : Prop :=
  M.B < M.G * M.R

theorem G_pos (M : MicroObject) :
    0 < M.G := by
  exact M.path.terminalGap_pos

/--
general CST on this path は pure separation と同値。
-/
theorem cstHolds_iff_pureSeparation
    (M : MicroObject) :
    M.CSTHolds ↔ M.PureSeparation := by
  constructor
  · intro hCST
    unfold PureSeparation
    rcases M.representative_exact with ⟨y, hy⟩
    have hdesc :
        y < M.R := by
      exact hCST M.R y hy
    by_contra hnot
    have hcap :
        M.G * M.R ≤ M.B := by
      omega
    have hwithin :
        M.path.WithinCapacity M.R := by
      exact hcap
    have hle :
        M.R ≤ y :=
      (FirstPassagePath.start_le_end_iff_withinCapacity_of_exact
        (P := M.path) hy).2 hwithin
    omega
  · intro hsep x y hxy
    unfold PureSeparation at hsep
    have hRle :
        M.R ≤ x :=
      hxy.affine.leastRepresentative_le_start
    have hsep' :
        affineConst M.path.word <
          M.path.terminalGap * M.R := by
      simpa [B, G] using hsep
    have hmul :
        M.path.terminalGap * M.R ≤
          M.path.terminalGap * x :=
      Nat.mul_le_mul_left M.path.terminalGap hRle
    have hnotWithin :
        ¬ M.path.WithinCapacity x := by
      unfold FirstPassagePath.WithinCapacity
      omega
    have hnotLe :
        ¬ x ≤ y := by
      intro hle
      have hwithin :=
        (FirstPassagePath.start_le_end_iff_withinCapacity_of_exact
          (P := M.path) hxy).1 hle
      exact hnotWithin hwithin
    omega

/--
数値 capacity 版。

  PureSeparation
    ↔ Cap(P) < R(P)

したがって `CST ⇔ R(P) > Cap(P)` が得られる。
-/
theorem pureSeparation_iff_capacity_lt_R
    (M : MicroObject) :
    M.PureSeparation ↔ M.Cap < M.R := by
  unfold PureSeparation Cap B G R
  have hG : 0 < M.path.terminalGap :=
    M.path.terminalGap_pos
  constructor
  · intro h
    exact
      (Nat.div_lt_iff_lt_mul hG).2
        (by simpa [Nat.mul_comm] using h)
  · intro h
    have h' :=
      (Nat.div_lt_iff_lt_mul hG).1 h
    simpa [Nat.mul_comm] using h'

/--
要求した最終形:

  CST on P
    ↔ R(P) > Cap(P)
-/
theorem cstHolds_iff_R_gt_Cap
    (M : MicroObject) :
    M.CSTHolds ↔ M.R > M.Cap := by
  rw [M.cstHolds_iff_pureSeparation]
  simpa only [gt_iff_lt] using M.pureSeparation_iff_capacity_lt_R

/--
counterexample があれば必ず parity representative が capacity 以下。

これは `R(P) ≤ Cap(P)` 側への入口。
-/
theorem representative_le_capacity_of_counterexample
    (M : MicroObject)
    {x y : ℕ}
    (hxy : ExactRealizes M.path.word x y)
    (hreturn : x ≤ y) :
    M.R ≤ x ∧ M.path.WithinCapacity x := by
  exact
    ⟨hxy.affine.leastRepresentative_le_start,
      (FirstPassagePath.start_le_end_iff_withinCapacity_of_exact
        (P := M.path) hxy).1 hreturn⟩

end MicroObject
end CSTMicro
end Collatz2
