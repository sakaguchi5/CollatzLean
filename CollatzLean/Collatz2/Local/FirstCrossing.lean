import CollatzLean.Collatz2.Local.Defect


/-!
# Collatz2: first determinant-sign crossing

FirstCrossing を primitive な orbit object として置かない。
非空 word の prefix determinant が正で進み、terminal で初めて負になるという
transfer sign profile の特殊形として定義する。
-/

namespace Collatz2
namespace Word

/-- 全 nonempty proper prefix の determinant が正。 -/
def ProperPrefixesPositiveDeterminant (w : Word) : Prop :=
  ∀ k : ℕ, 0 < k → k < w.length →
    AffineTransfer.PositiveDeterminant
      (AffineTransfer.ofWord (w.take k))

/--
first crossing は prefix determinant profile の最初の `+ -> -` crossing。
新しい算術量は保持しない。
-/
structure FirstCrossing (w : Word) : Prop where
  nonempty : w ≠ []
  properPositive : ProperPrefixesPositiveDeterminant w
  terminalNegative :
    AffineTransfer.NegativeDeterminant (AffineTransfer.ofWord w)

namespace FirstCrossing

/-- proper prefix の従来名は Expanding のコロラリー。 -/
theorem properExpanding
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < w.length) :
    Expanding (w.take k) := by
  exact hF.properPositive k hkPos hkLt

/-- terminal の従来名は Contracting のコロラリー。 -/
theorem terminalContracting
    {w : Word}
    (hF : FirstCrossing w) :
    Contracting w := by
  exact hF.terminalNegative

end FirstCrossing

/--
contracting valid nonempty word には最初の determinant-sign crossing が存在する。
-/
theorem exists_firstCrossing_of_contracting
    {w : Word}
    (hvalid : Valid w)
    (hne : w ≠ [])
    (hC : Contracting w) :
    ∃ p : ℕ, p ≤ w.length ∧ FirstCrossing (w.take p) := by
  classical
  let Bad : ℕ → Prop := fun p =>
    0 < p ∧ p ≤ w.length ∧ ¬ Expanding (w.take p)
  have hlen : 0 < w.length := List.length_pos_iff.mpr hne
  have hnotExpanding : ¬ Expanding w := by
    intro hE
    exact (not_expanding_and_contracting w) ⟨hE, hC⟩
  have hbad : ∃ p : ℕ, Bad p := by
    refine ⟨w.length, hlen, le_rfl, ?_⟩
    simpa using hnotExpanding
  let p := Nat.find hbad
  have hpBad : Bad p := Nat.find_spec hbad
  have hpPos : 0 < p := hpBad.1
  have hpLe : p ≤ w.length := hpBad.2.1
  have hpNotExpanding : ¬ Expanding (w.take p) := hpBad.2.2
  have hlenTake : (w.take p).length = p := List.length_take_of_le hpLe
  have htakeNonempty : w.take p ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hlenTake]
    exact hpPos
  have htakeValid : Valid (w.take p) := by
    have hwhole : Valid (w.take p ++ w.drop p) := by
      simpa using hvalid
    exact hwhole.prefix
  have htakeContracting : Contracting (w.take p) :=
    (expanding_or_contracting_of_valid_nonempty
      htakeValid htakeNonempty).resolve_left hpNotExpanding
  have hproper : ProperPrefixesPositiveDeterminant (w.take p) := by
    intro q hqPos hqLtTake
    have hqLt : q < p := by
      rw [hlenTake] at hqLtTake
      exact hqLtTake
    by_contra hqNot
    have hqLeW : q ≤ w.length := by omega
    have htakeTake : (w.take p).take q = w.take q := by
      simp [List.take_take, Nat.min_eq_left (Nat.le_of_lt hqLt)]
    have hqNotExpanding : ¬ Expanding (w.take q) := by
      simpa [Expanding, htakeTake] using hqNot
    have hqBad : Bad q := ⟨hqPos, hqLeW, hqNotExpanding⟩
    have hmin : p ≤ q := by
      dsimp [p]
      exact Nat.find_min' hbad hqBad
    omega
  exact ⟨p, hpLe, {
    nonempty := htakeNonempty
    properPositive := hproper
    terminalNegative := htakeContracting
  }⟩

end Word
end Collatz2
