import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBPositiveComponentEndpoint

/-!
# MultiCorner: terminal last-two exposed normal form

`card E ≥ 2` branch で terminal exposed cut の直前にある最後の exposed cut を
canonical に取り出すための層。

ここでは exposed を depth drop と同一視しない。exposed の本体は
`profileRunGap ≥ 2` という checkpoint jump である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- `t` より左にある exposed predecessor の有限集合。 -/
noncomputable def exposedBelow
    (P : PureBProfileObstruction)
    (t : ℕ) : Finset ℕ := by
  classical
  exact P.exposedPredecessorSet.filter (fun k => k < t)

@[simp] theorem mem_exposedBelow_iff
    (P : PureBProfileObstruction)
    {t k : ℕ} :
    k ∈ exposedBelow P t ↔
      k ∈ P.exposedPredecessorSet ∧ k < t := by
  classical
  simp [exposedBelow]

/-- `t` より左の exposed 集合が nonempty のとき、その最大要素。 -/
noncomputable def previousExposedIndex
    (P : PureBProfileObstruction)
    (t : ℕ)
    (hNE : (exposedBelow P t).Nonempty) : ℕ :=
  (exposedBelow P t).max' hNE

/-- canonical previous exposed は実際に `t` より左の exposed 集合に属する。 -/
theorem previousExposedIndex_mem_exposedBelow
    (P : PureBProfileObstruction)
    (t : ℕ)
    (hNE : (exposedBelow P t).Nonempty) :
    previousExposedIndex P t hNE ∈ exposedBelow P t := by
  classical
  exact Finset.max'_mem _ _

/-- canonical previous exposed は global exposed set に属する。 -/
theorem previousExposedIndex_mem_exposedPredecessorSet
    (P : PureBProfileObstruction)
    (t : ℕ)
    (hNE : (exposedBelow P t).Nonempty) :
    previousExposedIndex P t hNE ∈ P.exposedPredecessorSet := by
  have hMem := (mem_exposedBelow_iff P).1
    (previousExposedIndex_mem_exposedBelow P t hNE)
  exact hMem.1

/-- canonical previous exposed は terminal cut より strict に左にある。 -/
theorem previousExposedIndex_lt
    (P : PureBProfileObstruction)
    (t : ℕ)
    (hNE : (exposedBelow P t).Nonempty) :
    previousExposedIndex P t hNE < t := by
  have hMem := (mem_exposedBelow_iff P).1
    (previousExposedIndex_mem_exposedBelow P t hNE)
  exact hMem.2

/-- `t` より左の任意 exposed は canonical previous exposed 以下。 -/
theorem le_previousExposedIndex_of_mem_exposedBelow
    (P : PureBProfileObstruction)
    (t : ℕ)
    (hNE : (exposedBelow P t).Nonempty)
    {k : ℕ}
    (hk : k ∈ exposedBelow P t) :
    k ≤ previousExposedIndex P t hNE := by
  classical
  exact Finset.le_max' _ _ hk

/-- canonical previous exposed と terminal cut の間には exposed は存在しない。 -/
theorem no_exposed_between_previous_and_terminal
    (P : PureBProfileObstruction)
    (t : ℕ)
    (hNE : (exposedBelow P t).Nonempty)
    {k : ℕ}
    (ha : previousExposedIndex P t hNE < k)
    (hkt : k < t) :
    k ∉ P.exposedPredecessorSet := by
  intro hk
  have hkBelow : k ∈ exposedBelow P t :=
    (mem_exposedBelow_iff P).2 ⟨hk, hkt⟩
  have hle := le_previousExposedIndex_of_mem_exposedBelow P t hNE hkBelow
  omega

/-- terminal 側の最後の二つの exposed cuts をまとめた normal-form packet。 -/
structure LastTwoExposedNormalForm
    (P : PureBProfileObstruction) where
  previous : ℕ
  terminal : ℕ
  previous_mem : previous ∈ P.exposedPredecessorSet
  terminal_mem : terminal ∈ P.exposedPredecessorSet
  previous_lt_terminal : previous < terminal
  no_exposed_between :
    ∀ k : ℕ,
      previous < k →
      k < terminal →
      k ∉ P.exposedPredecessorSet

/-- terminal cut とその左側 nonempty exposed 集合から normal form を構成する。 -/
noncomputable def lastTwoExposedNormalForm
    (P : PureBProfileObstruction)
    (t : ℕ)
    (hTerminal : t ∈ P.exposedPredecessorSet)
    (hNE : (exposedBelow P t).Nonempty) :
    LastTwoExposedNormalForm P :=
  { previous := previousExposedIndex P t hNE
    terminal := t
    previous_mem := previousExposedIndex_mem_exposedPredecessorSet P t hNE
    terminal_mem := hTerminal
    previous_lt_terminal := previousExposedIndex_lt P t hNE
    no_exposed_between := by
      intro k hak hkt
      exact no_exposed_between_previous_and_terminal P t hNE hak hkt }

/-- exposed index は terminal critical suffix の開始より strict に左にある。 -/
theorem exposed_lt_terminalCriticalStart
    (P : PureBProfileObstruction)
    {k : ℕ}
    (E : P.IsExposedPredecessorIndex k) :
    k < P.terminalCriticalStart := by
  by_contra hnot
  have hge : P.terminalCriticalStart ≤ k := by omega
  have hzero :=
    P.terminalCriticalStart_spec.2 k hge E.lt_m
  exact (Nat.ne_of_gt E.depth_pos) hzero

/-- `c>0` なら任意 exposed cut は terminal predecessor `c-1` 以下。 -/
theorem exposed_le_terminalPred
    (P : PureBProfileObstruction)
    (hc : 0 < P.terminalCriticalStart)
    {k : ℕ}
    (E : P.IsExposedPredecessorIndex k) :
    k ≤ P.terminalCriticalStart - 1 := by
  have hlt := exposed_lt_terminalCriticalStart P E
  omega

/--
`card E ≥ 2` なら terminal predecessor より strict に左にも exposed が存在する。
terminal critical suffix より右には positive column がないことだけを使う。
-/
theorem exposedBelow_terminalPred_nonempty_of_card_ge_two
    (P : PureBProfileObstruction)
    (hc : 0 < P.terminalCriticalStart)
    (hCard : 2 ≤ P.exposedPredecessorSet.card) :
    (exposedBelow P (P.terminalCriticalStart - 1)).Nonempty := by
  classical
  by_contra hNE
  have hSub :
      P.exposedPredecessorSet ⊆
        ({P.terminalCriticalStart - 1} : Finset ℕ) := by
    intro k hk
    have E : P.IsExposedPredecessorIndex k :=
      (P.mem_exposedPredecessorSet_iff).1 hk
    have hle := exposed_le_terminalPred P hc E
    have hEq : k = P.terminalCriticalStart - 1 := by
      by_contra hne
      have hlt : k < P.terminalCriticalStart - 1 := by omega
      have hkBelow :
          k ∈ exposedBelow P (P.terminalCriticalStart - 1) :=
        (mem_exposedBelow_iff P).2 ⟨hk, hlt⟩
      exact hNE ⟨k, hkBelow⟩
    simp [hEq]
  have hCardLe := Finset.card_le_card hSub
  have hAtMostOne : P.exposedPredecessorSet.card ≤ 1 := by
    simpa using hCardLe
  omega

/--
terminal predecessor 自身が exposed で `card E ≥ 2` なら、
terminal 側の last-two exposed normal form が canonical に得られる。
-/
noncomputable def terminalLastTwoExposedNormalForm
    (P : PureBProfileObstruction)
    (hc : 0 < P.terminalCriticalStart)
    (hTerminal :
      P.terminalCriticalStart - 1 ∈ P.exposedPredecessorSet)
    (hCard : 2 ≤ P.exposedPredecessorSet.card) :
    LastTwoExposedNormalForm P :=
  lastTwoExposedNormalForm
    P
    (P.terminalCriticalStart - 1)
    hTerminal
    (exposedBelow_terminalPred_nonempty_of_card_ge_two P hc hCard)

/--
actual minimal B packet では既存の terminal-exposed theorem を使って
last-two normal form を直接構成できる。
-/
noncomputable def actualTerminalLastTwoExposedNormalForm
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      2 ≤ (M.toPureBProfileObstruction hL).exposedPredecessorSet.card) :
    LastTwoExposedNormalForm (M.toPureBProfileObstruction hL) := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  have hc : 0 < P.terminalCriticalStart := by
    have hLe := P.criticalizationStart_le_terminalCriticalStart
    omega
  have hTerminal :
      P.terminalCriticalStart - 1 ∈ P.exposedPredecessorSet := by
    simpa [P] using M.terminalPred_mem_exposedPredecessorSet R hL
  have hCardP : 2 ≤ P.exposedPredecessorSet.card := by
    simpa [P] using hCard
  simpa [P] using
    terminalLastTwoExposedNormalForm P hc hTerminal hCardP

/-- terminal positive component の開始 `b` に対する二分岐。 -/
inductive TerminalCornerPlacement (a b : ℕ) : Prop
  | attached (h : b ≤ a) : TerminalCornerPlacement a b
  | restarted (h : a < b) : TerminalCornerPlacement a b

/-- previous exposed `a` と component start `b` は attached / restarted のどちらか。 -/
theorem terminalCornerPlacement_total
    (a b : ℕ) :
    TerminalCornerPlacement a b := by
  by_cases h : b ≤ a
  · exact TerminalCornerPlacement.attached h
  · exact TerminalCornerPlacement.restarted (by omega)

end MultiCorner
end CSTMicro
end Collatz2
