import CollatzLean.CollatzSecondLayer.ChainOutcomes

/-!
# bounded depthからlong synchronization driftへ

軌道固有の部分と純粋な無限列論を分離する。
同じ最小同期長が再び現れるたびdepthが真に増える、という局所法則から、
depthが有界なら同期長が任意の固定値を最終的に越えることを証明する。
-/

namespace CollatzSecondLayer

/-- 値`m`が数列`f`に任意に遠く現れること。 -/
def RecurrentValue (f : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ f n = m

/-- 再帰しない値は、ある位置以後には現れない。 -/
theorem eventually_ne_of_not_recurrent
    (f : ℕ → ℕ)
    (m : ℕ)
    (h : ¬ RecurrentValue f m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≠ m := by
  unfold RecurrentValue at h
  push Not at h
  exact h

/--
ある有限上界以下の値が任意に遠く現れるなら、その有限集合のどれか一値が
任意に遠く現れる。
-/
theorem exists_recurrent_value_of_cofinally_bounded
    (f : ℕ → ℕ) :
    ∀ M : ℕ,
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ f n ≤ M) →
      ∃ m : ℕ, m ≤ M ∧ RecurrentValue f m := by
  intro M
  induction M with
  | zero =>
      intro h
      refine ⟨0, le_rfl, ?_⟩
      intro N
      obtain ⟨n, hn, hzero⟩ := h N
      exact ⟨n, hn, by omega⟩
  | succ M ih =>
      intro h
      by_cases htop : RecurrentValue f (M + 1)
      · exact ⟨M + 1, le_rfl, htop⟩
      · obtain ⟨Ntop, hNtop⟩ :=
          eventually_ne_of_not_recurrent f (M + 1) htop
        have hsmall :
            ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ f n ≤ M := by
          intro N
          obtain ⟨n, hn, hbound⟩ := h (max N Ntop)
          have hnN : N ≤ n :=
            le_trans (le_max_left _ _) hn
          have hnTop : Ntop ≤ n :=
            le_trans (le_max_right _ _) hn
          have hne := hNtop n hnTop
          refine ⟨n, hnN, ?_⟩
          omega
        obtain ⟨m, hm, hrec⟩ := ih hsmall
        exact ⟨m, Nat.le_trans hm (Nat.le_succ M), hrec⟩

/-- 最小再帰値より小さい値が再帰しなければ、最終的に数列はその値以上。 -/
theorem eventually_ge_of_no_smaller_recurrent
    (f : ℕ → ℕ) :
    ∀ m : ℕ,
      (∀ r : ℕ, r < m → ¬ RecurrentValue f r) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m ≤ f n := by
  intro m
  induction m with
  | zero =>
      intro _
      exact ⟨0, by intro n hn; omega⟩
  | succ m ih =>
      intro hsmall
      have hbelow :
          ∀ r : ℕ, r < m → ¬ RecurrentValue f r := by
        intro r hr
        exact hsmall r (by omega)
      obtain ⟨N₁, hN₁⟩ := ih hbelow
      have hmNot : ¬ RecurrentValue f m :=
        hsmall m (by omega)
      obtain ⟨N₂, hN₂⟩ :=
        eventually_ne_of_not_recurrent f m hmNot
      refine ⟨max N₁ N₂, ?_⟩
      intro n hn
      have hmle : m ≤ f n :=
        hN₁ n (le_trans (le_max_left _ _) hn)
      have hmne : f n ≠ m :=
        hN₂ n (le_trans (le_max_right _ _) hn)
      omega

/-- 再帰値`m`の、閾値`N`以後で最初の出現位置。 -/
noncomputable def firstOccurrenceAfter
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N : ℕ) : ℕ :=
  Nat.find (hrec N)

/-- 最初の出現位置は閾値以後で、値は`m`。 -/
theorem firstOccurrenceAfter_spec
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N : ℕ) :
    N ≤ firstOccurrenceAfter f m hrec N ∧
      f (firstOccurrenceAfter f m hrec N) = m := by
  unfold firstOccurrenceAfter
  exact Nat.find_spec (hrec N)

/-- 閾値と最初の出現位置の間には`m`は現れない。 -/
theorem firstOccurrenceAfter_minimal
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N t : ℕ)
    (hNt : N ≤ t)
    (ht : t < firstOccurrenceAfter f m hrec N) :
    f t ≠ m := by
  intro htm
  have hnot := Nat.find_min (hrec N) ht
  exact hnot ⟨hNt, htm⟩

/-- 再帰値の連続出現位置列。 -/
noncomputable def recurrentOccurrence
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N₀ : ℕ) : ℕ → ℕ
  | 0 => firstOccurrenceAfter f m hrec N₀
  | j + 1 =>
      firstOccurrenceAfter f m hrec
        (recurrentOccurrence f m hrec N₀ j + 1)

/-- 各選択位置で値は`m`。 -/
theorem recurrentOccurrence_value
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N₀ j : ℕ) :
    f (recurrentOccurrence f m hrec N₀ j) = m := by
  cases j with
  | zero =>
      exact (firstOccurrenceAfter_spec f m hrec N₀).2
  | succ j =>
      exact
        (firstOccurrenceAfter_spec f m hrec
          (recurrentOccurrence f m hrec N₀ j + 1)).2

/-- 連続出現位置は一段ごとに増える。 -/
theorem recurrentOccurrence_lt_succ
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N₀ j : ℕ) :
    recurrentOccurrence f m hrec N₀ j <
      recurrentOccurrence f m hrec N₀ (j + 1) := by
  have h :=
    (firstOccurrenceAfter_spec f m hrec
      (recurrentOccurrence f m hrec N₀ j + 1)).1
  simpa [recurrentOccurrence] using h

/-- 連続出現位置列は狭義単調。 -/
theorem recurrentOccurrence_strict
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N₀ : ℕ) :
    StrictMono (recurrentOccurrence f m hrec N₀) :=
  strictMono_nat_of_lt_succ
    (recurrentOccurrence_lt_succ f m hrec N₀)

/-- 最初の選択位置は初期閾値以後。 -/
theorem recurrentOccurrence_zero_ge
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N₀ : ℕ) :
    N₀ ≤ recurrentOccurrence f m hrec N₀ 0 :=
  (firstOccurrenceAfter_spec f m hrec N₀).1

/-- 連続する選択位置の間には`m`は現れない。 -/
theorem recurrentOccurrence_between_ne
    (f : ℕ → ℕ)
    (m : ℕ)
    (hrec : RecurrentValue f m)
    (N₀ j t : ℕ)
    (hleft : recurrentOccurrence f m hrec N₀ j < t)
    (hright : t < recurrentOccurrence f m hrec N₀ (j + 1)) :
    f t ≠ m := by
  apply firstOccurrenceAfter_minimal
    f m hrec
    (recurrentOccurrence f m hrec N₀ j + 1)
  · omega
  · simpa [recurrentOccurrence] using hright

/--
同期長とprepared depthの抽象列。
`depthGrowth`は、同じ同期長が二度現れ、その間の同期長がすべて真に大きいなら、
後のdepthが真に増えるというorbit由来の局所法則である。
-/
structure SynchronizationCarrySequence where
  syncLength : ℕ → ℕ
  depth : ℕ → ℕ
  depthGrowth :
    ∀ {k l m : ℕ},
      k < l →
      syncLength k = m →
      syncLength l = m →
      (∀ t : ℕ, k < t → t < l → m < syncLength t) →
      depth k < depth l

namespace SynchronizationCarrySequence

/--
depthが一様有界なら、同期長は任意の固定値を最終的に越える。
-/
theorem syncLength_tendsto_of_depth_bounded
    (D : SynchronizationCarrySequence)
    (B : ℕ)
    (hdepth : ∀ n : ℕ, D.depth n ≤ B) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M < D.syncLength n := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨M, hM⟩ := hnot
  obtain ⟨m₀, hm₀M, hm₀rec⟩ :=
    exists_recurrent_value_of_cofinally_bounded
      D.syncLength M hM
  let m := Nat.find
    (show ∃ r : ℕ, RecurrentValue D.syncLength r from
      ⟨m₀, hm₀rec⟩)
  have hmrec : RecurrentValue D.syncLength m := by
    dsimp [m]
    exact Nat.find_spec
      (show ∃ r : ℕ, RecurrentValue D.syncLength r from
        ⟨m₀, hm₀rec⟩)
  have hminimal :
      ∀ r : ℕ, r < m → ¬ RecurrentValue D.syncLength r := by
    intro r hr
    exact Nat.find_min
      (show ∃ q : ℕ, RecurrentValue D.syncLength q from
        ⟨m₀, hm₀rec⟩)
      hr
  obtain ⟨N₀, hN₀⟩ :=
    eventually_ge_of_no_smaller_recurrent
      D.syncLength m hminimal
  let occ := recurrentOccurrence D.syncLength m hmrec N₀
  have hoccStrict : StrictMono occ := by
    exact recurrentOccurrence_strict D.syncLength m hmrec N₀
  have hdepthStep :
      ∀ j : ℕ, D.depth (occ j) < D.depth (occ (j + 1)) := by
    intro j
    apply D.depthGrowth
    · exact hoccStrict (Nat.lt_succ_self j)
    · exact recurrentOccurrence_value D.syncLength m hmrec N₀ j
    · exact recurrentOccurrence_value D.syncLength m hmrec N₀ (j + 1)
    · intro t hleft hright
      have hocc0 : N₀ ≤ occ 0 :=
        recurrentOccurrence_zero_ge D.syncLength m hmrec N₀
      have hzeroLe : occ 0 ≤ occ j :=
        hoccStrict.monotone (Nat.zero_le j)
      have hNt : N₀ ≤ t := by omega
      have hmle : m ≤ D.syncLength t := hN₀ t hNt
      have hmne : D.syncLength t ≠ m :=
        recurrentOccurrence_between_ne
          D.syncLength m hmrec N₀ j t hleft hright
      omega
  have hdepthStrict : StrictMono (fun j => D.depth (occ j)) :=
    strictMono_nat_of_lt_succ hdepthStep
  have hindexBound : B + 1 ≤ D.depth (occ (B + 1)) := by
    exact CoherentC3CylinderSequence.strictMono_nat_id_le
      (fun j => D.depth (occ j)) hdepthStrict (B + 1)
  have hupper := hdepth (occ (B + 1))
  omega

end SynchronizationCarrySequence

/--
最終的にSpecial C3であるchainに、orbit由来のdepth-growth法則を付加したもの。
この構造を構成することが、prepared座標と隣接endpointを接続する局所課題である。
-/
structure ChainSynchronizationLaw
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) where
  specialTail : EventuallyChainSpecialData C
  depthGrowth :
    ∀ {k l m : ℕ},
      specialTail.start ≤ k →
      k < l →
      (chainAnalysisPacket C k).prepared.boundary.word.length = m →
      (chainAnalysisPacket C l).prepared.boundary.word.length = m →
      (∀ t : ℕ, k < t → t < l →
        m < (chainAnalysisPacket C t).prepared.boundary.word.length) →
      (chainAnalysisPacket C k).carry.d <
        (chainAnalysisPacket C l).carry.d

namespace ChainSynchronizationLaw


/-- tailを0始まりへ移した抽象同期列。 -/
noncomputable def sequence
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (L : ChainSynchronizationLaw C) :
    SynchronizationCarrySequence where
  syncLength := fun n =>
    (chainAnalysisPacket C (L.specialTail.start + n)).prepared.boundary.word.length
  depth := fun n =>
    (chainAnalysisPacket C (L.specialTail.start + n)).carry.d
  depthGrowth := by
    intro k l m hkl hk hl hbetween
    apply L.depthGrowth
    · omega
    · omega
    · exact hk
    · exact hl
    · intro t hkt htl
      let u := t - L.specialTail.start
      have hu : L.specialTail.start + u = t := by omega
      have hku : k < u := by omega
      have hul : u < l := by omega
      have hbetweenU :
          m <
            (chainAnalysisPacket C
              (L.specialTail.start + u)).prepared.boundary.word.length :=
        hbetween u hku hul
      rw [hu] at hbetweenU
      exact hbetweenU

/-- chain上でprepared depthが有界なら同期prefix長は無限大へ進む。 -/
theorem syncLength_tendsto_of_depth_bounded
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (L : ChainSynchronizationLaw C)
    (B : ℕ)
    (hdepth : ∀ n : ℕ,
      L.specialTail.start ≤ n →
      (chainAnalysisPacket C n).carry.d ≤ B) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      M <
        (chainAnalysisPacket C (L.specialTail.start + n)).prepared.boundary.word.length := by
  apply L.sequence.syncLength_tendsto_of_depth_bounded B
  intro n
  exact hdepth _ (by omega)

end ChainSynchronizationLaw

end CollatzSecondLayer
