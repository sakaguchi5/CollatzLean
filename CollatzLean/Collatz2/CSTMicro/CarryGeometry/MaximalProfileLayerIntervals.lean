import CollatzLean.Collatz2.CSTMicro.CarryGeometry.SturmianProfileLevelSets

/-!
# Maximal profile-layer intervals

`SturmianProfileLevelSets` では fixed layer

  S_j = { k < m | j < h(k) }

を singleton intervals で常に分解できることまで証明した。
このファイルでは singleton fallback を canonical maximal connected components へ置き換える。

有限一次元 support なので、各 `k ∈ S_j` について

* `a` = `[a,k]` がすべて support に入る最小の left endpoint,
* `b` = `k < b ≤ m` で `b=m` または `b ∉ S_j` となる最小の exit,

を取れば `[a,b)` が `k` を含む一意な maximal interval になる。

この構成は Sturmian 性を使わない純有限組合せ論であり、後段では各 maximal interval の
endpoint だけを `CriticalPrefixOstrowski` へ渡す。
-/

namespace Collatz2
namespace CSTMicro

/-- fixed layer support の membership を短く書く。 -/
def IsProfileLayerSupported
    (m : ℕ)
    (h : ℕ → ℕ)
    (j k : ℕ) : Prop :=
  k ∈ profileLayerSupport m h j

/--
`[a,b)` が fixed layer support の maximal connected component であること。
-/
def IsMaximalProfileLayerInterval
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ)
    (ab : ℕ × ℕ) : Prop :=
  ab.1 < ab.2 ∧
  ab.2 ≤ m ∧
  Finset.Ico ab.1 ab.2 ⊆ profileLayerSupport m h j ∧
  (ab.1 = 0 ∨ ab.1 - 1 ∉ profileLayerSupport m h j) ∧
  (ab.2 = m ∨ ab.2 ∉ profileLayerSupport m h j)

/--
全 maximal layer intervals の finite set。
endpoint は `0,...,m` に限られるので finite filter で保持できる。
-/
noncomputable def maximalProfileLayerIntervals
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (Finset.product (Finset.range (m + 1)) (Finset.range (m + 1))).filter
      (fun ab => IsMaximalProfileLayerInterval m h j ab)

@[simp] theorem mem_maximalProfileLayerIntervals_iff
    {m : ℕ}
    {h : ℕ → ℕ}
    {j : ℕ}
    {ab : ℕ × ℕ} :
    ab ∈ maximalProfileLayerIntervals m h j ↔
      ab.1 ≤ m ∧
      ab.2 ≤ m ∧
      IsMaximalProfileLayerInterval m h j ab := by
  classical
  rcases ab with ⟨a, b⟩
  simp [maximalProfileLayerIntervals, and_assoc]

/-- maximal interval の内部は support に入る。 -/
theorem IsMaximalProfileLayerInterval.mem_support
    {m : ℕ}
    {h : ℕ → ℕ}
    {j a b k : ℕ}
    (H : IsMaximalProfileLayerInterval m h j (a, b))
    (hak : a ≤ k)
    (hkb : k < b) :
    k ∈ profileLayerSupport m h j := by
  exact H.2.2.1 (Finset.mem_Ico.mpr ⟨hak, hkb⟩)

/-- maximal interval の left boundary。 -/
theorem IsMaximalProfileLayerInterval.left_boundary
    {m : ℕ}
    {h : ℕ → ℕ}
    {j a b : ℕ}
    (H : IsMaximalProfileLayerInterval m h j (a, b)) :
    a = 0 ∨ a - 1 ∉ profileLayerSupport m h j :=
  H.2.2.2.1

/-- maximal interval の right boundary。 -/
theorem IsMaximalProfileLayerInterval.right_boundary
    {m : ℕ}
    {h : ℕ → ℕ}
    {j a b : ℕ}
    (H : IsMaximalProfileLayerInterval m h j (a, b)) :
    b = m ∨ b ∉ profileLayerSupport m h j :=
  H.2.2.2.2

/--
各 support point は一意な maximal interval に属する。

証明では left endpoint と right exit をそれぞれ `Nat.find` で canonical に取る。
-/
theorem existsUnique_maximalProfileLayerInterval_containing
    {m : ℕ}
    {h : ℕ → ℕ}
    {j k : ℕ}
    (hk : k ∈ profileLayerSupport m h j) :
    ∃! ab : ℕ × ℕ,
      ab ∈ maximalProfileLayerIntervals m h j ∧
        ab.1 ≤ k ∧ k < ab.2 := by
  have hkRange : k < m := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  let LeftCandidate : ℕ → Prop :=
    fun a =>
      a ≤ k ∧
        Finset.Icc a k ⊆ profileLayerSupport m h j
  have hLeftExists : ∃ a : ℕ, LeftCandidate a := by
    refine ⟨k, le_rfl, ?_⟩
    intro t ht
    have htk := Finset.mem_Icc.mp ht
    have hEq : t = k := by omega
    simpa [hEq] using hk
  let a : ℕ := Nat.find hLeftExists
  have haSpec : LeftCandidate a := by
    simpa [a] using Nat.find_spec hLeftExists
  have haLeK : a ≤ k := haSpec.1
  have haLeftBoundary :
      a = 0 ∨ a - 1 ∉ profileLayerSupport m h j := by
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · right
      intro hPrev
      have haPos : 0 < a := Nat.pos_of_ne_zero ha0
      have hPrevCandidate : LeftCandidate (a - 1) := by
        constructor
        · omega
        · intro t ht
          have htIcc := Finset.mem_Icc.mp ht
          by_cases hta : t < a
          · have hEq : t = a - 1 := by omega
            simpa [hEq] using hPrev
          · apply haSpec.2
            exact Finset.mem_Icc.mpr ⟨by omega, htIcc.2⟩
      have hMin : a ≤ a - 1 := by
        simpa [a] using Nat.find_min' hLeftExists hPrevCandidate
      omega
  let RightExit : ℕ → Prop :=
    fun b =>
      k < b ∧
        b ≤ m ∧
        (b = m ∨ b ∉ profileLayerSupport m h j)
  have hRightExists : ∃ b : ℕ, RightExit b := by
    exact ⟨m, hkRange, le_rfl, Or.inl rfl⟩
  let b : ℕ := Nat.find hRightExists
  have hbSpec : RightExit b := by
    simpa [b] using Nat.find_spec hRightExists
  have hkLtB : k < b := hbSpec.1
  have hbLeM : b ≤ m := hbSpec.2.1
  have hbRightBoundary :
      b = m ∨ b ∉ profileLayerSupport m h j :=
    hbSpec.2.2
  have hRightInside :
      ∀ t : ℕ,
        k ≤ t → t < b →
        t ∈ profileLayerSupport m h j := by
    intro t hkt htb
    by_contra htNot
    have hktStrict : k < t := by
      by_cases hEq : t = k
      · subst t
        exact (htNot hk).elim
      · omega
    have htLeM : t ≤ m := by
      omega
    have htCandidate : RightExit t := by
      exact ⟨hktStrict, htLeM, Or.inr htNot⟩
    have hMin : b ≤ t := by
      simpa [b] using Nat.find_min' hRightExists htCandidate
    omega
  have hIntervalSupport :
      Finset.Ico a b ⊆ profileLayerSupport m h j := by
    intro t ht
    have htIco := Finset.mem_Ico.mp ht
    by_cases htk : t ≤ k
    · apply haSpec.2
      exact Finset.mem_Icc.mpr ⟨htIco.1, htk⟩
    · exact hRightInside t (by omega) htIco.2
  have habLt : a < b := lt_of_le_of_lt haLeK hkLtB
  have hMax : IsMaximalProfileLayerInterval m h j (a, b) := by
    exact
      ⟨habLt, hbLeM, hIntervalSupport,
        haLeftBoundary, hbRightBoundary⟩
  have habMem : (a, b) ∈ maximalProfileLayerIntervals m h j := by
    apply mem_maximalProfileLayerIntervals_iff.mpr
    exact ⟨by omega, hbLeM, hMax⟩
  refine ⟨(a, b), ⟨habMem, haLeK, hkLtB⟩, ?_⟩
  intro cd hcd
  rcases hcd with ⟨hcdMem, hck, hkd⟩
  let c := cd.1
  let d := cd.2
  have hcdMax : IsMaximalProfileLayerInterval m h j (c, d) := by
    exact (mem_maximalProfileLayerIntervals_iff.mp hcdMem).2.2
  have hcdInside := hcdMax.2.2.1
  have hcCandidate : LeftCandidate c := by
    constructor
    · exact hck
    · intro t ht
      have htIcc := Finset.mem_Icc.mp ht
      apply hcdInside
      exact Finset.mem_Ico.mpr ⟨htIcc.1, lt_of_le_of_lt htIcc.2 hkd⟩
  have haLeC : a ≤ c := by
    simpa [a] using Nat.find_min' hLeftExists hcCandidate
  have hcEqA : c = a := by
    by_contra hne
    have haLtC : a < c := by omega
    have hcPos : 0 < c := by omega
    have hcPrevSupport :
        c - 1 ∈ profileLayerSupport m h j := by
      apply haSpec.2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rcases hcdMax.left_boundary with hc0 | hcBoundary
    · omega
    · exact (hcBoundary hcPrevSupport).elim
  have hdCandidate : RightExit d := by
    exact ⟨hkd, hcdMax.2.1, hcdMax.right_boundary⟩
  have hbLeD : b ≤ d := by
    simpa [b] using Nat.find_min' hRightExists hdCandidate
  have hdEqB : d = b := by
    by_contra hne
    have hbLtD : b < d := by omega
    rcases hbRightBoundary with hbM | hbNotSupport
    · omega
    · have hbSupport : b ∈ profileLayerSupport m h j := by
        apply hcdInside
        exact Finset.mem_Ico.mpr ⟨by simpa [hcEqA] using habLt.le, hbLtD⟩
      exact (hbNotSupport hbSupport).elim
  apply Prod.ext
  · simpa [c] using hcEqA
  · simpa [d] using hdEqB

/--
canonical maximal interval family は Stage 7 の generic interval-decomposition interface を満たす。
-/
noncomputable def maximalProfileLayerIntervalDecomposition
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) :
    ProfileLayerIntervalDecomposition m h j := by
  classical
  refine {
    intervals := maximalProfileLayerIntervals m h j
    interval_nonempty := ?_
    interval_inside := ?_
    cover_unique := ?_
  }
  · intro ab hab
    exact (mem_maximalProfileLayerIntervals_iff.mp hab).2.2.1
  · intro ab hab
    exact (mem_maximalProfileLayerIntervals_iff.mp hab).2.1
  · intro k hk
    constructor
    · intro hLayer
      have hkSupport : k ∈ profileLayerSupport m h j := by
        simp [profileLayerSupport, hk, hLayer]
      exact existsUnique_maximalProfileLayerInterval_containing hkSupport
    · rintro ⟨ab, hab, _⟩
      have hMax : IsMaximalProfileLayerInterval m h j ab :=
        (mem_maximalProfileLayerIntervals_iff.mp hab.1).2.2
      have hkSupport : k ∈ profileLayerSupport m h j :=
        hMax.mem_support hab.2.1 hab.2.2
      exact (Finset.mem_filter.mp hkSupport).2

/-- maximal decomposition に現れる interval は本当に maximal。 -/
theorem maximalProfileLayerIntervalDecomposition_interval_isMaximal
    {m : ℕ}
    {h : ℕ → ℕ}
    {j : ℕ}
    {ab : ℕ × ℕ}
    (hab :
      ab ∈
        (maximalProfileLayerIntervalDecomposition m h j).intervals) :
    IsMaximalProfileLayerInterval m h j ab := by
  exact (mem_maximalProfileLayerIntervals_iff.mp hab).2.2

/--
異なる maximal intervals は共通の column を持たない。
-/
theorem maximalProfileLayerIntervals_disjoint_of_ne
    {m : ℕ}
    {h : ℕ → ℕ}
    {j : ℕ}
    {ab cd : ℕ × ℕ}
    (hab : ab ∈ maximalProfileLayerIntervals m h j)
    (hcd : cd ∈ maximalProfileLayerIntervals m h j)
    (hne : ab ≠ cd) :
    Disjoint (Finset.Ico ab.1 ab.2) (Finset.Ico cd.1 cd.2) := by
  classical
  rw [Finset.disjoint_left]
  intro k hkab hkcd
  have hMaxAB := (mem_maximalProfileLayerIntervals_iff.mp hab).2.2
  have hkSupport :=
    hMaxAB.mem_support
      (Finset.mem_Ico.mp hkab).1
      (Finset.mem_Ico.mp hkab).2
  rcases existsUnique_maximalProfileLayerInterval_containing hkSupport with
    ⟨ef, hef, hUnique⟩
  have hABSpec :
      ab ∈ maximalProfileLayerIntervals m h j ∧ ab.1 ≤ k ∧ k < ab.2 :=
    ⟨hab, (Finset.mem_Ico.mp hkab).1, (Finset.mem_Ico.mp hkab).2⟩
  have hCDSpec :
      cd ∈ maximalProfileLayerIntervals m h j ∧ cd.1 ≤ k ∧ k < cd.2 :=
    ⟨hcd, (Finset.mem_Ico.mp hkcd).1, (Finset.mem_Ico.mp hkcd).2⟩
  have hEqAB : ab = ef := hUnique ab hABSpec
  have hEqCD : cd = ef := hUnique cd hCDSpec
  exact hne (hEqAB.trans hEqCD.symm)

end CSTMicro
end Collatz2
