import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ProfileCostClosedForm

/-!
# Sturmian profile level-set decomposition

Stage 3 では admissible profile `h` の full cell numerator を

  Σ_k Σ_{j<h(k)} 2^(β_k-j-1) 3^(m-k-1)

として保持し、column ごとには closed form へ畳んだ。

ここでは和の順序を逆転し、各 layer `j` の support

  { k < m | j < h(k) }

を先に見る。

さらに contiguous interval `[a,b)` の寄与を

  2^(β_a-j-1) * 3^(m-b) * Φ[a,b]

へ exact に因数分解する。ここで

  Φ[a,b]
    = Σ_{a≤k<b} 2^(β_k-β_a) 3^(b-1-k).

この `Φ[a,b]` が次段の standard/Ostrowski/Christoffel block calculus へ渡す pure object。

interval decomposition 自体は interface として切り出し、まず singleton intervals による
存在を無条件で構成する。後段では同じ interface を保ったまま adjacent singleton を
maximal / standard blocks へまとめればよい。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators

/-! ## generic level-set Fubini -/

/--
profile の row sum を fixed rectangle `0 ≤ j < L` に埋め込んだ level sum。
`j < h(k)` の cell だけ weight を残す。
-/
def columnProfileLevelSum
    {α : Type*}
    [AddCommMonoid α]
    (m L : ℕ)
    (h : ℕ → ℕ)
    (weight : ℕ → ℕ → α) : α :=
  Finset.sum (Finset.range L)
    (fun j =>
      Finset.sum (Finset.range m)
        (fun k => if j < h k then weight k j else 0))

/-- bounded row を indicator 付き rectangle row へ延長する。 -/
private theorem sum_range_eq_sum_range_ite_lt
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    {h L : ℕ}
    (hh : h ≤ L) :
    Finset.sum (Finset.range h) f =
      Finset.sum (Finset.range L)
        (fun j => if j < h then f j else 0) := by
  induction L generalizing h with
  | zero =>
      have hh0 : h = 0 := by omega
      subst h
      simp
  | succ L ih =>
      by_cases hSmall : h ≤ L
      · rw [Finset.sum_range_succ]
        rw [← ih hSmall]
        have hnot : ¬ L < h := by omega
        simp [hnot]
      · have hEq : h = L + 1 := by omega
        subst h
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hPrefix :
            Finset.sum (Finset.range L)
                (fun j => if j < L + 1 then f j else 0) =
              Finset.sum (Finset.range L) f := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjLt : j < L := Finset.mem_range.mp hj
          simp [show j < L + 1 by omega]
        rw [hPrefix]
        simp

/--
row-bounded profile sum は exact に layer-first double sum へ交換できる。
-/
theorem columnProfileSum_eq_levelSum
    {α : Type*}
    [AddCommMonoid α]
    {m L : ℕ}
    {h : ℕ → ℕ}
    (weight : ℕ → ℕ → α)
    (hBound : ∀ k : ℕ, k < m → h k ≤ L) :
    columnProfileSum m h weight =
      columnProfileLevelSum m L h weight := by
  unfold columnProfileSum columnProfileLevelSum
  calc
    Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range (h k))
            (fun j => weight k j))
        =
      Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range L)
            (fun j => if j < h k then weight k j else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkLt : k < m := Finset.mem_range.mp hk
          exact
            sum_range_eq_sum_range_ite_lt
              (fun j => weight k j)
              (hBound k hkLt)
    _ =
      Finset.sum (Finset.range L)
        (fun j =>
          Finset.sum (Finset.range m)
            (fun k => if j < h k then weight k j else 0)) := by
          rw [Finset.sum_comm]

/-! ## admissible profile level sets -/

/-- fixed layer `j` の support columns。 -/
def profileLayerSupport
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun k => j < h k)

/-- fixed layer `j` の dyadic numerator。 -/
def profileDyadicLayerNumerator
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) : ℕ :=
  Finset.sum (Finset.range m)
    (fun k =>
      if j < h k then profileDyadicCellTerm m k j else 0)

/-- 全 layer を terminal Beatty roof まで積分した numerator。 -/
def profileDyadicLevelNumerator
    (m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  Finset.sum (Finset.range (beattyIndex m))
    (fun j => profileDyadicLayerNumerator m h j)

/-- admissible profile の relevant depth は terminal Beatty roof 以下。 -/
theorem AdmissibleSturmianProfile.depth_le_terminalRoof
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k : ℕ}
    (hk : k < m) :
    h k ≤ beattyIndex m := by
  have hDepth : h k ≤ beattyIndex k := A.depth_le hk
  have hBeatty : beattyIndex k < beattyIndex m :=
    beattyIndex_strictMono hk
  omega

/--
Stage 3 numerator は exact に layer-first level-set numerator と一致する。
-/
theorem profileDyadicCellNumerator_eq_levelNumerator
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h) :
    profileDyadicCellNumerator m h =
      profileDyadicLevelNumerator m h := by
  unfold profileDyadicCellNumerator profileDyadicLevelNumerator
    profileDyadicLayerNumerator
  exact
    columnProfileSum_eq_levelSum
      (m := m)
      (L := beattyIndex m)
      (h := h)
      (fun k j => profileDyadicCellTerm m k j)
      (fun k hk => A.depth_le_terminalRoof hk)

/-- filter sum と indicator sum の elementary bridge。 -/
private theorem sum_filter_eq_sum_ite
    {α β : Type*}
    [AddCommMonoid β]
    (s : Finset α)
    (p : α → Prop)
    [DecidablePred p]
    (f : α → β) :
    Finset.sum (s.filter p) f =
      Finset.sum s (fun x => if p x then f x else 0) := by
  exact Finset.sum_filter (s := s) p f

/-- layer numerator は support 上の普通の sum として読める。 -/
theorem profileDyadicLayerNumerator_eq_supportSum
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) :
    profileDyadicLayerNumerator m h j =
      Finset.sum (profileLayerSupport m h j)
        (fun k => profileDyadicCellTerm m k j) := by
  unfold profileDyadicLayerNumerator profileLayerSupport
  symm
  exact
    sum_filter_eq_sum_ite
      (Finset.range m)
      (fun k => j < h k)
      (fun k => profileDyadicCellTerm m k j)

/-! ## contiguous interval contribution -/

/--
critical Beatty interval `[a,b)` の normalized affine numerator。
-/
def criticalIntervalPhi
    (a b : ℕ) : ℕ :=
  Finset.sum (Finset.Ico a b)
    (fun k =>
      2 ^ (beattyIndex k - beattyIndex a) *
        3 ^ (b - 1 - k))

/-- profile layer `j` の interval `[a,b)` に含まれる raw cell contribution。 -/
def profileDyadicIntervalNumerator
    (m j a b : ℕ) : ℕ :=
  Finset.sum (Finset.Ico a b)
    (fun k => profileDyadicCellTerm m k j)

/-- interval 内では Beatty index は left endpoint 以上。 -/
private theorem beattyIndex_le_of_mem_Ico
    {a b k : ℕ}
    (hk : k ∈ Finset.Ico a b) :
    beattyIndex a ≤ beattyIndex k := by
  have hak : a ≤ k := (Finset.mem_Ico.mp hk).1
  by_cases hEq : a = k
  · subst k
    exact le_rfl
  · exact le_of_lt (beattyIndex_strictMono (by omega))

/--
contiguous interval `[a,b)` の layer contribution は exact に

  2^(β_a-j-1) * 3^(m-b) * Φ[a,b]

へ因数分解される。
-/
theorem profileDyadicIntervalNumerator_eq_scaledCriticalIntervalPhi
    {m j a b : ℕ}
    (hbm : b ≤ m)
    (hj : j < beattyIndex a) :
    profileDyadicIntervalNumerator m j a b =
      2 ^ (beattyIndex a - j - 1) *
        3 ^ (m - b) *
        criticalIntervalPhi a b := by
  unfold profileDyadicIntervalNumerator criticalIntervalPhi
  calc
    Finset.sum (Finset.Ico a b)
        (fun k => profileDyadicCellTerm m k j)
        =
      Finset.sum (Finset.Ico a b)
        (fun k =>
          (2 ^ (beattyIndex a - j - 1) * 3 ^ (m - b)) *
            (2 ^ (beattyIndex k - beattyIndex a) *
              3 ^ (b - 1 - k))) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkIco := Finset.mem_Ico.mp hk
          have hBeta : beattyIndex a ≤ beattyIndex k :=
            beattyIndex_le_of_mem_Ico hk
          have hTwoExp :
              beattyIndex k - j - 1 =
                (beattyIndex a - j - 1) +
                  (beattyIndex k - beattyIndex a) := by
            omega
          have hThreeExp :
              m - (k + 1) =
                (m - b) + (b - 1 - k) := by
            omega
          unfold profileDyadicCellTerm
          rw [hTwoExp, hThreeExp, pow_add, pow_add]
          ring
    _ =
      (2 ^ (beattyIndex a - j - 1) * 3 ^ (m - b)) *
        Finset.sum (Finset.Ico a b)
          (fun k =>
            2 ^ (beattyIndex k - beattyIndex a) *
              3 ^ (b - 1 - k)) := by
          rw [Finset.mul_sum]
    _ =
      2 ^ (beattyIndex a - j - 1) *
        3 ^ (m - b) *
        Finset.sum (Finset.Ico a b)
          (fun k =>
            2 ^ (beattyIndex k - beattyIndex a) *
              3 ^ (b - 1 - k)) := by
          ring

/-! ## interval-decomposition interface -/

/--
fixed layer support を disjoint interval family として扱うための pure interface。
`cover_unique` により各 support column は exactly one interval に属する。
-/
structure ProfileLayerIntervalDecomposition
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) where
  intervals : Finset (ℕ × ℕ)

  interval_nonempty :
    ∀ ab : ℕ × ℕ,
      ab ∈ intervals →
      ab.1 < ab.2

  interval_inside :
    ∀ ab : ℕ × ℕ,
      ab ∈ intervals →
      ab.2 ≤ m

  cover_unique :
    ∀ k : ℕ,
      k < m →
      (j < h k ↔
        ∃! ab : ℕ × ℕ,
          ab ∈ intervals ∧
            ab.1 ≤ k ∧ k < ab.2)

/-- support の各 column を singleton interval `[k,k+1)` にする canonical fallback。 -/
def singletonProfileLayerIntervals
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) : Finset (ℕ × ℕ) :=
  (profileLayerSupport m h j).image
    (fun k => (k, k + 1))

/--
任意の finite profile layer は少なくとも singleton interval decomposition を持つ。
後段ではこれを adjacent merging して maximal / standard blocks に置き換えられる。
-/
def exists_profileLayerIntervalDecomposition
    (m : ℕ)
    (h : ℕ → ℕ)
    (j : ℕ) :
    ProfileLayerIntervalDecomposition m h j := by
  classical
  refine {
    intervals := singletonProfileLayerIntervals m h j
    interval_nonempty := ?_
    interval_inside := ?_
    cover_unique := ?_
  }
  · intro ab hab
    rcases Finset.mem_image.mp hab with ⟨k, hk, rfl⟩
    omega
  · intro ab hab
    rcases Finset.mem_image.mp hab with ⟨k, hk, rfl⟩
    have hkRange : k ∈ Finset.range m :=
      (Finset.mem_filter.mp hk).1
    have hkLt : k < m := Finset.mem_range.mp hkRange
    omega
  · intro k hk
    constructor
    · intro hLayer
      have hkSupport : k ∈ profileLayerSupport m h j := by
        simp [profileLayerSupport, hk, hLayer]
      refine ⟨(k, k + 1), ?_, ?_⟩
      · constructor
        · exact Finset.mem_image.mpr ⟨k, hkSupport, rfl⟩
        · omega
      · intro ab hab
        rcases Finset.mem_image.mp hab.1 with ⟨l, hl, hEq⟩
        have hEq' : ab = (l, l + 1) := hEq.symm
        have hlk : l ≤ k := by
          simpa [hEq'] using hab.2.1
        have hkl : k < l + 1 := by
          simpa [hEq'] using hab.2.2
        have hklEq : k = l := by omega
        subst l
        exact hEq'
    · rintro ⟨ab, hab, _⟩
      rcases Finset.mem_image.mp hab.1 with ⟨l, hl, hEq⟩
      have hEq' : ab = (l, l + 1) := hEq.symm
      have hlk : l ≤ k := by
        simpa [hEq'] using hab.2.1
      have hkl : k < l + 1 := by
        simpa [hEq'] using hab.2.2
      have hklEq : k = l := by omega
      subst l
      exact (Finset.mem_filter.mp hl).2

end CSTMicro
end Collatz2
