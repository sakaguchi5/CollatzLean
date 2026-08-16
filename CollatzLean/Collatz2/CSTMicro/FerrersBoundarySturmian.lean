import CollatzLean.Collatz2.CSTMicro.BinaryFerrersOrder

/-!
# General CST: Ferrers boundary = critical Sturmian boundary

`IsFerrersBoundary` を abstract な predecessor-free object のまま残さず、
critical irrational slope の upper mechanical/Sturmian boundary と同定する。

実数 log は使わない。proper prefix `j` ごとに

  SturmianBoundaryAt j (prefixOddCount v j)

すなわち prefix odd count が `2^j < 3^m` を初めて満たす最小 height
であることを exact power language で要求する。

数学的には `j > 0` で

  prefixOddCount v j = ceil (j * log₃ 2)

と同じ条件である。
-/

namespace Collatz2
namespace CSTMicro

/--
critical Sturmian boundary の explicit power-form characterization。
proper prefix がすべて最小 expanding height に exact に乗る。
-/
def IsCriticalSturmianBoundaryWord (v : ParityWord) : Prop :=
  IsFirstPassageWord v ∧
    ∀ j : ℕ, 0 < j → j < v.length →
      FirstPassagePath.SturmianBoundaryAt j (prefixOddCount v j)

/-- critical Sturmian condition は criticalHeight との等式に言い換えられる。 -/
theorem isCriticalSturmianBoundaryWord_iff_criticalHeight
    (v : ParityWord) :
    IsCriticalSturmianBoundaryWord v ↔
      IsFirstPassageWord v ∧
        ∀ j : ℕ, 0 < j → j < v.length →
          prefixOddCount v j = criticalHeight j := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro j hjPos hjLt
    exact (sturmianBoundaryAt_iff_eq_criticalHeight
      j (prefixOddCount v j)).1 (h.2 j hjPos hjLt)
  · intro h
    refine ⟨h.1, ?_⟩
    intro j hjPos hjLt
    apply (sturmianBoundaryAt_iff_eq_criticalHeight
      j (prefixOddCount v j)).2
    exact h.2 j hjPos hjLt

/-- critical mechanical step bit。 -/
noncomputable def criticalSturmianBit (i : ℕ) : Bool :=
  decide (criticalPrefixHeight (i + 1) = criticalPrefixHeight i + 1)

/--
critical Sturmian bit が true であることは、
critical prefix height がその step で exact に 1 増えることと同値。
-/
@[simp] theorem criticalSturmianBit_eq_true_iff
    (i : ℕ) :
    criticalSturmianBit i = true ↔
      criticalPrefixHeight (i + 1) =
        criticalPrefixHeight i + 1 := by
  simp [criticalSturmianBit]

/--
critical Sturmian bit が false であることは、
critical prefix height がその step で 1 増えないことと同値。
-/
@[simp] theorem criticalSturmianBit_eq_false_iff
    (i : ℕ) :
    criticalSturmianBit i = false ↔
      criticalPrefixHeight (i + 1) ≠
        criticalPrefixHeight i + 1 := by
  simp [criticalSturmianBit]

/-- critical height increment は bitNat と exact に一致する。 -/
theorem criticalPrefixHeight_step (i : ℕ) :
    criticalPrefixHeight (i + 1) =
      criticalPrefixHeight i + bitNat (criticalSturmianBit i) := by
  have hmono := criticalPrefixHeight_mono i
  have hle := criticalPrefixHeight_succ_le i
  by_cases hEq :
      criticalPrefixHeight (i + 1) =
        criticalPrefixHeight i + 1
  · have hbit : criticalSturmianBit i = true := by
      exact (criticalSturmianBit_eq_true_iff i).2 hEq
    rw [hEq, hbit]
    simp [bitNat]
  · have hsame :
        criticalPrefixHeight (i + 1) =
          criticalPrefixHeight i := by
      omega
    have hbit : criticalSturmianBit i = false := by
      exact (criticalSturmianBit_eq_false_iff i).2 hEq
    rw [hsame, hbit]
    simp [bitNat]

/-- upper mechanical Sturmian word の finite prefix。 -/
noncomputable def criticalSturmianPrefix : ℕ → ParityWord
  | 0 => []
  | n + 1 => criticalSturmianPrefix n ++ [criticalSturmianBit n]

@[simp] theorem criticalSturmianPrefix_length (n : ℕ) :
    (criticalSturmianPrefix n).length = n := by
  induction n with
  | zero => simp [criticalSturmianPrefix]
  | succ n ih => simp [criticalSturmianPrefix, ih]

@[simp] theorem criticalSturmianPrefix_oddCount (n : ℕ) :
    oddCount (criticalSturmianPrefix n) = criticalPrefixHeight n := by
  induction n with
  | zero =>
      simp [criticalSturmianPrefix, criticalPrefixHeight, oddCount]
  | succ n ih =>
      rw [criticalSturmianPrefix]
      rw [cstOddCount_append]
      rw [ih]
      rw [criticalPrefixHeight_step]
      simp [oddCount, bitNat]

/-- length 内の prefix は後ろに word を足しても変わらない。 -/
theorem prefixOddCount_append_of_le_length
    (u v : ParityWord)
    {j : ℕ}
    (hj : j ≤ u.length) :
    prefixOddCount (u ++ v) j = prefixOddCount u j := by
  induction u generalizing j with
  | nil =>
      have hj0 : j = 0 := by simp at hj; omega
      subst j
      simp [prefixOddCount]
  | cons b u ih =>
      cases j with
      | zero =>
          simp [prefixOddCount]
      | succ j =>
          simp only [
            List.cons_append,
            prefixOddCount_cons_succ_general
          ]
          have hj' : j ≤ u.length := by
            simp at hj
            omega
          rw [ih hj']

@[simp] theorem prefixOddCount_length (v : ParityWord) :
    prefixOddCount v v.length = oddCount v := by
  unfold prefixOddCount
  rw [List.take_length]

/-- mechanical prefix の prefix odd count は critical height そのもの。 -/
theorem criticalSturmianPrefix_prefixOddCount
    (n j : ℕ)
    (hj : j ≤ n) :
    prefixOddCount (criticalSturmianPrefix n) j =
      criticalPrefixHeight j := by
  induction n generalizing j with
  | zero =>
      have hj0 : j = 0 := by
        omega
      subst j
      simp only [prefixOddCount, criticalSturmianPrefix, List.take_nil, criticalPrefixHeight]
      decide
  | succ n ih =>
      by_cases hjn : j ≤ n
      · rw [criticalSturmianPrefix]
        rw [
          prefixOddCount_append_of_le_length
            (criticalSturmianPrefix n)
            [criticalSturmianBit n]
            (by simpa using hjn)
        ]
        exact ih j hjn
      · have hjEq : j = n + 1 := by
          omega
        subst j
        have hlen :
            (criticalSturmianPrefix (n + 1)).length = n + 1 := by
          simp [criticalSturmianPrefix]
        calc
          prefixOddCount
              (criticalSturmianPrefix (n + 1))
              (n + 1)
              =
            prefixOddCount
              (criticalSturmianPrefix (n + 1))
              (criticalSturmianPrefix (n + 1)).length := by
                exact
                  congrArg
                    (fun k =>
                      prefixOddCount
                        (criticalSturmianPrefix (n + 1)) k)
                    hlen.symm
          _ =
            oddCount (criticalSturmianPrefix (n + 1)) :=
              prefixOddCount_length
                (criticalSturmianPrefix (n + 1))
          _ =
            criticalPrefixHeight (n + 1) :=
              criticalSturmianPrefix_oddCount (n + 1)

/--
first-passage length `k>0` に対応する critical boundary word。
mechanical prefix の最後の crossing bit は terminal では 0 に落ちる。
-/
noncomputable def criticalBoundaryWord : ℕ → ParityWord
  | 0 => []
  | k + 1 => criticalSturmianPrefix k ++ [false]

@[simp] theorem criticalBoundaryWord_length
    (k : ℕ) :
    (criticalBoundaryWord k).length = k := by
  cases k with
  | zero => simp [criticalBoundaryWord]
  | succ k => simp [criticalBoundaryWord]

/-- positive length の proper prefix は exact critical height。 -/
theorem criticalBoundaryWord_prefixOddCount
    {k j : ℕ}
    (hk : 0 < k)
    (hj : j < k) :
    prefixOddCount (criticalBoundaryWord k) j =
      criticalPrefixHeight j := by
  cases k with
  | zero => omega
  | succ k =>
      rw [criticalBoundaryWord]
      rw [prefixOddCount_append_of_le_length
        (criticalSturmianPrefix k) [false]
        (by simpa using (Nat.le_of_lt_succ hj))]
      exact criticalSturmianPrefix_prefixOddCount k j
        (Nat.le_of_lt_succ hj)

/-- positive time では criticalPrefixHeight は criticalHeight と一致する。 -/
theorem criticalPrefixHeight_eq_criticalHeight_of_pos
    {j : ℕ}
    (hj : 0 < j) :
    criticalPrefixHeight j = criticalHeight j := by
  cases j with
  | zero =>
      simp at hj
  | succ t =>
      rfl

/-- any nonempty first-passage word の endpoint odd count は前時刻 critical height。 -/
theorem endpointOddCount_eq_criticalPrefixHeight_pred
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    oddCount v = criticalPrefixHeight (v.length - 1) := by
  have hlenPos : 0 < v.length := List.length_pos_of_ne_nil h.1
  by_cases hlen1 : v.length = 1
  · have hmle : oddCount v ≤ 1 := by
      rw [← hlen1]
      exact oddCount_le_length v
    have hcontract := h.2.2
    unfold CoefficientContracting at hcontract
    have hm0 : oddCount v = 0 := by
      by_contra hm0
      have hm1 : oddCount v = 1 := by
        omega
      rw [hlen1, hm1] at hcontract
      norm_num at hcontract
    rw [hm0, hlen1]
    simp [criticalPrefixHeight]
  · have hlen2 : 2 ≤ v.length := by omega
    let j := v.length - 1
    have hjPos : 0 < j := by simp [j]; omega
    have hjLt : j < v.length := by simp [j]; omega
    have hjSucc : j + 1 = v.length := by simp [j]; omega
    have hExp := h.2.1 j hjPos hjLt
    unfold CoefficientExpandingAt at hExp
    have hcrit_le_prefix :
        criticalHeight j ≤ prefixOddCount v j :=
      criticalHeight_le_of_expanding hExp
    have hprefix_le_total : prefixOddCount v j ≤ oddCount v :=
      prefixOddCount_le_oddCount v j
    have hcrit_le_total : criticalHeight j ≤ oddCount v :=
      le_trans hcrit_le_prefix hprefix_le_total
    have htotal_le_crit : oddCount v ≤ criticalHeight j := by
      by_contra hnot
      have hcritSucc : criticalHeight j + 1 ≤ oddCount v := by omega
      have hpowMono :
          3 ^ (criticalHeight j + 1) ≤ 3 ^ oddCount v :=
        Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hcritSucc
      have hcritExp := criticalHeight_expanding j
      have htwo :
          2 ^ (j + 1) < 3 ^ (criticalHeight j + 1) := by
        rw [pow_succ, pow_succ]
        have hp : 0 < 2 ^ j := Nat.pow_pos (by omega)
        nlinarith
      have hcontract := h.2.2
      unfold CoefficientContracting at hcontract
      rw [← hjSucc] at hcontract
      omega
    have heq : oddCount v = criticalHeight j := by omega
    have hpref :
        criticalPrefixHeight j = criticalHeight j :=
      criticalPrefixHeight_eq_criticalHeight_of_pos hjPos
    change oddCount v = criticalPrefixHeight j
    rw [hpref]
    exact heq

/--
critical boundary word has the same endpoint odd count as
 any first-passage word of that length. -/
theorem criticalBoundaryWord_oddCount_eq
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    oddCount (criticalBoundaryWord v.length) = oddCount v := by
  have hlenPos : 0 < v.length := List.length_pos_of_ne_nil h.1
  cases hlen : v.length with
  | zero => omega
  | succ k =>
      have hend :=
        endpointOddCount_eq_criticalPrefixHeight_pred h
      have hend' :
          oddCount v = criticalPrefixHeight k := by
        simpa [hlen] using hend
      rw [hend']
      simp only [criticalBoundaryWord, cstOddCount_append,
        criticalSturmianPrefix_oddCount, oddCount_false_cons,Nat.add_eq_left]
      decide

/-- critical boundary word itself is first-passage whenever that length occurs. -/
theorem criticalBoundaryWord_isFirstPassage
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    IsFirstPassageWord (criticalBoundaryWord v.length) := by
  have hlenPos : 0 < v.length :=
    List.length_pos_of_ne_nil h.1
  constructor
  · intro hnil
    have hzero :
        (criticalBoundaryWord v.length).length = 0 := by
      rw [hnil]
      rfl
    simp only [criticalBoundaryWord_length, List.length_eq_zero_iff] at hzero
    exact h.1 hzero
  · constructor
    · intro j hjPos hjLt
      have hjLtV : j < v.length := by
        simpa only [criticalBoundaryWord_length] using hjLt
      unfold CoefficientExpandingAt
      rw [criticalBoundaryWord_prefixOddCount hlenPos hjLtV]
      cases j with
      | zero =>
          omega
      | succ j =>
          exact criticalHeight_expanding (j + 1)
    · unfold CoefficientContracting
      rw [criticalBoundaryWord_oddCount_eq h]
      rw [criticalBoundaryWord_length]
      exact h.2.2

/-- critical boundary lies below every first-passage word of the same length. -/
theorem criticalBoundaryWord_prefixBelow
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    PrefixBelow (criticalBoundaryWord v.length) v := by
  have hlenPos : 0 < v.length :=
    List.length_pos_of_ne_nil h.1
  refine ⟨by simp, criticalBoundaryWord_oddCount_eq h, ?_⟩
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [prefixOddCount]
  · by_cases hjEq : j = v.length
    · -- endpoint
      subst j
      have hBoundaryLength :
          (criticalBoundaryWord v.length).length = v.length :=
        criticalBoundaryWord_length v.length
      have hLeft :
          prefixOddCount
              (criticalBoundaryWord v.length)
              v.length
            =
          oddCount (criticalBoundaryWord v.length) := by
        calc
          prefixOddCount
              (criticalBoundaryWord v.length)
              v.length
              =
            prefixOddCount
              (criticalBoundaryWord v.length)
              (criticalBoundaryWord v.length).length := by
                exact
                  congrArg
                    (fun k =>
                      prefixOddCount
                        (criticalBoundaryWord v.length) k)
                    hBoundaryLength.symm
          _ =
            oddCount (criticalBoundaryWord v.length) :=
              prefixOddCount_length
                (criticalBoundaryWord v.length)
      have hRight :
          prefixOddCount v v.length = oddCount v :=
        prefixOddCount_length v
      have hEq :
          prefixOddCount
              (criticalBoundaryWord v.length)
              v.length
            =
          prefixOddCount v v.length := by
        calc
          prefixOddCount
              (criticalBoundaryWord v.length)
              v.length
              =
            oddCount (criticalBoundaryWord v.length) :=
              hLeft
          _ = oddCount v :=
            criticalBoundaryWord_oddCount_eq h
          _ = prefixOddCount v v.length :=
            hRight.symm
      exact le_of_eq hEq
    · -- proper positive prefix
      have hjLeV : j ≤ v.length := by
        have hBoundaryLength :
            (criticalBoundaryWord v.length).length = v.length := by
          exact criticalBoundaryWord_length v.length
        rw [hBoundaryLength] at hj
        exact hj
      have hjPos : 0 < j := by
        omega
      have hjLt : j < v.length := by
        omega
      have hBoundaryPrefix :
          prefixOddCount
              (criticalBoundaryWord v.length) j
            =
          criticalPrefixHeight j :=
        criticalBoundaryWord_prefixOddCount
          hlenPos
          hjLt
      have hExp := h.2.1 j hjPos hjLt
      unfold CoefficientExpandingAt at hExp
      have hCritLe :
          criticalHeight j ≤ prefixOddCount v j :=
        criticalHeight_le_of_expanding hExp
      have hPrefixHeight :
          criticalPrefixHeight j = criticalHeight j :=
        criticalPrefixHeight_eq_criticalHeight_of_pos hjPos
      rw [hBoundaryPrefix, hPrefixHeight]
      exact hCritLe


/-- explicit critical word is Ferrers-minimal. -/
theorem criticalSturmianBoundary_isFerrersBoundary
    {v : ParityWord}
    (h : IsCriticalSturmianBoundaryWord v) :
    IsFerrersBoundary v := by
  refine ⟨h.1, ?_⟩
  intro lower S hLowerFP
  let j := S.edge.position + 1
  have hjPos : 0 < j := by simp [j]
  have hjLt : j < v.length := by
    have hedge : S.edge.position + 1 < S.edge.length := by
      unfold AdjacentFerrersSwap.position AdjacentFerrersSwap.length
      omega
    rw [S.upper_eq, S.edge.upperWord_length]
    simpa [j] using hedge
  have hBoundary := h.2 j hjPos hjLt
  have hLowerExp := hLowerFP.2.1 j hjPos (by
    rw [S.length_eq]
    exact hjLt)
  unfold CoefficientExpandingAt at hLowerExp
  have hswap :=
    S.edge.upper_prefix_eq_lower_prefix_add_one
  have hUpperCount :
      prefixOddCount v j =
        prefixOddCount S.edge.upperWord j := by
    exact
      congrArg
        (fun w => prefixOddCount w j)
        S.upper_eq
  have hLowerCount :
      prefixOddCount lower j =
        prefixOddCount S.edge.lowerWord j := by
    exact
      congrArg
        (fun w => prefixOddCount w j)
        S.lower_eq
  have hltCount :
      prefixOddCount lower j < prefixOddCount v j := by
    rw [hUpperCount, hLowerCount]
    rw [show prefixOddCount S.edge.upperWord j =
        prefixOddCount S.edge.lowerWord j + 1 by
      simpa [j] using hswap]
    exact Nat.lt_succ_self (prefixOddCount S.edge.lowerWord j)
  exact hBoundary.2 (prefixOddCount lower j) hltCount hLowerExp

/--
Ferrers-minimal boundary は global critical word に一致する。
これが local predecessor-free 定義から mechanical/Sturmian word への同定の核心。
-/
theorem ferrersBoundary_eq_criticalBoundaryWord
    {v : ParityWord}
    (h : IsFerrersBoundary v) :
    v = criticalBoundaryWord v.length := by
  have hCritFP := criticalBoundaryWord_isFirstPassage h.1
  have hBelow := criticalBoundaryWord_prefixBelow h.1
  by_contra hne
  have hne' : criticalBoundaryWord v.length ≠ v := by
    exact Ne.symm hne
  rcases exists_ferrersPredecessor_of_prefixBelow_ne hBelow hne' with
    ⟨pred, S, hPredBelow⟩
  have hPredFP : IsFirstPassageWord pred :=
    IsFirstPassageWord.of_prefixBelow hCritFP hPredBelow
  exact h.2 pred S hPredFP

/--
最終同定:

  IsFerrersBoundary v
    iff
  v は critical irrational slope の explicit Sturmian boundary。
-/
theorem isFerrersBoundary_iff_criticalSturmian
    (v : ParityWord) :
    IsFerrersBoundary v ↔ IsCriticalSturmianBoundaryWord v := by
  constructor
  · intro h
    have hvEq := ferrersBoundary_eq_criticalBoundaryWord h
    have hFP : IsFirstPassageWord v := h.1
    refine ⟨hFP, ?_⟩
    intro j hjPos hjLt
    rw [hvEq]
    have hlenPos : 0 < v.length := List.length_pos_of_ne_nil hFP.1
    have hcount := criticalBoundaryWord_prefixOddCount hlenPos hjLt
    rw [hcount]
    cases j with
    | zero => omega
    | succ j =>
        exact criticalHeight_sturmianBoundaryAt (j + 1)
  · intro h
    exact criticalSturmianBoundary_isFerrersBoundary h

/-- fixed length の Ferrers boundary は一意。 -/
theorem ferrersBoundary_unique_of_length
    {u v : ParityWord}
    (hu : IsFerrersBoundary u)
    (hv : IsFerrersBoundary v)
    (hlen : u.length = v.length) :
    u = v := by
  rw [ferrersBoundary_eq_criticalBoundaryWord hu,
      ferrersBoundary_eq_criticalBoundaryWord hv,
      hlen]

end CSTMicro
end Collatz2
