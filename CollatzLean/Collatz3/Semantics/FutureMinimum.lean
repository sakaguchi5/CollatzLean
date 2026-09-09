import CollatzLean.Collatz3.Semantics.OddOrbit
import Mathlib.Tactic.NormNum


/-!
# Collatz3: future minimum の thin semantics

future minimum は **actual orbit の値** に関する意味論であり、
critical roof anchor や Record--Ferrers の cut とは別概念である。

無限の selector を最初から要求せず、まず一点の future minimum と、
current より後の tail から一つだけ最小点を取る `NextFutureMinimum` を薄い局所語彙として置く。
一つの next minimum を無条件に無限 tail から選ぶことはここでは行わない。
有限区間に最小値があることと、「十分後ろでは既知の候補以上」という有限化証明書から
next minimum の存在を構成的に導く。三つの終局型からその証明書を作る橋は
`OrbitFateFutureMinimum.lean` に分離する。

repeat が与えられた場合の tail 有限化は `HasNontrivialRepeat` を使わず、
生の `i<j`, `value i = value j` だけからこの層で導く。

選択済み future-minimum 列は compatibility view として残し、
標準隣接性は `StandardFutureMinimum.lean` に分離する。
-/

namespace Collatz3
namespace OddOrbit

/-- 位置 `n` の値が、それ以後の全軌道値以下である。 -/
def FutureMinimumAt
    (O : OddOrbit)
    (n : ℕ) : Prop :=
  ∀ m : ℕ, n ≤ m → O.value n ≤ O.value m

namespace FutureMinimumAt

/-- future minimum から始まる任意の有限 segment の終点は開始値以上。 -/
theorem le_segment_end
    {O : OddOrbit}
    {n : ℕ}
    (h : O.FutureMinimumAt n)
    (q : ℕ) :
    O.value n ≤ O.value (n + q) :=
  h (n + q) (by omega)

/--
値が `1` より大きい future minimum では、その位置の odd-only 指数は exact に `1`。

これは actual 値の最小性から出る定理であり、pure roof anchor `[1]` の定義には使わない。
-/
theorem exponent_eq_one_of_one_lt
    {O : OddOrbit}
    {n : ℕ}
    (h : O.FutureMinimumAt n)
    (hValue : 1 < O.value n) :
    O.exponent n = 1 := by
  have hExpPos := O.exponent_pos n
  by_contra hNe
  have hTwo : 2 ≤ O.exponent n := by
    omega
  have hPow : 4 ≤ 2 ^ O.exponent n := by
    have hMon := Nat.pow_le_pow_right
      (by decide : 0 < (2 : ℕ)) hTwo
    norm_num at hMon
    exact hMon
  have hNext : O.value n ≤ O.value (n + 1) :=
    h.le_segment_end 1
  have hFourStart :
      4 * O.value n ≤ 4 * O.value (n + 1) :=
    Nat.mul_le_mul_left 4 hNext
  have hFourNext :
      4 * O.value (n + 1) ≤
        2 ^ O.exponent n * O.value (n + 1) :=
    Nat.mul_le_mul_right (O.value (n + 1)) hPow
  have hEquation := (O.step n).equation
  have hBound : 4 * O.value n ≤ 3 * O.value n + 1 := by
    calc
      4 * O.value n ≤ 4 * O.value (n + 1) := hFourStart
      _ ≤ 2 ^ O.exponent n * O.value (n + 1) := hFourNext
      _ = 3 * O.value n + 1 := hEquation
  omega

end FutureMinimumAt

/--
`j` が current index `i` より後の tail 全体の最小値を実現する。
無限 selector を保存せず、一つの局所 witness だけを表す。
-/
def NextFutureMinimum
    (O : OddOrbit)
    (i j : ℕ) : Prop :=
  i < j ∧
    ∀ t : ℕ, i < t → O.value j ≤ O.value t

namespace NextFutureMinimum

/-- next minimum は特にその位置自身から先の future minimum。 -/
theorem futureMinimumAt
    {O : OddOrbit}
    {i j : ℕ}
    (h : O.NextFutureMinimum i j) :
    O.FutureMinimumAt j := by
  intro t hjt
  exact h.2 t (lt_of_lt_of_le h.1 hjt)

/-- 同じ current に対する二つの next minimum は値として一致する。 -/
theorem value_eq
    {O : OddOrbit}
    {i j k : ℕ}
    (hj : O.NextFutureMinimum i j)
    (hk : O.NextFutureMinimum i k) :
    O.value j = O.value k := by
  apply Nat.le_antisymm
  · exact hj.2 k hk.1
  · exact hk.2 j hj.1

end NextFutureMinimum

/--
有限区間 `[a, a+q]` には actual orbit value の最小点が存在する。
有限長に対する帰納法と自然数比較だけを使う構成的補題。
-/
theorem exists_intervalMinimum
    (O : OddOrbit)
    (a q : ℕ) :
    ∃ j : ℕ,
      a ≤ j ∧
      j ≤ a + q ∧
      ∀ t : ℕ,
        a ≤ t →
        t ≤ a + q →
        O.value j ≤ O.value t := by
  induction q with
  | zero =>
      refine ⟨a, le_rfl, by simp, ?_⟩
      intro t hat hta
      have ht : t = a := by omega
      subst t
      exact le_rfl
  | succ q ih =>
      rcases ih with ⟨j, haj, hjEnd, hMin⟩
      let b : ℕ := a + (q + 1)
      by_cases hle : O.value j ≤ O.value b
      · refine ⟨j, haj, ?_, ?_⟩
        · omega
        · intro t hat htEnd
          by_cases htb : t = b
          · subst t
            exact hle
          · apply hMin t hat
            dsimp [b] at htEnd htb
            omega
      · have hbj : O.value b < O.value j :=
          lt_of_not_ge hle
        refine ⟨b, ?_, le_rfl, ?_⟩
        · dsimp [b]
          omega
        · intro t hat htEnd
          by_cases htb : t = b
          · subst t
            exact le_rfl
          · have htOld : t ≤ a + q := by
              dsimp [b] at htEnd htb
              omega
            exact le_trans (Nat.le_of_lt hbj) (hMin t hat htOld)

/--
current `i` の直後の値が、ある有限境界 `M` より後の tail 全体以下であるなら、
`i` の次の tail minimum は有限区間 `[i+1,M]` の探索だけで得られる。

これは無限 tail から witness を選ばずに済むための構成的な一般 bridge。
-/
theorem exists_nextFutureMinimum_of_eventually_ge_candidate
    (O : OddOrbit)
    (i M : ℕ)
    (hM : i + 1 ≤ M)
    (hTail :
      ∀ t : ℕ,
        M < t →
        O.value (i + 1) ≤ O.value t) :
    ∃ j : ℕ, O.NextFutureMinimum i j := by
  let q : ℕ := M - (i + 1)
  have hEnd : (i + 1) + q = M := by
    dsimp [q]
    exact Nat.add_sub_of_le hM
  rcases O.exists_intervalMinimum (i + 1) q with
    ⟨j, hjStart, hjEnd, hMin⟩
  refine ⟨j, ?_, ?_⟩
  · omega
  · intro t hit
    by_cases htM : t ≤ M
    · apply hMin t
      · omega
      · rw [hEnd]
        exact htM
    · have hMt : M < t := Nat.lt_of_not_ge htM
      have hCandidate : O.value (i + 1) ≤ O.value t :=
        hTail t hMt
      have hMinCandidate : O.value j ≤ O.value (i + 1) := by
        apply hMin (i + 1)
        · exact le_rfl
        · omega
      exact le_trans hMinCandidate hCandidate

/--
値の repeat `i<j`, `O_i=O_j` だけで、任意の current の後に
`NextFutureMinimum` が構成的に存在する。

`O_i ≠ 1` はこの有限化には不要であり、transient 部分と一周期幅だけを有限探索する。
-/
theorem exists_nextFutureMinimum_of_repeat
    (O : OddOrbit)
    {i j0 : ℕ}
    (hij : i < j0)
    (heq : O.value i = O.value j0)
    (current : ℕ) :
    ∃ j : ℕ, O.NextFutureMinimum current j := by
  let d : ℕ := j0 - i
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt hij
  let base : ℕ := max (current + 1) i
  have hBaseI : i ≤ base := Nat.le_max_right _ _
  have hCurrentBase : current + 1 ≤ base := Nat.le_max_left _ _
  let terminal : ℕ := base + (d - 1)
  have hCurrentTerminal : current + 1 ≤ terminal := by
    dsimp [terminal]
    omega
  let q : ℕ := terminal - (current + 1)
  have hEnd : (current + 1) + q = terminal := by
    dsimp [q]
    exact Nat.add_sub_of_le hCurrentTerminal
  rcases O.exists_intervalMinimum (current + 1) q with
    ⟨m, hmStart, hmEnd, hMin⟩
  refine ⟨m, by omega, ?_⟩
  intro t hCurrentT
  by_cases htTerminal : t ≤ terminal
  · apply hMin t
    · omega
    · rw [hEnd]
      exact htTerminal
  · have hTerminalT : terminal < t := Nat.lt_of_not_ge htTerminal
    have hBaseT : base ≤ t := by
      dsimp [terminal] at hTerminalT
      omega
    let qt : ℕ := t - base
    have hTIndex : base + qt = t := by
      dsimp [qt]
      exact Nat.add_sub_of_le hBaseT
    rcases O.exists_periodRepresentativeFrom_repeat
        hij heq hBaseI qt with
      ⟨r, hrBase, hrPeriod, hRep⟩
    have hrStart : current + 1 ≤ r :=
      le_trans hCurrentBase hrBase
    have hrTerminal : r ≤ terminal := by
      dsimp [terminal, d] at hrPeriod ⊢
      omega
    have hMinR : O.value m ≤ O.value r := by
      apply hMin r hrStart
      rw [hEnd]
      exact hrTerminal
    rw [hTIndex] at hRep
    rw [hRep]
    exact hMinR

/--
選択済み future-minimum 列。

ここには「標準列であること」「値が strict に増えること」「非有界性」を保存しない。
それらは必要な theorem / predicate 側で追加する。
-/
structure FutureMinima (O : OddOrbit) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  minimum : ∀ j : ℕ, O.FutureMinimumAt (index j)

namespace FutureMinima

/-- strict selector の index は列添字自身以上。 -/
theorem index_ge
    {O : OddOrbit}
    (S : O.FutureMinima)
    (j : ℕ) :
    j ≤ S.index j := by
  induction j with
  | zero =>
      exact Nat.zero_le _
  | succ j ih =>
      have hStep := S.index_strict (Nat.lt_succ_self j)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hStep)

end FutureMinima
end OddOrbit
end Collatz3
