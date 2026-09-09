import CollatzLean.Collatz3.Semantics.OrbitFate
import CollatzLean.Collatz3.Semantics.FutureMinimum


/-!
# Collatz3: 軌道終局型と actual future minimum の接続

`FutureMinimum` の局所語彙自体は三分類を知らない。
このファイルで最終挙動の証明書と接続する。

* `HitsOne` では、到達した `1`（またはその後の `1`）が next minimum になる。
* `HasNontrivialRepeat` では、transient 部分と一周期分だけを有限探索すればよい。
* `DivergesToInfinity` では、current+1 の値を境界に使うと、十分後ろはそれより大きい。
  従って next minimum は有限区間だけを探索すれば構成的に得られる。
* 発散枝ではさらに、任意に遠い future minimum の値を `>1` にでき、指数は exact に `1`。

任意の無限自然数列に対する無条件の tail-minimum 選択はここでは主張しない。
-/

namespace Collatz3
namespace OddOrbit

/-- odd-only 軌道値は奇数なので常に正、従って `1` 以上。 -/
theorem one_le_value
    (O : OddOrbit)
    (n : ℕ) :
    1 ≤ O.value n := by
  rcases O.value_odd n with ⟨k, hk⟩
  omega

/--
第1枝では任意の current の後に next future minimum が構成的に存在する。
`1` への到達時刻が current より後ならその時刻、既に通過済みなら current+1 を取る。
-/
theorem exists_nextFutureMinimum_of_hitsOne
    (O : OddOrbit)
    (hHit : O.HitsOne)
    (i : ℕ) :
    ∃ j : ℕ, O.NextFutureMinimum i j := by
  rcases hHit with ⟨n, hn⟩
  by_cases hin : i < n
  · refine ⟨n, hin, ?_⟩
    intro t hit
    rw [hn]
    exact O.one_le_value t
  · have hni : n ≤ i := Nat.le_of_not_gt hin
    let j : ℕ := i + 1
    have hnj : n ≤ j := by
      dsimp [j]
      omega
    have hjOne : O.value j = 1 :=
      O.value_eq_one_of_hit_of_le hn hnj
    refine ⟨j, by dsimp [j]; omega, ?_⟩
    intro t hit
    rw [hjOne]
    exact O.one_le_value t

/--
第2枝でも任意の current の後に next future minimum が構成的に存在する。
repeat 開始以後は有限周期幅へ値を代表できるため、transient 部分と一周期分だけを有限探索する。
-/
theorem exists_nextFutureMinimum_of_nontrivialRepeat
    (O : OddOrbit)
    (hRepeat : O.HasNontrivialRepeat)
    (current : ℕ) :
    ∃ j : ℕ, O.NextFutureMinimum current j := by
  rcases hRepeat with ⟨i, j0, hij, heq, _hiOne⟩
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
第3枝では任意の current の後に next future minimum が構成的に存在する。
current+1 の値を境界に発散時刻を取り、それ以後は候補値より strict に大きいので、
有限区間探索の一般補題へ帰着する。
-/
theorem exists_nextFutureMinimum_of_diverges
    (O : OddOrbit)
    (hDiv : O.DivergesToInfinity)
    (i : ℕ) :
    ∃ j : ℕ, O.NextFutureMinimum i j := by
  rcases hDiv (O.value (i + 1)) with ⟨N, hN⟩
  let M : ℕ := max (i + 1) N
  apply O.exists_nextFutureMinimum_of_eventually_ge_candidate i M
  · exact Nat.le_max_left _ _
  · intro t hMt
    have hNle : N ≤ t :=
      le_trans (Nat.le_max_right _ _) (Nat.le_of_lt hMt)
    exact Nat.le_of_lt (hN t hNle)

/--
三分類の枝が証明書として与えられていれば、next future minimum の存在は完全に構成的。
どの枝かを無限軌道から選ぶ網羅性だけは `OrbitFateClassical` の責務である。
-/
theorem exists_nextFutureMinimum_of_fateWitness
    (O : OddOrbit)
    (i : ℕ)
    (hFate :
      O.HitsOne ∨
        O.HasNontrivialRepeat ∨
        O.DivergesToInfinity) :
    ∃ j : ℕ, O.NextFutureMinimum i j := by
  rcases hFate with hHit | hRest
  · exact O.exists_nextFutureMinimum_of_hitsOne hHit i
  · rcases hRest with hRepeat | hDiv
    · exact O.exists_nextFutureMinimum_of_nontrivialRepeat hRepeat i
    · exact O.exists_nextFutureMinimum_of_diverges hDiv i

/--
発散軌道では、任意に遠い位置に値 `>1` の future minimum が存在する。
-/
theorem exists_futureMinimum_one_lt_after_of_diverges
    (O : OddOrbit)
    (hDiv : O.DivergesToInfinity)
    (start : ℕ) :
    ∃ n : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n := by
  rcases hDiv 1 with ⟨N, hN⟩
  let a : ℕ := max start N
  rcases O.exists_nextFutureMinimum_of_diverges hDiv a with ⟨n, hNext⟩
  have hStart : start < n :=
    lt_of_le_of_lt (Nat.le_max_left _ _) hNext.1
  have hNle : N ≤ n :=
    le_trans (Nat.le_max_right _ _) (Nat.le_of_lt hNext.1)
  exact ⟨n, hStart, hNext.futureMinimumAt, hN n hNle⟩

/--
発散軌道では、任意に遠い future minimum anchor で odd-only 指数が exact に `1`。
-/
theorem exists_futureMinimum_exponent_eq_one_after_of_diverges
    (O : OddOrbit)
    (hDiv : O.DivergesToInfinity)
    (start : ℕ) :
    ∃ n : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 := by
  rcases O.exists_futureMinimum_one_lt_after_of_diverges hDiv start with
    ⟨n, hStart, hMin, hOneLt⟩
  exact
    ⟨n, hStart, hMin, hOneLt,
      FutureMinimumAt.exponent_eq_one_of_one_lt hMin hOneLt⟩

end OddOrbit
end Collatz3
