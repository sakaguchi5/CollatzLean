import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalArithmetic

/-!
# Collatz3 Experimental2: canonical Ostrowski greedy normal form

`UnitOstrowskiWeightSystem` に対し、上位 weight から Euclidean division で digit を決める
有限 greedy 展開を定義する。

長さ `t+1` の展開では最上位 digit を

`N / Q t`

とし、下位桁は residual `N % Q t` を長さ `t` で再帰的に展開する。

`N < Q(t+1)` のもとで、continued-fraction 型再帰から

* digit bound,
* 最大 digit の直下が `0`,
* weighted sum の exact reconstruction

が自動的に従う。

さらに `Q(N+1) > N` を使って、任意の `N` に canonical digits を与える。
canonicality は exact corridor law のためではなく、一意な住所を選ぶ normal form である。
-/

namespace Collatz3
namespace Experimental2

/--
長さ `t` の finite greedy Ostrowski digits。

`t=0` では全 digit を `0` とし、`t+1` では index `t` に quotient、
それより下を remainder の greedy 展開にする。
-/
def ostrowskiGreedyDigits
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, n =>
      if n = t then N / W.Q t
      else ostrowskiGreedyDigits W (N % W.Q t) t n

/-- finite greedy digits は指定長さ以上では `0`。 -/
theorem ostrowskiGreedyDigits_eq_zero_of_length_le
    (W : UnitOstrowskiWeightSystem) :
    ∀ (N t n : ℕ), t ≤ n → ostrowskiGreedyDigits W N t n = 0 := by
  intro N t
  induction t generalizing N with
  | zero =>
      intro n hn
      rfl
  | succ t ih =>
      intro n hn
      have hne : n ≠ t := by omega
      rw [ostrowskiGreedyDigits]
      simp only [hne, ↓reduceIte]
      exact ih (N % W.Q t) n (by omega)

/--
長さ `t>0` の greedy 展開は、上位 bound の有無にかかわらず元の `N` を exact に復元する。
最下位 weight が `Q 0=1` なので最後の remainder は必ず `0` になる。
-/
theorem ostrowskiGreedyDigits_reconstruct
    (W : UnitOstrowskiWeightSystem) :
    ∀ {t N : ℕ}, 0 < t →
      ostrowskiPrefixSum W.Q (ostrowskiGreedyDigits W N t) t = N := by
  intro t
  induction t with
  | zero =>
      intro N ht
      omega
  | succ t ih =>
      intro N ht
      rcases t with (_ | t)
      · rw [ostrowskiPrefixSum_succ, ostrowskiPrefixSum_zero,
          ostrowskiGreedyDigits, W.q_zero]
        simp
      · let R := N % W.Q (t + 1)
        have hQPos : 0 < W.Q (t + 1) := W.q_pos (t + 1)
        have hR : R < W.Q (t + 1) := by
          dsimp [R]
          exact Nat.mod_lt _ hQPos
        have hLow := ih (N := R) (by omega)
        have hPrefixCongr :
            ostrowskiPrefixSum W.Q
                (ostrowskiGreedyDigits W N (t + 2)) (t + 1) =
              ostrowskiPrefixSum W.Q
                (ostrowskiGreedyDigits W R (t + 1)) (t + 1) := by
          apply ostrowskiPrefixSum_congr
          intro j hj
          rw [ostrowskiGreedyDigits]
          have hjne : j ≠ t + 1 := by omega
          simp only [hjne, ↓reduceIte]
          rfl
        rw [ostrowskiPrefixSum_succ, hPrefixCongr, hLow]
        rw [ostrowskiGreedyDigits]
        simp only [↓reduceIte]
        dsimp [R]
        have hDiv := Nat.mod_add_div N (W.Q (t + 1))
        simpa [Nat.mul_comm] using hDiv

/--
`N<Q t` なら長さ `t` の greedy 展開の全 digit は partial quotient 上限以下。
-/
theorem ostrowskiGreedyDigits_bounded_below_length
    (W : UnitOstrowskiWeightSystem) :
    ∀ {t N n : ℕ},
      N < W.Q t → n < t →
      ostrowskiGreedyDigits W N t n ≤ W.a n := by
  intro t
  induction t with
  | zero =>
      intro N n hN hn
      omega
  | succ t ih =>
      intro N n hN hn
      by_cases hnt : n = t
      · subst n
        rw [ostrowskiGreedyDigits]
        simp only [↓reduceIte]
        rcases t with (_ | t)
        · -- 最下位 digit
          have hN' : N < W.a 0 + 1 := by
            simpa [W.q_one] using hN
          rw [W.q_zero]
          simp only [Nat.div_one]
          omega
        · -- t = t+1
          have hN' : N < W.Q (t + 2) := by
            simpa [Nat.add_assoc] using hN
          apply ostrowskiGreedyDigit_le_partialQuotient
              (Qprev := W.Q t)
              (Q := W.Q (t + 1))
              (Qnext := W.Q (t + 2))
              (a := W.a (t + 1))
              (R := N)
          · exact W.q_pos (t + 1)
          · exact W.q_lt_succ t
          · exact W.q_rec t
          · exact hN'
      · rw [ostrowskiGreedyDigits]
        simp only [hnt, ↓reduceIte]
        have hQPos : 0 < W.Q t := W.q_pos t
        have hRem : N % W.Q t < W.Q t :=
          Nat.mod_lt _ hQPos
        exact ih hRem (by omega)

/--
finite greedy 展開は、その長さの上限 `N<Q t` のもとで canonical adjacency も満たす。
-/
theorem ostrowskiGreedyDigits_canonical_below_length
    (W : UnitOstrowskiWeightSystem) :
    ∀ {t N n : ℕ},
      N < W.Q t → n + 1 < t →
      ostrowskiGreedyDigits W N t (n + 1) = W.a (n + 1) →
      ostrowskiGreedyDigits W N t n = 0 := by
  intro t
  induction t with
  | zero =>
      intro N n hN hn hMax
      omega
  | succ t ih =>
      intro N n hN hn hMax
      by_cases hTop : n + 1 = t
      · rcases t with (_ | t)
        · omega
        · have hn : n = t := by omega
          subst n
          have hQtPos : 0 < W.Q (t + 1) := W.q_pos (t + 1)
          have hQprevPos : 0 < W.Q t := W.q_pos t
          have hTopDigit :
              N / W.Q (t + 1) = W.a (t + 1) := by
            simpa [ostrowskiGreedyDigits] using hMax
          have hDivEq := Nat.mod_add_div N (W.Q (t + 1))
          have hDivEq' :
              N % W.Q (t + 1) +
                  W.a (t + 1) * W.Q (t + 1) = N := by
            calc
              N % W.Q (t + 1) + W.a (t + 1) * W.Q (t + 1)
                  = N % W.Q (t + 1) +
                      W.Q (t + 1) * W.a (t + 1) := by ring
              _ = N := by rw [← hTopDigit]; exact hDivEq
          have hRec := W.q_rec t
          have hRemLtPrev : N % W.Q (t + 1) < W.Q t := by
            rw [hRec] at hN
            omega
          rw [ostrowskiGreedyDigits]
          have hne : t ≠ t + 1 := by omega
          simp only [hne, ↓reduceIte]
          rw [ostrowskiGreedyDigits]
          simp only [↓reduceIte]
          exact Nat.div_eq_of_lt hRemLtPrev
      · have hBelow : n + 1 < t := by omega
        rw [ostrowskiGreedyDigits] at hMax ⊢
        have hneSucc : n + 1 ≠ t := by exact hTop
        have hne : n ≠ t := by omega
        simp only [hneSucc, hne, ↓reduceIte] at hMax ⊢
        have hQPos := W.q_pos t
        have hRem : N % W.Q t < W.Q t := Nat.mod_lt _ hQPos
        exact ih hRem hBelow hMax

/--
任意 `N` の canonical Ostrowski digits。

`Q(N+1)>N` なので長さ `N+1` の finite greedy expansion を採用すれば十分。
-/
def canonicalOstrowskiDigits
    (W : UnitOstrowskiWeightSystem)
    (N n : ℕ) : ℕ :=
  ostrowskiGreedyDigits W N (N + 1) n

/-- canonical digits は index `N+1` 以上で `0`。 -/
theorem canonicalOstrowskiDigits_eq_zero_of_large
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    {n : ℕ}
    (hn : N + 1 ≤ n) :
    canonicalOstrowskiDigits W N n = 0 := by
  exact ostrowskiGreedyDigits_eq_zero_of_length_le W N (N + 1) n hn

/-- canonical digits は全 index で digit bound を満たす。 -/
theorem canonicalOstrowskiDigits_bounded
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    IsBoundedOstrowskiDigits W (canonicalOstrowskiDigits W N) := by
  intro n
  by_cases hn : n < N + 1
  · exact ostrowskiGreedyDigits_bounded_below_length W
      (W.self_lt_next_q N) hn
  · have hZero := canonicalOstrowskiDigits_eq_zero_of_large W N
      (n := n) (by omega)
    rw [hZero]
    exact Nat.zero_le _

/-- canonical digits は最大 digit の直下が `0` という normal-form 条件も満たす。 -/
theorem canonicalOstrowskiDigits_canonical
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    IsCanonicalOstrowskiDigits W (canonicalOstrowskiDigits W N) := by
  refine ⟨canonicalOstrowskiDigits_bounded W N, ?_⟩
  intro n hMax
  by_cases hInside : n + 1 < N + 1
  · exact ostrowskiGreedyDigits_canonical_below_length W
      (W.self_lt_next_q N) hInside hMax
  · have hZero : canonicalOstrowskiDigits W N (n + 1) = 0 :=
      canonicalOstrowskiDigits_eq_zero_of_large W N (by omega)
    have haPos := W.a_pos (n + 1)
    rw [hZero] at hMax
    omega

/-- canonical digits は `N` を exact に再構成する。 -/
theorem canonicalOstrowskiDigits_reconstruct
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    ostrowskiPrefixSum W.Q (canonicalOstrowskiDigits W N) (N + 1) = N := by
  exact ostrowskiGreedyDigits_reconstruct W (by omega)

/--
canonical prefix の最上位 digit は weighted sum を `Q t` で割った商に等しい。
-/
theorem canonicalOstrowskiTopDigit_eq_div
    {W : UnitOstrowskiWeightSystem}
    {d : ℕ → ℕ}
    (C : IsCanonicalOstrowskiDigits W d)
    (t : ℕ) :
    ostrowskiPrefixSum W.Q d (t + 1) / W.Q t = d t := by
  have hQPos := W.q_pos t
  have hLow := canonicalOstrowskiPrefix_lt_weight C t
  rw [ostrowskiPrefixSum_succ]
  apply Nat.div_eq_of_lt_le
  · omega
  · calc
      ostrowskiPrefixSum W.Q d t + d t * W.Q t
          < W.Q t + d t * W.Q t := Nat.add_lt_add_right hLow _
      _ = (d t + 1) * W.Q t := by ring

/--
同じ weighted sum を持つ canonical prefix は、その範囲の digit が一点ごとに一致する。
これが finite canonical Ostrowski representation の一意性。
-/
theorem canonicalOstrowskiPrefix_unique
    {W : UnitOstrowskiWeightSystem}
    {d e : ℕ → ℕ}
    (Cd : IsCanonicalOstrowskiDigits W d)
    (Ce : IsCanonicalOstrowskiDigits W e) :
    ∀ {t : ℕ},
      ostrowskiPrefixSum W.Q d t = ostrowskiPrefixSum W.Q e t →
      ∀ n < t, d n = e n := by
  intro t
  induction t with
  | zero =>
      intro h n hn
      omega
  | succ t ih =>
      intro h n hn
      have hTopD := canonicalOstrowskiTopDigit_eq_div Cd t
      have hTopE := canonicalOstrowskiTopDigit_eq_div Ce t
      have hTop : d t = e t := by
        rw [h] at hTopD
        omega
      by_cases hnt : n = t
      · simpa [hnt] using hTop
      · have hLowEq :
            ostrowskiPrefixSum W.Q d t = ostrowskiPrefixSum W.Q e t := by
          rw [ostrowskiPrefixSum_succ, ostrowskiPrefixSum_succ, hTop] at h
          omega
        exact ih hLowEq n (by omega)

/--
任意の canonical finite-support 表現は、十分大きい prefix 上で
`canonicalOstrowskiDigits` と一致する。

`canonicalOstrowskiDigits W N` が一意な canonical 住所であることの実用形。
-/
theorem canonicalOstrowskiDigits_unique_of_prefix
    (W : UnitOstrowskiWeightSystem)
    (N t : ℕ)
    {d : ℕ → ℕ}
    (Cd : IsCanonicalOstrowskiDigits W d)
    (hSum : ostrowskiPrefixSum W.Q d t = N)
    (hCanonSupport : N + 1 ≤ t) :
    ∀ n < N + 1,
      d n = canonicalOstrowskiDigits W N n := by
  have Ccanon := canonicalOstrowskiDigits_canonical W N
  have hStable : ∀ s : ℕ,
      ostrowskiPrefixSum W.Q (canonicalOstrowskiDigits W N)
          (N + 1 + s) = N := by
    intro s
    induction s with
    | zero =>
        simpa using canonicalOstrowskiDigits_reconstruct W N
    | succ s ih =>
        rw [show N + 1 + (s + 1) = (N + 1 + s) + 1 by omega]
        rw [ostrowskiPrefixSum_succ, ih]
        have hZero :
            canonicalOstrowskiDigits W N (N + 1 + s) = 0 :=
          canonicalOstrowskiDigits_eq_zero_of_large W N (by omega)
        rw [hZero]
        simp
  obtain ⟨s, ht⟩ := Nat.exists_eq_add_of_le hCanonSupport
  have hCanonTail :
      ostrowskiPrefixSum W.Q (canonicalOstrowskiDigits W N) t = N := by
    rw [ht]
    exact hStable s
  have hEq :
      ostrowskiPrefixSum W.Q d t =
        ostrowskiPrefixSum W.Q (canonicalOstrowskiDigits W N) t := by
    rw [hSum, hCanonTail]
  have hUnique := canonicalOstrowskiPrefix_unique Cd Ccanon hEq
  intro n hn
  exact hUnique n (lt_of_lt_of_le hn hCanonSupport)

end Experimental2
end Collatz3
