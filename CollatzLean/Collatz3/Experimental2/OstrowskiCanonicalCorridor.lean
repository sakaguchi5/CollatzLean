import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalGreedy
import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridorSharpEndpoint

/-!
# Collatz3 Experimental2: canonical Ostrowski digits から exact corridor chain へ

このファイルが中央橋の generic 核である。

Ostrowski weight system `W` と height `H` に対し、各 weight `Q n` が

* positive residual `k < Q(n+1)` 上で `H(Q n + k) = P n + H(k)`,
* endpoint で `H(Q n) = P n + ε n`

を満たすとする。

すると bounded digit 条件だけから各段の residual range が自動的に得られるため、
従来 theorem の仮定だった `ExactInverseCorridorChain` は canonical/Ostrowski 側で
別 certificate として渡す必要がない。

さらに canonical greedy digits を使えば任意の正整数 `N` について

`H(N) = Σ c_n P_n + ε(min supp c)`

が得られる。

canonical adjacency はこの exactness の証明には使わない。
その役割は `OstrowskiCanonicalGreedy` で証明した一意性だけである。
-/

namespace Collatz3
namespace Experimental2

/--
Ostrowski weight と exact inverse corridor を結ぶ最小 data。

continued fraction 自体や Farey certificate は保存せず、後続の bridge が
sharp corridor theorem からこの data を構成する。
-/
structure ExactOstrowskiCorridorSystem
    (H : ℕ → ℕ)
    (W : UnitOstrowskiWeightSystem) where
  P : ℕ → ℕ
  ε : ℕ → ℕ
  epsilon_le_one : ∀ n, ε n ≤ 1
  translate : ∀ n k, 0 < k → k < W.Q (n + 1) →
    H (W.Q n + k) = P n + H k
  endpoint : ∀ n, H (W.Q n) = P n + ε n

namespace ExactOstrowskiCorridorSystem

/-- `P` 側の Ostrowski weighted prefix sum。 -/
def pPrefix
    {H : ℕ → ℕ}
    {W : UnitOstrowskiWeightSystem}
    (S : ExactOstrowskiCorridorSystem H W)
    (d : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  ostrowskiPrefixSum S.P d n

@[simp] theorem pPrefix_zero
    {H : ℕ → ℕ}
    {W : UnitOstrowskiWeightSystem}
    (S : ExactOstrowskiCorridorSystem H W)
    (d : ℕ → ℕ) :
    S.pPrefix d 0 = 0 := rfl

@[simp] theorem pPrefix_succ
    {H : ℕ → ℕ}
    {W : UnitOstrowskiWeightSystem}
    (S : ExactOstrowskiCorridorSystem H W)
    (d : ℕ → ℕ)
    (n : ℕ) :
    S.pPrefix d (n + 1) = S.pPrefix d n + d n * S.P n := rfl

/--
同じ corridor を複数回通るが最後の residual は正のまま、という一般反復。
endpoint correction は一度も踏まない。
-/
theorem repeated_translation_with_positive_residual
    {H : ℕ → ℕ}
    {P Q Qnext d r : ℕ}
    (hd : 0 < d)
    (hr : 0 < r)
    (hRange : (d - 1) * Q + r < Qnext)
    (hTranslate : ∀ k, 0 < k → k < Qnext →
      H (Q + k) = P + H k) :
    H (d * Q + r) = d * P + H r := by
  revert hd hRange
  induction d with
  | zero =>
      intro hd hRange
      omega
  | succ d ih =>
      intro hd hRange
      by_cases hd0 : d = 0
      · subst d
        have hR : r < Qnext := by simpa using hRange
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          hTranslate r hr hR
      · have hdPos : 0 < d := Nat.pos_of_ne_zero hd0
        have hHeadRange : d * Q + r < Qnext := by
          simpa using hRange
        have hTailRange : (d - 1) * Q + r < Qnext := by
          have hMul : (d - 1) * Q ≤ d * Q :=
            Nat.mul_le_mul_right Q (Nat.sub_le d 1)
          omega
        have hTail := ih hdPos hTailRange
        have hResidualPos : 0 < d * Q + r := by omega
        have hHead := hTranslate (d * Q + r) hResidualPos hHeadRange
        calc
          H ((d + 1) * Q + r)
              = H (Q + (d * Q + r)) := by ring_nf
          _ = P + H (d * Q + r) := hHead
          _ = P + (d * P + H r) := by rw [hTail]
          _ = (d + 1) * P + H r := by ring

/--
既存 `ExactInverseCorridorChain` の tail の前に同じ corridor を `c>0` 個追加する。
必要な最大 residual は「最初の一個を除いた残り」なので
`(c-1)Q + tailResidual < Qnext` が exact な仮定である。
-/
theorem prepend_replicate_exactChain
    {H : ℕ → ℕ}
    {tail : List (ℕ × ℕ)}
    {k P Q Qnext c : ℕ}
    (hc : 0 < c)
    (Ctail : ExactInverseCorridorChain H tail k)
    (hTailPos : 0 < corridorQSum tail + k)
    (hRange : (c - 1) * Q + (corridorQSum tail + k) < Qnext)
    (hTranslate : ∀ r, 0 < r → r < Qnext →
      H (Q + r) = P + H r) :
    ExactInverseCorridorChain H
      (List.replicate c (P, Q) ++ tail) k := by
  revert hc hRange
  induction c with
  | zero =>
      intro hc hRange
      omega
  | succ c ih =>
      intro hc hRange
      by_cases hc0 : c = 0
      · subst c
        have hTailRange : corridorQSum tail + k < Qnext := by
          simpa using hRange
        rw [List.replicate_succ, List.replicate_zero]
        apply exactInverseCorridorChain_cons
        · exact hTranslate (corridorQSum tail + k) hTailPos hTailRange
        · exact Ctail
      · have hcPos : 0 < c := Nat.pos_of_ne_zero hc0
        have hSmallRange :
            (c - 1) * Q + (corridorQSum tail + k) < Qnext := by
          have hMul : (c - 1) * Q ≤ c * Q :=
            Nat.mul_le_mul_right Q (Nat.sub_le c 1)
          have hBig : c * Q + (corridorQSum tail + k) < Qnext := by
            simpa using hRange
          omega
        have Csmall := ih hcPos hSmallRange
        have hResidual :
            corridorQSum (List.replicate c (P, Q) ++ tail) + k =
              c * Q + (corridorQSum tail + k) := by
          rw [corridorQSum_append, corridorQSum_replicate]
          omega
        have hResidualPos :
            0 < corridorQSum (List.replicate c (P, Q) ++ tail) + k := by
          rw [hResidual]
          omega
        have hResidualLt :
            corridorQSum (List.replicate c (P, Q) ++ tail) + k < Qnext := by
          rw [hResidual]
          simpa using hRange
        rw [List.replicate_succ]
        apply exactInverseCorridorChain_cons
        · exact hTranslate _ hResidualPos hResidualLt
        · exact Csmall

/--
最小非零 digit `j` を一個 endpoint として残した exact chain が bounded digits から自動生成される。

出力 `xs` は高位 digit を順に並べ、`j` 番目だけ一個減らした corridor 列。
従って

* `corridorQSum xs + Q j = Σ_{i<t} d i Q i`,
* `corridorPSum xs + P j = Σ_{i<t} d i P i`

も同時に得る。
-/
theorem exists_exactChain_of_boundedDigits
    {H : ℕ → ℕ}
    {W : UnitOstrowskiWeightSystem}
    (S : ExactOstrowskiCorridorSystem H W)
    {d : ℕ → ℕ}
    (B : IsBoundedOstrowskiDigits W d) :
    ∀ {t j : ℕ},
      j < t →
      0 < d j →
      (∀ i < j, d i = 0) →
      ∃ xs : List (ℕ × ℕ),
        ExactInverseCorridorChain H xs (W.Q j) ∧
        corridorQSum xs + W.Q j = ostrowskiPrefixSum W.Q d t ∧
        corridorPSum xs + S.P j = S.pPrefix d t := by
  intro t
  induction t with
  | zero =>
      intro j hj hPos hZero
      omega
  | succ n ih =>
      intro j hj hJPos hBelowZero
      by_cases hTopZero : d n = 0
      · have hjne : j ≠ n := by
          intro h
          subst j
          omega
        have hjn : j < n := by omega
        obtain ⟨xs, Cxs, hQ, hP⟩ := ih hjn hJPos hBelowZero
        refine ⟨xs, Cxs, ?_, ?_⟩
        · rw [ostrowskiPrefixSum_succ, hTopZero]
          simp only [zero_mul, add_zero]
          exact hQ
        · rw [pPrefix_succ, hTopZero]
          simp only [zero_mul, add_zero]
          exact hP
      · have hTopPos : 0 < d n := Nat.pos_of_ne_zero hTopZero
        by_cases hjnEq : j = n
        · subst j
          have hQlowZero : ostrowskiPrefixSum W.Q d n = 0 :=
            ostrowskiPrefixSum_eq_zero_of_digits_eq_zero hBelowZero
          have hPlowZero : S.pPrefix d n = 0 := by
            unfold pPrefix
            exact ostrowskiPrefixSum_eq_zero_of_digits_eq_zero hBelowZero
          have hRange0 := boundedOstrowskiResidual_lt_nextWeight B hTopPos
          rw [hQlowZero, Nat.add_zero] at hRange0
          let xs := List.replicate (d n - 1) (S.P n, W.Q n)
          have Cxs : ExactInverseCorridorChain H xs (W.Q n) := by
            dsimp [xs]
            exact exactInverseCorridorChain_replicate
              (H := H)
              (P := S.P n)
              (Q := W.Q n)
              (Qn := W.Q (n + 1))
              (c := d n - 1)
              (W.q_pos n)
              hRange0
              (S.translate n)
          refine ⟨xs, Cxs, ?_, ?_⟩
          · dsimp [xs]
            rw [corridorQSum_replicate, hQlowZero]
            have hdEq : d n - 1 + 1 = d n := by omega
            calc
              (d n - 1) * W.Q n + W.Q n
                  = (d n - 1 + 1) * W.Q n := by ring
              _ = d n * W.Q n := by rw [hdEq]
              _ = 0 + d n * W.Q n := by simp
          · dsimp [xs]
            rw [corridorPSum_replicate, hPlowZero]
            have hdEq : d n - 1 + 1 = d n := by omega
            calc
              (d n - 1) * S.P n + S.P n
                  = (d n - 1 + 1) * S.P n := by ring
              _ = d n * S.P n := by rw [hdEq]
              _ = 0 + d n * S.P n := by simp
        · have hjn : j < n := by omega
          obtain ⟨tail, Ctail, hQtail, hPtail⟩ :=
            ih hjn hJPos hBelowZero
          have hLowerPos : 0 < ostrowskiPrefixSum W.Q d n :=
            ostrowskiPrefixSum_pos_of_digit_pos
              (W.q_pos j) hJPos hjn
          have hTailPos : 0 < corridorQSum tail + W.Q j := by
            rw [hQtail]
            exact hLowerPos
          have hRange0 := boundedOstrowskiResidual_lt_nextWeight B hTopPos
          have hRange :
              (d n - 1) * W.Q n +
                  (corridorQSum tail + W.Q j) < W.Q (n + 1) := by
            rw [hQtail]
            exact hRange0
          let xs := List.replicate (d n) (S.P n, W.Q n) ++ tail
          have Cxs : ExactInverseCorridorChain H xs (W.Q j) := by
            dsimp [xs]
            exact prepend_replicate_exactChain
              hTopPos Ctail hTailPos hRange (S.translate n)
          refine ⟨xs, Cxs, ?_, ?_⟩
          · dsimp [xs]
            rw [corridorQSum_append, corridorQSum_replicate]
            rw [← hQtail]
            omega
          · dsimp [xs]
            rw [corridorPSum_append, corridorPSum_replicate]
            rw [← hPtail]
            omega

/--
bounded digits だけから得られる exact scalar-height formula。

`ExactInverseCorridorChain` は仮定ではなく前 theorem で自動生成される。
補正は最小非零 digit `j` の endpoint correction `ε j` 一個だけである。
-/
theorem height_eq_pPrefix_add_endpointCorrection_of_boundedDigits
    {H : ℕ → ℕ}
    {W : UnitOstrowskiWeightSystem}
    (S : ExactOstrowskiCorridorSystem H W)
    {d : ℕ → ℕ}
    (B : IsBoundedOstrowskiDigits W d)
    {t j : ℕ}
    (hj : j < t)
    (hJPos : 0 < d j)
    (hBelowZero : ∀ i < j, d i = 0) :
    H (ostrowskiPrefixSum W.Q d t) =
      S.pPrefix d t + S.ε j := by
  obtain ⟨xs, Cxs, hQ, hP⟩ :=
    S.exists_exactChain_of_boundedDigits B hj hJPos hBelowZero
  have hComp := exactInverseCorridorChain_to_endpoint
    (H := H)
    (xs := xs)
    (P := S.P j)
    (Q := W.Q j)
    (ε := S.ε j)
    Cxs (S.endpoint j)
  rw [hQ] at hComp
  omega

/-- positive weighted prefix は、その範囲に非零 digit を少なくとも一つ持つ。 -/
theorem exists_positive_digit_of_positive_prefix
    {w d : ℕ → ℕ}
    {t : ℕ}
    (hPos : 0 < ostrowskiPrefixSum w d t) :
    ∃ j < t, 0 < d j := by
  by_contra hNot
  push Not at hNot
  have hZero : ∀ i < t, d i = 0 := by
    intro i hi
    have h := hNot i hi
    omega
  have hSumZero :
      ostrowskiPrefixSum w d t = 0 :=
    ostrowskiPrefixSum_eq_zero_of_digits_eq_zero
      (w := w) (d := d) (n := t) hZero
  omega

/-- 正整数の canonical digits には support 内に必ず正の digit がある。 -/
theorem canonicalOstrowskiDigits_exists_positive
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (hN : 0 < N) :
    ∃ j < N + 1, 0 < canonicalOstrowskiDigits W N j := by
  have hReconstruct := canonicalOstrowskiDigits_reconstruct W N
  have hPos :
      0 < ostrowskiPrefixSum W.Q (canonicalOstrowskiDigits W N) (N + 1) := by
    rw [hReconstruct]
    exact hN
  exact exists_positive_digit_of_positive_prefix hPos

/--
正整数 `N` の canonical Ostrowski digits における最小非零 index。
-/
def canonicalOstrowskiMinIndex
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (hN : 0 < N) : ℕ :=
  Nat.find (canonicalOstrowskiDigits_exists_positive W N hN)

/-- canonical 最小非零 index は support 範囲内。 -/
theorem canonicalOstrowskiMinIndex_lt
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (hN : 0 < N) :
    canonicalOstrowskiMinIndex W N hN < N + 1 := by
  exact (Nat.find_spec (canonicalOstrowskiDigits_exists_positive W N hN)).1

/-- canonical 最小非零 index の digit は正。 -/
theorem canonicalOstrowskiMinIndex_digit_pos
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (hN : 0 < N) :
    0 < canonicalOstrowskiDigits W N (canonicalOstrowskiMinIndex W N hN) := by
  exact (Nat.find_spec (canonicalOstrowskiDigits_exists_positive W N hN)).2

/-- canonical 最小非零 index より下の digit は全て `0`。 -/
theorem canonicalOstrowskiDigits_eq_zero_below_min
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (hN : 0 < N)
    {i : ℕ}
    (hi : i < canonicalOstrowskiMinIndex W N hN) :
    canonicalOstrowskiDigits W N i = 0 := by
  have hNot :
      ¬(i < N + 1 ∧ 0 < canonicalOstrowskiDigits W N i) := by
    apply Nat.find_min (canonicalOstrowskiDigits_exists_positive W N hN)
    simpa [canonicalOstrowskiMinIndex] using hi
  have hiSupport : i < N + 1 := by
    exact lt_trans hi (canonicalOstrowskiMinIndex_lt W N hN)
  by_contra hZero
  have hPos : 0 < canonicalOstrowskiDigits W N i := Nat.pos_of_ne_zero hZero
  exact hNot ⟨hiSupport, hPos⟩

/--
任意の正整数 `N` に対する canonical Ostrowski exact height formula。

ここには `ExactInverseCorridorChain` の仮定は現れない。
chain は canonical digits の boundedness から内部で自動生成される。
-/
theorem canonicalOstrowski_height_formula
    {H : ℕ → ℕ}
    {W : UnitOstrowskiWeightSystem}
    (S : ExactOstrowskiCorridorSystem H W)
    (N : ℕ)
    (hN : 0 < N) :
    H N =
      S.pPrefix (canonicalOstrowskiDigits W N) (N + 1) +
        S.ε (canonicalOstrowskiMinIndex W N hN) := by
  let j := canonicalOstrowskiMinIndex W N hN
  have hj : j < N + 1 := canonicalOstrowskiMinIndex_lt W N hN
  have hJPos : 0 < canonicalOstrowskiDigits W N j :=
    canonicalOstrowskiMinIndex_digit_pos W N hN
  have hBelow : ∀ i < j, canonicalOstrowskiDigits W N i = 0 := by
    intro i hi
    exact canonicalOstrowskiDigits_eq_zero_below_min W N hN hi
  have hFormula := S.height_eq_pPrefix_add_endpointCorrection_of_boundedDigits
    (canonicalOstrowskiDigits_bounded W N) hj hJPos hBelow
  rw [canonicalOstrowskiDigits_reconstruct W N] at hFormula
  exact hFormula

end ExactOstrowskiCorridorSystem

end Experimental2
end Collatz3
