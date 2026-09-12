import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalGreedy

import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: lazy Ostrowski 正規形

Epifanio--Frougny--Gabriele--Mignosi--Shallit (2012) の Proposition 36(2) に対応する
lazy Ostrowski 表現を、現行 `UnitOstrowskiWeightSystem` 上で構成する。

論文の局所条件は

`d (h+1) = 0  ->  d h = a h`

である。ただしこれは表現の最上位桁より下でだけ要求する。
そこでまず、digit 上限をすべて使った prefix capacity

`C(t) = Σ_{i<t} a_i Q_i`

を定義し、`N ≤ C(t)` となる最小 `t` を canonical lazy length とする。
この長さを固定すると、lazy digits の complement `a_i-d_i` は現行 repo の
canonical greedy adjacency

`g (h+1) = a (h+1) -> g h = 0`

そのものになる。

この duality から

* lazy 表現の存在、
* lazy 表現の一意性、
* weighted sum の exact reconstruction

を axiom なしで導く。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/-- 最初の `t` 桁で使用可能な全 digit capacity。 -/
def ostrowskiLazyCapacity
    (W : UnitOstrowskiWeightSystem)
    (t : ℕ) : ℕ :=
  ostrowskiPrefixSum W.Q W.a t

@[simp] theorem ostrowskiLazyCapacity_zero
    (W : UnitOstrowskiWeightSystem) :
    ostrowskiLazyCapacity W 0 = 0 := rfl

@[simp] theorem ostrowskiLazyCapacity_succ
    (W : UnitOstrowskiWeightSystem)
    (t : ℕ) :
    ostrowskiLazyCapacity W (t + 1) =
      ostrowskiLazyCapacity W t + W.a t * W.Q t := rfl

/-- capacity は一桁増やすたび真に増加する。 -/
theorem ostrowskiLazyCapacity_lt_succ
    (W : UnitOstrowskiWeightSystem)
    (t : ℕ) :
    ostrowskiLazyCapacity W t < ostrowskiLazyCapacity W (t + 1) := by
  rw [ostrowskiLazyCapacity_succ]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (W.a_pos t) (W.q_pos t))

/-- capacity は少なくとも length だけ増える。 -/
theorem index_le_ostrowskiLazyCapacity
    (W : UnitOstrowskiWeightSystem) :
    ∀ t : ℕ, t ≤ ostrowskiLazyCapacity W t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have hinc := ostrowskiLazyCapacity_lt_succ W t
      omega

private theorem exists_le_ostrowskiLazyCapacity
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    ∃ t : ℕ, N ≤ ostrowskiLazyCapacity W t := by
  exact ⟨N, index_le_ostrowskiLazyCapacity W N⟩

/-- `N` を収容できる最小 lazy length。 -/
def ostrowskiLazyLength
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) : ℕ :=
  Nat.find (exists_le_ostrowskiLazyCapacity W N)

/-- canonical lazy length は `N` を収容する。 -/
theorem le_capacity_lazyLength
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    N ≤ ostrowskiLazyCapacity W (ostrowskiLazyLength W N) := by
  exact Nat.find_spec (exists_le_ostrowskiLazyCapacity W N)

/-- lazy length より短い prefix capacity では `N` を収容できない。 -/
theorem capacity_lt_of_lt_lazyLength
    (W : UnitOstrowskiWeightSystem)
    (N t : ℕ)
    (ht : t < ostrowskiLazyLength W N) :
    ostrowskiLazyCapacity W t < N := by
  by_contra h
  have hle : N ≤ ostrowskiLazyCapacity W t := by
    omega
  have hmin : ostrowskiLazyLength W N ≤ t := by
    change Nat.find (exists_le_ostrowskiLazyCapacity W N) ≤ t
    exact Nat.find_min' (exists_le_ostrowskiLazyCapacity W N) hle
  omega

@[simp] theorem ostrowskiLazyLength_zero
    (W : UnitOstrowskiWeightSystem) :
    ostrowskiLazyLength W 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  change Nat.find (exists_le_ostrowskiLazyCapacity W 0) ≤ 0
  exact Nat.find_min'
    (exists_le_ostrowskiLazyCapacity W 0)
    (by simp)

/-- 正の整数の lazy length は正。 -/
theorem ostrowskiLazyLength_pos
    (W : UnitOstrowskiWeightSystem)
    {N : ℕ}
    (hN : 0 < N) :
    0 < ostrowskiLazyLength W N := by
  by_contra h
  have hz : ostrowskiLazyLength W N = 0 := by omega
  have hs := le_capacity_lazyLength W N
  rw [hz, ostrowskiLazyCapacity_zero] at hs
  omega

/-- 最上位 capacity block は次 weight より小さい。 -/
theorem topCapacityBlock_lt_weight
    (W : UnitOstrowskiWeightSystem)
    {t : ℕ}
    (ht : 0 < t) :
    W.a (t - 1) * W.Q (t - 1) < W.Q t := by
  rcases t with (_ | t)
  · omega
  · rcases t with (_ | t)
    · rw [W.q_zero, W.q_one]
      have ha := W.a_pos 0
      simp
    · rw [show t + 2 - 1 = t + 1 by omega]
      rw [W.q_rec t]
      have hq := W.q_pos t
      omega

/--
lazy complement を作る greedy remainder は、その length の次 weight 未満。
-/
theorem lazyRemainder_lt_weight
    (W : UnitOstrowskiWeightSystem)
    {N : ℕ}
    (hN : 0 < N) :
    ostrowskiLazyCapacity W (ostrowskiLazyLength W N) - N <
      W.Q (ostrowskiLazyLength W N) := by
  let t := ostrowskiLazyLength W N
  change ostrowskiLazyCapacity W t - N < W.Q t
  have ht : 0 < t := by
    simpa [t] using ostrowskiLazyLength_pos W hN
  have hPrev : ostrowskiLazyCapacity W (t - 1) < N := by
    apply capacity_lt_of_lt_lazyLength W N
    simp [t]
    omega
  have hTop :
      W.a (t - 1) * W.Q (t - 1) < W.Q t := by
    exact topCapacityBlock_lt_weight W ht
  have hSucc :
      ostrowskiLazyCapacity W t =
        ostrowskiLazyCapacity W (t - 1) +
          W.a (t - 1) * W.Q (t - 1) := by
    calc
      ostrowskiLazyCapacity W t =
          ostrowskiLazyCapacity W ((t - 1) + 1) := by
            congr 1
            omega
      _ =
          ostrowskiLazyCapacity W (t - 1) +
            W.a (t - 1) * W.Q (t - 1) :=
        ostrowskiLazyCapacity_succ W (t - 1)
  rw [hSucc]
  omega

/--
有限 greedy 展開をその length で 0 延長すると global canonical digits になる。
-/
theorem ostrowskiGreedyDigits_canonical_of_lt_weight
    (W : UnitOstrowskiWeightSystem)
    {M t : ℕ}
    (hM : M < W.Q t) :
    IsCanonicalOstrowskiDigits W (ostrowskiGreedyDigits W M t) := by
  constructor
  · intro n
    by_cases hn : n < t
    · exact ostrowskiGreedyDigits_bounded_below_length W hM hn
    · have hz := ostrowskiGreedyDigits_eq_zero_of_length_le W M t n (by omega)
      rw [hz]
      exact Nat.zero_le _
  · intro n hMax
    by_cases hn : n + 1 < t
    · exact ostrowskiGreedyDigits_canonical_below_length W hM hn hMax
    · have hz := ostrowskiGreedyDigits_eq_zero_of_length_le W M t (n + 1) (by omega)
      rw [hz] at hMax
      have ha := W.a_pos (n + 1)
      omega

/-- digit-wise complement。 -/
def ostrowskiDigitComplement
    (W : UnitOstrowskiWeightSystem)
    (d : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  W.a n - d n

/-- bounded prefix では complement と元 digit の weighted sum が capacity に戻る。 -/
theorem complement_prefixSum_add
    (W : UnitOstrowskiWeightSystem)
    {d : ℕ → ℕ} :
    ∀ {t : ℕ},
      (∀ n < t, d n ≤ W.a n) →
      ostrowskiPrefixSum W.Q (ostrowskiDigitComplement W d) t +
          ostrowskiPrefixSum W.Q d t =
        ostrowskiLazyCapacity W t := by
  intro t
  induction t with
  | zero =>
      intro h
      rfl
  | succ t ih =>
      intro h
      have hPrev := ih (fun n hn => h n (by omega))
      change
        ostrowskiPrefixSum W.Q (fun n => W.a n - d n) t +
            ostrowskiPrefixSum W.Q d t =
          ostrowskiLazyCapacity W t at hPrev
      have hd : d t ≤ W.a t := h t (by omega)
      rw [ostrowskiPrefixSum_succ, ostrowskiPrefixSum_succ,
        ostrowskiLazyCapacity_succ]
      unfold ostrowskiDigitComplement
      have hsub : W.a t - d t + d t = W.a t :=
        Nat.sub_add_cancel hd
      calc
        (ostrowskiPrefixSum W.Q (fun n => W.a n - d n) t +
            (W.a t - d t) * W.Q t) +
            (ostrowskiPrefixSum W.Q d t + d t * W.Q t)
            =
            (ostrowskiPrefixSum W.Q (fun n => W.a n - d n) t +
                ostrowskiPrefixSum W.Q d t) +
              ((W.a t - d t) + d t) * W.Q t := by
                ring
        _ =
            ostrowskiLazyCapacity W t +
              ((W.a t - d t) + d t) * W.Q t := by
                rw [hPrev]
        _ =
            ostrowskiLazyCapacity W t +
              W.a t * W.Q t := by
                rw [hsub]


/-- capacity の monotonicity。 -/
theorem ostrowskiLazyCapacity_mono
    (W : UnitOstrowskiWeightSystem) :
    Monotone (ostrowskiLazyCapacity W) := by
  exact (strictMono_nat_of_lt_succ (ostrowskiLazyCapacity_lt_succ W)).monotone

/-- 任意 finite lazy prefix の complement を 0 延長する。 -/
def finiteLazyComplement
    (W : UnitOstrowskiWeightSystem)
    (d : ℕ → ℕ)
    (t n : ℕ) : ℕ :=
  if n < t then W.a n - d n else 0

/-- finite lazy adjacency の complement は global canonical adjacency。 -/
theorem finiteLazyComplement_canonical
    (W : UnitOstrowskiWeightSystem)
    {d : ℕ → ℕ}
    {t : ℕ}
    (B : ∀ n < t, d n ≤ W.a n)
    (L : ∀ n, n + 1 < t → d (n + 1) = 0 → d n = W.a n) :
    IsCanonicalOstrowskiDigits W (finiteLazyComplement W d t) := by
  constructor
  · intro n
    by_cases hn : n < t
    · simp [finiteLazyComplement, hn]
    · simp [finiteLazyComplement, hn]
  · intro n hMax
    by_cases hn : n + 1 < t
    · have hb := B (n + 1) hn
      have hZero : d (n + 1) = 0 := by
        simp [finiteLazyComplement, hn] at hMax
        omega
      have hPrev := L n hn hZero
      have hn0 : n < t := by omega
      simp [finiteLazyComplement, hn0, hPrev]
    · have hz : finiteLazyComplement W d t (n + 1) = 0 := by
        simp [finiteLazyComplement, hn]
      rw [hz] at hMax
      have ha := W.a_pos (n + 1)
      omega

/-- finite complement の prefix value は raw digit complement と同じ。 -/
theorem finiteLazyComplement_prefixSum
    (W : UnitOstrowskiWeightSystem)
    (d : ℕ → ℕ)
    (t : ℕ) :
    ostrowskiPrefixSum W.Q (finiteLazyComplement W d t) t =
      ostrowskiPrefixSum W.Q (ostrowskiDigitComplement W d) t := by
  apply ostrowskiPrefixSum_congr
  intro n hn
  simp [finiteLazyComplement, ostrowskiDigitComplement, hn]

/--
normalised finite lazy word の length は capacity から定まる `ostrowskiLazyLength` と一致する。
これは path から抽出した lazy digits の長さを canonical length に同定するために使う。
-/
theorem lazyLength_eq_of_normalizedPrefix
    (W : UnitOstrowskiWeightSystem)
    {N t : ℕ}
    {d : ℕ → ℕ}
    (B : ∀ n < t, d n ≤ W.a n)
    (L : ∀ n, n + 1 < t → d (n + 1) = 0 → d n = W.a n)
    (V : ostrowskiPrefixSum W.Q d t = N)
    (Top : 0 < t → 0 < d (t - 1)) :
    t = ostrowskiLazyLength W N := by
  by_cases ht : t = 0
  · subst t
    simp only [ostrowskiPrefixSum_zero] at V
    subst N
    exact (ostrowskiLazyLength_zero W).symm
  · have htPos : 0 < t := Nat.pos_of_ne_zero ht
    have C := finiteLazyComplement_canonical W B L
    have hCompSum := complement_prefixSum_add W B
    have hFinite := finiteLazyComplement_prefixSum W d t
    rw [← hFinite, V] at hCompSum
    have hNle : N ≤ ostrowskiLazyCapacity W t := by omega
    have hPrevLtN : ostrowskiLazyCapacity W (t - 1) < N := by
      let c := finiteLazyComplement W d t
      have hTopDigit : c (t - 1) < W.a (t - 1) := by
        have hb := B (t - 1) (by omega)
        have hp := Top htPos
        simp [c, finiteLazyComplement, show t - 1 < t by omega]
        omega
      have hLow := canonicalOstrowskiPrefix_lt_weight C (t - 1)
      have hSplit :
          ostrowskiPrefixSum W.Q c t =
            ostrowskiPrefixSum W.Q c (t - 1) +
              c (t - 1) * W.Q (t - 1) := by
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htPos)
        rfl
      have hCompLt :
          ostrowskiPrefixSum W.Q c t <
            W.a (t - 1) * W.Q (t - 1) := by
        rw [hSplit]
        have hQ := W.q_pos (t - 1)
        have ha := W.a_pos (t - 1)
        have hcLe : c (t - 1) ≤ W.a (t - 1) - 1 := by omega
        have hMul :
            c (t - 1) * W.Q (t - 1) ≤
              (W.a (t - 1) - 1) * W.Q (t - 1) :=
          Nat.mul_le_mul_right _ hcLe
        calc
          ostrowskiPrefixSum W.Q c (t - 1) +
                c (t - 1) * W.Q (t - 1)
              < W.Q (t - 1) + c (t - 1) * W.Q (t - 1) :=
            Nat.add_lt_add_right hLow _
          _ ≤ W.Q (t - 1) +
                (W.a (t - 1) - 1) * W.Q (t - 1) :=
            Nat.add_le_add_left hMul _
          _ = W.a (t - 1) * W.Q (t - 1) := by
            have haEq : W.a (t - 1) = (W.a (t - 1) - 1) + 1 := by omega
            rw [haEq]
            ring_nf
            simp
      have hCapSplit :
          ostrowskiLazyCapacity W t =
            ostrowskiLazyCapacity W (t - 1) +
              W.a (t - 1) * W.Q (t - 1) := by
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htPos)
        rfl
      dsimp [c] at hCompLt
      rw [hCapSplit] at hCompSum
      omega
    have hLenLe : ostrowskiLazyLength W N ≤ t := by
      by_contra hnot
      have hlt : t < ostrowskiLazyLength W N := by omega
      have hBad := capacity_lt_of_lt_lazyLength W N t hlt
      omega
    have hTle : t ≤ ostrowskiLazyLength W N := by
      by_contra hnot
      have hlt : ostrowskiLazyLength W N < t := by omega
      have hLePrev : ostrowskiLazyLength W N ≤ t - 1 := by omega
      have hCapMono := ostrowskiLazyCapacity_mono W hLePrev
      have hSpec := le_capacity_lazyLength W N
      omega
    exact Nat.le_antisymm hTle hLenLe

/-- lazy representation。length は `N` から canonical に決まるため primitive field に保存しない。 -/
structure LazyOstrowskiRepresentation
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) where
  digits : ℕ → ℕ
  zero_above : ∀ n, ostrowskiLazyLength W N ≤ n → digits n = 0
  bounded : ∀ n, n < ostrowskiLazyLength W N → digits n ≤ W.a n
  lazy : ∀ n, n + 1 < ostrowskiLazyLength W N →
    digits (n + 1) = 0 → digits n = W.a n
  value : ostrowskiPrefixSum W.Q digits (ostrowskiLazyLength W N) = N

namespace LazyOstrowskiRepresentation

/-- finite lazy word の complement を 0 延長した canonical greedy code。 -/
def complement
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (R : LazyOstrowskiRepresentation W N)
    (n : ℕ) : ℕ :=
  if n < ostrowskiLazyLength W N then
    W.a n - R.digits n
  else
    0

/-- lazy adjacency は complement 側では canonical greedy adjacency そのもの。 -/
theorem complement_canonical
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (R : LazyOstrowskiRepresentation W N) :
    IsCanonicalOstrowskiDigits W R.complement := by
  constructor
  · intro n
    by_cases hn : n < ostrowskiLazyLength W N
    · simp [complement, hn]
    · simp [complement, hn]
  · intro n hMax
    by_cases hn : n + 1 < ostrowskiLazyLength W N
    · have hb := R.bounded (n + 1) hn
      have hZero : R.digits (n + 1) = 0 := by
        simp [complement, hn] at hMax
        omega
      have hPrev := R.lazy n hn hZero
      have hn0 : n < ostrowskiLazyLength W N := by omega
      simp [complement, hn0, hPrev]
    · have hz : R.complement (n + 1) = 0 := by
        simp [complement, hn]
      rw [hz] at hMax
      have ha := W.a_pos (n + 1)
      omega

/-- complement の weighted value は `capacity - N`。 -/
theorem complement_value
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (R : LazyOstrowskiRepresentation W N) :
    ostrowskiPrefixSum W.Q R.complement (ostrowskiLazyLength W N) =
      ostrowskiLazyCapacity W (ostrowskiLazyLength W N) - N := by
  let t := ostrowskiLazyLength W N
  have hBound : ∀ n < t, R.digits n ≤ W.a n := by
    intro n hn
    exact R.bounded n hn
  have hComp :
      ostrowskiPrefixSum W.Q R.complement t =
        ostrowskiPrefixSum W.Q (ostrowskiDigitComplement W R.digits) t := by
    apply ostrowskiPrefixSum_congr
    intro n hn
    simp [LazyOstrowskiRepresentation.complement,
      ostrowskiDigitComplement, t, hn]
  have hSum := complement_prefixSum_add W hBound
  rw [← hComp, R.value] at hSum
  have hNC : N ≤ ostrowskiLazyCapacity W t := by
    simpa [t] using le_capacity_lazyLength W N
  change
    ostrowskiPrefixSum W.Q R.complement t =
      ostrowskiLazyCapacity W t - N
  omega

@[ext] theorem ext
    {R S : LazyOstrowskiRepresentation W N}
    (h : ∀ n, R.digits n = S.digits n) :
    R = S := by
  cases R
  cases S
  congr
  funext n
  exact h n

/-- lazy Ostrowski representation は一意。 -/
theorem unique
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (R S : LazyOstrowskiRepresentation W N) :
    R = S := by
  apply ext
  intro n
  let t := ostrowskiLazyLength W N
  by_cases hn : n < t
  · have CR := R.complement_canonical
    have CS := S.complement_canonical
    have hValue :
        ostrowskiPrefixSum W.Q R.complement t =
          ostrowskiPrefixSum W.Q S.complement t := by
      rw [R.complement_value, S.complement_value]
    have hEq := canonicalOstrowskiPrefix_unique CR CS hValue n hn
    have hRb := R.bounded n hn
    have hSb := S.bounded n hn
    simp [LazyOstrowskiRepresentation.complement, t, hn] at hEq
    omega
  · have hR := R.zero_above n (by simpa [t] using le_of_not_gt hn)
    have hS := S.zero_above n (by simpa [t] using le_of_not_gt hn)
    rw [hR, hS]

end LazyOstrowskiRepresentation

/--
canonical lazy digits。`N=0` は空表現、`N>0` は最小 capacity length で
`capacity-N` の finite canonical greedy code を complement する。
-/
noncomputable def lazyOstrowskiDigits
    (W : UnitOstrowskiWeightSystem)
    (N n : ℕ) : ℕ :=
  let t := ostrowskiLazyLength W N
  let M := ostrowskiLazyCapacity W t - N
  if n < t then
    W.a n - ostrowskiGreedyDigits W M t n
  else
    0

/-- canonical lazy digits から representation を構成できる。 -/
noncomputable def canonicalLazyOstrowskiRepresentation
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    LazyOstrowskiRepresentation W N := by
  let t := ostrowskiLazyLength W N
  let M := ostrowskiLazyCapacity W t - N
  by_cases hN : N = 0
  · subst N
    have ht : t = 0 := by simp only [ostrowskiLazyLength_zero, t]
    refine
      { digits := lazyOstrowskiDigits W 0
        zero_above := ?_
        bounded := ?_
        lazy := ?_
        value := ?_ }
    · intro n hn
      simp [lazyOstrowskiDigits, t, ht]
    · intro n hn
      simp only [ostrowskiLazyLength_zero, not_lt_zero] at hn
    · intro n hn
      simp only [ostrowskiLazyLength_zero, not_lt_zero] at hn
    · simp only [ht, ostrowskiPrefixSum_zero, t]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have htPos : 0 < t := by simpa [t] using ostrowskiLazyLength_pos W hNpos
    have hM : M < W.Q t := by
      simpa [M, t] using lazyRemainder_lt_weight W hNpos
    let g : ℕ → ℕ := ostrowskiGreedyDigits W M t
    have Cg : IsCanonicalOstrowskiDigits W g := by
      simpa [g] using ostrowskiGreedyDigits_canonical_of_lt_weight W hM
    refine
      { digits := lazyOstrowskiDigits W N
        zero_above := ?_
        bounded := ?_
        lazy := ?_
        value := ?_ }
    · intro n hn
      simp [lazyOstrowskiDigits, t, show ¬ n < t by omega]
    · intro n hn
      simp only [lazyOstrowskiDigits, hn]
      exact Nat.sub_le _ _
    · intro n hn hZero
      have hgb := Cg.bounded (n + 1)
      have hZero' :
          W.a (n + 1) - g (n + 1) = 0 := by
        simpa [lazyOstrowskiDigits, t, M, hn, g] using hZero
      have hgn : g (n + 1) = W.a (n + 1) := by
        omega
      have hgprev : g n = 0 :=
        Cg.previous_eq_zero_of_max hgn
      have hn0 : n < t := by
        omega
      simp [lazyOstrowskiDigits, t, M, hn0, g, hgprev]
    · have hgRecon : ostrowskiPrefixSum W.Q g t = M := by
        simpa [g] using ostrowskiGreedyDigits_reconstruct W htPos
      have hBound : ∀ n < t, g n ≤ W.a n := by
        intro n hn
        exact Cg.bounded n
      have hComp := complement_prefixSum_add W hBound
      have hDigitsEq :
          ostrowskiPrefixSum W.Q (lazyOstrowskiDigits W N) t =
            ostrowskiPrefixSum W.Q (ostrowskiDigitComplement W g) t := by
        apply ostrowskiPrefixSum_congr
        intro n hn
        simp [lazyOstrowskiDigits, t, M, hn, ostrowskiDigitComplement, g]
      rw [hgRecon] at hComp
      have hNC :
      N ≤ ostrowskiLazyCapacity W t := by
        simpa [t] using le_capacity_lazyLength W N
      change
        ostrowskiPrefixSum W.Q (lazyOstrowskiDigits W N) t = N
      omega

/-- lazy representation の公開一意性定理。 -/
theorem existsUnique_lazyOstrowskiRepresentation
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    ∃! _R : LazyOstrowskiRepresentation W N, True := by
  refine ⟨canonicalLazyOstrowskiRepresentation W N, trivial, ?_⟩
  intro R hR
  exact LazyOstrowskiRepresentation.unique R (canonicalLazyOstrowskiRepresentation W N)

end GenericRecordFerrers
end Experimental2
end Collatz3
