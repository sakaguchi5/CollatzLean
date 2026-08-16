import CollatzLean.Collatz2.CSTMicro.CriticalCrossingIndex
import CollatzLean.Collatz2.CSTMicro.InversePathSum

/-!
# Critical boundary residue = finite Beatty / Xi truncation

critical boundary の one positions は

  beattyIndex n = floor (n log₂ 3)

なので、Rozier inverse path sum は

  - Σ_{n < m} 2^(beattyIndex n) 3^(-(n+1))

になる。

これは

  Ξ = -(1/3) Σ_{n>=0} 2^floor(n log₂3) 3^(-n)

の最初の m 項そのもの。

ここでは無限 2-adic 和を導入せず、precision `e` の finite truncation class を作り、
first-passage length `k` について `e=k-1` とすると

  leastRepresentative(criticalBoundaryWord k)
      ≡ XiTruncation(e,m)  (mod 2^e)

を exact に証明する。
-/

namespace Collatz2
namespace CSTMicro

/-- Beatty weighted positive sum `Σ 2^q_n 3^(-(n+1))`。 -/
def beattyInverseContribution :
    (e : ℕ) → ℕ → ZMod (2 ^ e)
  | _e, 0 => 0
  | e, n + 1 =>
      beattyInverseContribution e n +
        (2 : ZMod (2 ^ e)) ^ beattyIndex n *
          invThreePow e (n + 1)

/-- critical Ξ の finite truncation class。 -/
def criticalXiTruncationClass
    (e m : ℕ) : ZMod (2 ^ e) :=
  - beattyInverseContribution e m

@[simp] theorem beattyInverseContribution_zero (e : ℕ) :
    beattyInverseContribution e 0 = 0 := rfl

@[simp] theorem beattyInverseContribution_succ (e n : ℕ) :
    beattyInverseContribution e (n + 1) =
      beattyInverseContribution e n +
        (2 : ZMod (2 ^ e)) ^ beattyIndex n *
          invThreePow e (n + 1) := rfl

/-- odd inverse scan の append formula。 -/
theorem oddInverseContributionScan_append
    (K : ℕ)
    (u v : ParityWord)
    (i a : ℕ) :
    oddInverseContributionScan K (u ++ v) i a =
      oddInverseContributionScan K u i a +
        oddInverseContributionScan K v
          (i + u.length) (a + oddCount u) := by
  induction u generalizing i a with
  | nil =>
      simp [oddInverseContributionScan, oddCount]
  | cons b u ih =>
      cases b
      · have hih := ih (i := i + 1) (a := a)
        simpa [oddInverseContributionScan, oddCount_false_cons,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hih
      · have hih := ih (i := i + 1) (a := a + 1)
        have hih' :
            oddInverseContributionScan K (u ++ v) (i + 1) (a + 1) =
              oddInverseContributionScan K u (i + 1) (a + 1) +
                oddInverseContributionScan K v
                  (i + (true :: u).length)
                  (a + oddCount (true :: u)) := by
          simpa [
            oddCount_true_cons,
            Nat.add_assoc,
            Nat.add_left_comm,
            Nat.add_comm
          ] using hih
        change
          (2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
              oddInverseContributionScan K (u ++ v) (i + 1) (a + 1)
            =
          ((2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
              oddInverseContributionScan K u (i + 1) (a + 1)) +
            oddInverseContributionScan K v
              (i + (true :: u).length)
              (a + oddCount (true :: u))
        rw [hih']
        exact (add_assoc _ _ _).symm
/-- critical mechanical prefix の inverse scan は Beatty sum そのもの。 -/
theorem oddInverseContributionScan_criticalSturmianPrefix
    (e n : ℕ) :
    oddInverseContributionScan e (criticalSturmianPrefix n) 0 0 =
      beattyInverseContribution e (criticalPrefixHeight n) := by
  induction n with
  | zero =>
      simp [
        criticalSturmianPrefix,
        oddInverseContributionScan,
        criticalPrefixHeight
      ]
  | succ n ih =>
      rw [criticalSturmianPrefix]
      rw [oddInverseContributionScan_append]
      rw [ih]
      rw [
        criticalSturmianPrefix_length,
        criticalSturmianPrefix_oddCount
      ]
      cases hbit : criticalSturmianBit n
      · have hheight := criticalPrefixHeight_step n
        rw [hbit] at hheight
        have hheight' :
            criticalHeight (n + 1) = criticalPrefixHeight n := by
          simpa [bitNat] using hheight
        simp only [oddInverseContributionScan, add_zero, criticalPrefixHeight_succ]
        rw [hheight']
      · have hheight := criticalPrefixHeight_step n
        rw [hbit] at hheight
        have hpos :
            n = beattyIndex (criticalPrefixHeight n) :=
          critical_true_position_eq_beattyIndex hbit
        simp only [oddInverseContributionScan]
        simp only [Nat.zero_add, add_zero]
        rw [hheight]
        simp only [bitNat]
        rw [beattyInverseContribution_succ, ← hpos]

/-- one-step precision reduction `ZMod(2^(e+1)) -> ZMod(2^e)`。 -/
def reduceOnePrecision (e : ℕ) :
    ZMod (2 ^ (e + 1)) →+* ZMod (2 ^ e) :=
  ZMod.castHom (by
    refine ⟨2, ?_⟩
    rw [pow_succ]
  ) (ZMod (2 ^ e))

@[simp] theorem reduceOnePrecision_natCast
    (e n : ℕ) :
    reduceOnePrecision e ((n : ℕ) : ZMod (2 ^ (e + 1))) =
      ((n : ℕ) : ZMod (2 ^ e)) := by
  simp [reduceOnePrecision]

/-- precision reduction は `3^{-a}` を同じ inverse へ送る。 -/
theorem reduceOnePrecision_invThreePow
    (e a : ℕ) :
    reduceOnePrecision e (invThreePow (e + 1) a) =
      invThreePow e a := by
  have hHigh :=
    threePow_mul_invThreePow (e + 1) a
  have hMapped :=
    congrArg (fun z => reduceOnePrecision e z) hHigh
  have hdiv : 2 ^ e ∣ 2 ^ (e + 1) := by
    refine ⟨2, ?_⟩
    rw [pow_succ]
  have hx :
      (3 : ZMod (2 ^ e)) ^ a *
          reduceOnePrecision e (invThreePow (e + 1) a) = 1 := by
    simpa only [
      reduceOnePrecision,
      map_mul,
      map_pow,
      map_ofNat,
      map_one
    ] using hMapped
  have hy := threePow_mul_invThreePow e a
  calc
    reduceOnePrecision e (invThreePow (e + 1) a)
        = 1 * reduceOnePrecision e (invThreePow (e + 1) a) := by simp
    _ = ((3 : ZMod (2 ^ e)) ^ a * invThreePow e a) *
          reduceOnePrecision e (invThreePow (e + 1) a) := by rw [hy]
    _ = invThreePow e a *
          ((3 : ZMod (2 ^ e)) ^ a *
            reduceOnePrecision e (invThreePow (e + 1) a)) := by ring
    _ = invThreePow e a := by rw [hx]; simp

theorem reduceOnePrecision_add
    (e : ℕ)
    (x y : ZMod (2 ^ (e + 1))) :
    reduceOnePrecision e (x + y) =
      reduceOnePrecision e x + reduceOnePrecision e y := by
  simp only [reduceOnePrecision, map_add]


theorem reduceOnePrecision_mul
    (e : ℕ)
    (x y : ZMod (2 ^ (e + 1))) :
    reduceOnePrecision e (x * y) =
      reduceOnePrecision e x * reduceOnePrecision e y := by
  simp only [reduceOnePrecision, map_mul]


theorem reduceOnePrecision_two_pow
    (e i : ℕ) :
    reduceOnePrecision e
        ((2 : ZMod (2 ^ (e + 1))) ^ i) =
      (2 : ZMod (2 ^ e)) ^ i := by
  simp only [
    reduceOnePrecision,
    map_pow,
    map_ofNat
  ]

/-- precision reduction と odd inverse scan は可換。 -/
theorem reduceOnePrecision_oddInverseContributionScan
    (e : ℕ)
    (v : ParityWord)
    (i a : ℕ) :
    reduceOnePrecision e
        (oddInverseContributionScan (e + 1) v i a) =
      oddInverseContributionScan e v i a := by
  induction v generalizing i a with
  | nil =>
      simp only [oddInverseContributionScan]
      exact map_zero _
  | cons b v ih =>
      cases b
      · change
          reduceOnePrecision e
            (oddInverseContributionScan
              (e + 1) v (i + 1) a) =
            oddInverseContributionScan e v (i + 1) a
        exact ih (i + 1) a
      · change
          reduceOnePrecision e
            (((2 : ZMod (2 ^ (e + 1))) ^ i *
                invThreePow (e + 1) (a + 1)) +
              oddInverseContributionScan
                (e + 1) v (i + 1) (a + 1)) =
            ((2 : ZMod (2 ^ e)) ^ i *
                invThreePow e (a + 1)) +
              oddInverseContributionScan
                e v (i + 1) (a + 1)
        rw [reduceOnePrecision_add]
        rw [reduceOnePrecision_mul]
        rw [reduceOnePrecision_two_pow]
        rw [reduceOnePrecision_invThreePow]
        rw [ih (i + 1) (a + 1)]

/-- word length を指定した座標へ inverse odd path sum を transport。 -/
def inverseOddPathSumAtLength
    (v : ParityWord)
    (k : ℕ)
    (h : v.length = k) :
    ZMod (2 ^ k) := by
  subst k
  exact inverseOddPathSum v

/-- critical boundary word の inverse odd path sum を
    ambient precision `k` で直接読む。 -/
def criticalBoundaryInverseOddPathSum :
    (k : ℕ) → ZMod (2 ^ k)
  | 0 => 0
  | k + 1 =>
      - oddInverseContributionScan
          (k + 1)
          (criticalSturmianPrefix k ++ [false])
          0 0

/--
full boundary inverse class を precision `e=k-1` へ落とすと、
terminal false は消えて mechanical prefix の inverse sumだけが残る。
-/
theorem reduced_inverseOddPathSum_criticalBoundaryWord
    (e : ℕ) :
    reduceOnePrecision e
        (criticalBoundaryInverseOddPathSum (e + 1)) =
      criticalXiTruncationClass e (criticalPrefixHeight e) := by
  change
    reduceOnePrecision e
      (- oddInverseContributionScan
        (e + 1)
        (criticalSturmianPrefix e ++ [false])
        0 0) =
      criticalXiTruncationClass e (criticalPrefixHeight e)
  rw [map_neg]
  rw [reduceOnePrecision_oddInverseContributionScan]
  rw [oddInverseContributionScan_append]
  simp only [
    criticalSturmianPrefix_length,
    criticalSturmianPrefix_oddCount
  ]
  change
    -(
      oddInverseContributionScan
        e
        (criticalSturmianPrefix e)
        0 0 +
      oddInverseContributionScan
        e
        [false]
        e
        (criticalPrefixHeight e)
    ) =
      criticalXiTruncationClass e (criticalPrefixHeight e)
  simp only [oddInverseContributionScan]
  rw [oddInverseContributionScan_criticalSturmianPrefix]
  rw [add_zero]
  rfl

/--
word の長さを外部 precision `k` と同定した状態で、
least representative は odd inverse contribution scan そのもの。

重要なのは `hk` を ZMod の型の中で rewrite せず、
先に `subst k` して definitional equality に落とすこと。
-/
theorem leastRepresentative_cast_eq_oddScan_atLength
    (w : ParityWord)
    (k : ℕ)
    (hk : w.length = k) :
    ((leastRepresentative w : ℕ) : ZMod (2 ^ k)) =
      - oddInverseContributionScan k w 0 0 := by
  subst k
  have h :=
    (leastRepresentative_cast w).trans
      (inverseOddPathSum_eq_parityStartClass w).symm
  change
    ((leastRepresentative w : ℕ) :
        ZMod (2 ^ w.length)) =
      - oddInverseContributionScan
          w.length w 0 0 at h
  exact h

/--
critical boundary の least representative を full precision `2^(e+1)` で読むと、
critical boundary inverse class そのもの。
-/
theorem leastRepresentative_criticalBoundary_fullPrecision
    (e : ℕ) :
    (((leastRepresentative (criticalBoundaryWord (e + 1)) : ℕ) :
        ZMod (2 ^ (e + 1)))) =
      criticalBoundaryInverseOddPathSum (e + 1) := by
  have h :=
    leastRepresentative_cast_eq_oddScan_atLength
      (criticalBoundaryWord (e + 1))
      (e + 1)
      (criticalBoundaryWord_length (e + 1))
  change
    (((leastRepresentative (criticalBoundaryWord (e + 1)) : ℕ) :
        ZMod (2 ^ (e + 1)))) =
      - oddInverseContributionScan
          (e + 1)
          (criticalSturmianPrefix e ++ [false])
          0 0
  simpa only [criticalBoundaryWord] using h


/--
最終 bridge（cast equality 版）。

任意の first-passage length k について、その canonical critical boundary の
least representative を mod `2^(k-1)` へ落とすと、endpoint count m までの
Beatty/Ξ truncation と一致する。
-/
theorem leastRepresentative_criticalBoundary_cast_eq_xiTruncation
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    let e := v.length - 1
    let m := oddCount v
    ((leastRepresentative (criticalBoundaryWord v.length) : ℕ) :
        ZMod (2 ^ e)) =
      criticalXiTruncationClass e m := by
  let e := v.length - 1
  let m := oddCount v
  have hkPos : 0 < v.length :=
    List.length_pos_of_ne_nil h.1
  have hkEq : v.length = e + 1 := by
    simp [e]
    omega
  have hmEq : criticalPrefixHeight e = m := by
    have hend :=
      endpointOddCount_eq_criticalPrefixHeight_pred h
    simpa [e, m] using hend.symm
  have hHigh :=
    leastRepresentative_criticalBoundary_fullPrecision e
  have hReduced :=
    congrArg (fun z => reduceOnePrecision e z) hHigh
  rw [reduceOnePrecision_natCast] at hReduced
  rw [reduced_inverseOddPathSum_criticalBoundaryWord] at hReduced
  calc
    ((leastRepresentative (criticalBoundaryWord v.length) : ℕ) :
        ZMod (2 ^ e))
        =
      ((leastRepresentative (criticalBoundaryWord (e + 1)) : ℕ) :
        ZMod (2 ^ e)) := by
          rw [hkEq]
    _ = criticalXiTruncationClass
          e (criticalPrefixHeight e) := hReduced
    _ = criticalXiTruncationClass e m := by
          rw [hmEq]

/-- 最終 bridge の ordinary residue (`Nat.mod`) 版。 -/
theorem leastRepresentative_criticalBoundary_mod_eq_xiTruncation_val
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    let e := v.length - 1
    let m := oddCount v
    leastRepresentative (criticalBoundaryWord v.length) % (2 ^ e) =
      (criticalXiTruncationClass e m).val := by
  let e := v.length - 1
  let m := oddCount v
  have hcast := leastRepresentative_criticalBoundary_cast_eq_xiTruncation h
  have hv := congrArg ZMod.val hcast
  simpa [e, m, ZMod.val_natCast] using hv

/-- Ferrers boundary 自身に対する Ξ truncation bridge。 -/
theorem ferrersBoundary_leastRepresentative_mod_eq_xiTruncation_val
    {v : ParityWord}
    (h : IsFerrersBoundary v) :
    let e := v.length - 1
    let m := oddCount v
    leastRepresentative v % (2 ^ e) =
      (criticalXiTruncationClass e m).val := by
  have hv := ferrersBoundary_eq_criticalBoundaryWord h
  rw [hv]
  have hfp : IsFirstPassageWord (criticalBoundaryWord v.length) := by
    rw [← hv]
    exact h.1
  have hres := leastRepresentative_criticalBoundary_mod_eq_xiTruncation_val hfp
  simpa [criticalBoundaryWord_length,
    criticalBoundaryWord_oddCount_eq h.1] using hres

end CSTMicro
end Collatz2
