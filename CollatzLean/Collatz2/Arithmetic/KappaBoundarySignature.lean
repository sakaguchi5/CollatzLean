import CollatzLean.Collatz2.Arithmetic.KappaSwapValuation
import CollatzLean.Collatz2.Native.AdjacentPrependOne
import CollatzLean.Collatz2.Core.TranslationPath
import Mathlib.Data.ZMod.Basic

/-!
# Collatz2 Arithmetic: kappa=1 の word 境界シグネチャ

primitive `kappa = 1` は単なる小さい center-separation integer ではない。
translation path の左右 divisibility と組み合わせると、actual adjacent words の
左端・右端に rigid な symbolic signature を強制する。

* 左端: 両 block は `1` で始まり、2番目 exponent で必ず分岐し、その一方は `1`
* 右端: terminal exponents の parity は反対

2-adic 側は common-prefix depth、3-adic 側は terminal/suffix depth を読んでいる。
-/

namespace Collatz2

/-! ## 小さな剰余補助定理 -/

/-- `2^(2k)=1 mod 3`. -/
private theorem two_pow_double_eq_one_mod_three
    (k : ℕ) :
    (2 : ZMod 3) ^ (k + k) = 1 := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      rw [show (k + 1) + (k + 1) = (k + k) + 2 by omega]
      rw [pow_add, ih]
      norm_num
      decide

/-- `2^(2k+1)=2 mod 3`. -/
private theorem two_pow_double_add_one_eq_two_mod_three
    (k : ℕ) :
    (2 : ZMod 3) ^ (k + k + 1) = 2 := by
  rw [pow_succ, two_pow_double_eq_one_mod_three]
  norm_num

/-- 2 の冪の mod 3 での値は exponent の parity だけで決まる。 -/
private theorem two_pow_mod_three_eq_of_mod_two_eq
    (a b : ℕ)
    (hmod : a % 2 = b % 2) :
    (2 : ZMod 3) ^ a = (2 : ZMod 3) ^ b := by
  obtain ⟨ka, haEven | haOdd⟩ := a.even_or_odd'
  · obtain ⟨kb, hbEven | hbOdd⟩ := b.even_or_odd'
    · rw [haEven, hbEven]
      calc
        (2 : ZMod 3) ^ (2 * ka) = 1 := by
          simpa [two_mul] using
            two_pow_double_eq_one_mod_three ka
        _ = (2 : ZMod 3) ^ (2 * kb) := by
          symm
          simpa [two_mul] using
            two_pow_double_eq_one_mod_three kb
    · exfalso
      rw [haEven, hbOdd] at hmod
      omega
  · obtain ⟨kb, hbEven | hbOdd⟩ := b.even_or_odd'
    · exfalso
      rw [haOdd, hbEven] at hmod
      omega
    · rw [haOdd, hbOdd]
      calc
        (2 : ZMod 3) ^ (2 * ka + 1) = 2 := by
          simpa [two_mul] using
            two_pow_double_add_one_eq_two_mod_three ka
        _ = (2 : ZMod 3) ^ (2 * kb + 1) := by
          symm
          simpa [two_mul] using
            two_pow_double_add_one_eq_two_mod_three kb

/-- 自然数が 3 で割り切れなければ、その Nat cast は `ZMod 3` で非零。 -/
private theorem natCast_mod_three_ne_zero_of_not_dvd
    {a : ℕ}
    (hnot : ¬ 3 ∣ a) :
    (a : ZMod 3) ≠ 0 := by
  intro hz
  have hval := congrArg ZMod.val hz
  have hmod : a % 3 = 0 := by
    simpa [ZMod.val_natCast] using hval
  apply hnot
  have hdecomp := Nat.mod_add_div a 3
  rw [hmod] at hdecomp
  refine ⟨a / 3, ?_⟩
  omega

namespace Word

/--
terminal exponent の parity が等しければ、word-swap separation は mod 3 で 0 になる。
-/
theorem wordSwap_separation_mod_three_eq_zero_of_terminal_same_parity
    {u v : Word}
    (huNe : u ≠ [])
    (hvNe : v ≠ [])
    (hparity :
      u.getLast huNe % 2 = v.getLast hvNe % 2) :
    (((AffineTransfer.ofWord u).separation
        (AffineTransfer.ofWord v) : ℤ) : ZMod 3) = 0 := by
  let eu := u.getLast huNe
  let ev := v.getLast hvNe
  let u0 := u.dropLast
  let v0 := v.dropLast
  have huDecomp : u0 ++ [eu] = u := by
    simpa [u0, eu] using List.dropLast_append_getLast huNe
  have hvDecomp : v0 ++ [ev] = v := by
    simpa [v0, ev] using List.dropLast_append_getLast hvNe
  have hparity' : eu % 2 = ev % 2 := by
    simpa [eu, ev] using hparity
  have huTwo : twoSteps u = twoSteps u0 + eu := by
    rw [← huDecomp, twoSteps_append]
    simp [twoSteps]
  have hvTwo : twoSteps v = twoSteps v0 + ev := by
    rw [← hvDecomp, twoSteps_append]
    simp [twoSteps]
  have hExpParity :
      twoSteps (u ++ v0) % 2 = twoSteps (v ++ u0) % 2 := by
    rw [twoSteps_append, twoSteps_append, huTwo, hvTwo]
    omega
  have hPow :
      (2 : ZMod 3) ^ twoSteps (u ++ v0) =
        (2 : ZMod 3) ^ twoSteps (v ++ u0) :=
    two_pow_mod_three_eq_of_mod_two_eq _ _ hExpParity
  have hBuv :
      ((affineConst (u ++ v) : ℕ) : ZMod 3) =
        (2 : ZMod 3) ^ twoSteps (u ++ v0) := by
    rw [← hvDecomp]
    simpa [List.append_assoc] using
      affineConst_append_singleton_mod_three (u ++ v0) ev
  have hBvu :
      ((affineConst (v ++ u) : ℕ) : ZMod 3) =
        (2 : ZMod 3) ^ twoSteps (v ++ u0) := by
    rw [← huDecomp]
    simpa [List.append_assoc] using
      affineConst_append_singleton_mod_three (v ++ u0) eu
  have hswap := wordSwap_translate_sub u v
  have hswapMod := congrArg (fun z : ℤ => (z : ZMod 3)) hswap
  have hswapMod' :
      (((affineConst (u ++ v) : ℕ) : ZMod 3) -
          ((affineConst (v ++ u) : ℕ) : ZMod 3)) =
        (((AffineTransfer.ofWord u).separation
          (AffineTransfer.ofWord v) : ℤ) : ZMod 3) := by
    simpa using hswapMod
  calc
    (((AffineTransfer.ofWord u).separation
        (AffineTransfer.ofWord v) : ℤ) : ZMod 3)
        =
        (((affineConst (u ++ v) : ℕ) : ZMod 3) -
          ((affineConst (v ++ u) : ℕ) : ZMod 3)) := hswapMod'.symm
    _ = 0 := by
      rw [hBuv, hBvu, hPow]
      ring

end Word

namespace AdjacentTransferChain

/-! ## 2-adic 左境界シグネチャ -/

/-- `kappa=1` なら adjacent separation は mod 8 で非零。 -/
theorem not_eight_dvd_separationAdjacent_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    ¬ (8 : ℤ) ∣ C.separationAdjacent n := by
  intro h8
  rcases h8 with ⟨q, hq⟩
  have hEightZero :
      (((8 : ℤ) : ZMod 8)) = 0 := by
    decide
  have hzero :
      ((C.separationAdjacent n : ℤ) : ZMod 8) = 0 := by
    rw [hq]
    rw [Int.cast_mul, hEightZero]
    simp
  have hmod :=
    C.neg_separationAdjacent_mod_eight_eq_four_of_primitiveKappa_eq_one
      hN hNs hstart hk
  rw [hzero] at hmod
  have hne : (0 : ZMod 8) ≠ 4 := by
    decide
  exact hne hmod

/-- `1` で始まる contracting block は必ず2番目の exponent を持つ。 -/
private theorem tail_nonempty_of_negative_word_eq_one_cons
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    {t : Word}
    (hword : C.word n = 1 :: t) :
    t ≠ [] := by
  intro ht
  subst t
  have hC : Word.Contracting (C.word n) :=
    (C.negativeAt_iff_contracting n).1 hN
  rw [hword] at hC
  have hnot : ¬ Word.Contracting ([1] : Word) := by
    rw [Word.contracting_iff_threePow_lt_twoPow]
    norm_num [Word.oddSteps, Word.twoSteps]
  exact hnot hC

/--
primitive `kappa=1` は、二つの adjacent word が2番目の exponent ですでに分岐することを強制する。
さらに、その二つの second exponent の一方は exact に `1` である。
-/
theorem exists_secondExponent_signature_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    ∃ a ua b vb,
      C.word n = 1 :: a :: ua ∧
      C.word (n + 1) = 1 :: b :: vb ∧
      a ≠ b ∧
      (a = 1 ∨ b = 1) := by
  have hstartNext : 1 < C.startValue (n + 1) := by
    rw [← C.endValue_eq_next_startValue n]
    exact lt_trans hstart (C.startValue_lt_endValue n)
  obtain ⟨ta, hta⟩ := C.exists_word_eq_one_cons_of_one_lt_startValue hstart
  obtain ⟨tb, htb⟩ := C.exists_word_eq_one_cons_of_one_lt_startValue hstartNext
  have htaNe : ta ≠ [] := C.tail_nonempty_of_negative_word_eq_one_cons hN hta
  have htbNe : tb ≠ [] := C.tail_nonempty_of_negative_word_eq_one_cons hNs htb
  cases ta with
  | nil => contradiction
  | cons a ua =>
      cases tb with
      | nil => contradiction
      | cons b vb =>
          have haPos : 0 < a := C.word_valid n a (by rw [hta]; simp)
          have hbPos : 0 < b := C.word_valid (n + 1) b (by rw [htb]; simp)
          have huaValid : Word.Valid ua := by
            intro e he
            exact C.word_valid n e (by rw [hta]; simp [he])
          have hvbValid : Word.Valid vb := by
            intro e he
            exact C.word_valid (n + 1) e (by rw [htb]; simp [he])
          have hNot8 : ¬ (8 : ℤ) ∣ C.separationAdjacent n :=
            C.not_eight_dvd_separationAdjacent_of_primitiveKappa_eq_one
              hN hNs hstart hk
          have hswap :
              (Word.affineConst (C.word n ++ C.word (n + 1)) : ℤ) -
                  (Word.affineConst (C.word (n + 1) ++ C.word n) : ℤ) =
                C.separationAdjacent n := by
            simpa [AdjacentTransferChain.transfer,
              AdjacentTransferChain.separationAdjacent] using
              Word.wordSwap_translate_sub (C.word n) (C.word (n + 1))
          have hab : a ≠ b := by
            intro habEq
            subst b
            let ru : Word := ua ++ C.word (n + 1)
            let rv : Word := vb ++ C.word n
            have hruValid : Word.Valid ru := by
              dsimp [ru]
              exact huaValid.append (C.word_valid (n + 1))
            have hrvValid : Word.Valid rv := by
              dsimp [rv]
              exact hvbValid.append (C.word_valid n)
            have hruNe : ru ≠ [] := by
              dsimp [ru]
              simp [C.word_nonempty (n + 1)]
            have hrvNe : rv ≠ [] := by
              dsimp [rv]
              simp [C.word_nonempty n]
            have hoddRem : Word.oddSteps ru = Word.oddSteps rv := by
              dsimp [ru, rv]
              rw [Word.oddSteps_append, Word.oddSteps_append]
              have hLenN : Word.oddSteps (C.word n) = Word.oddSteps ua + 2 := by
                rw [hta]
                simp [Word.oddSteps]
              have hLenNs : Word.oddSteps (C.word (n + 1)) = Word.oddSteps vb + 2 := by
                rw [htb]
                simp [Word.oddSteps]
              omega
            have hdepth : 2 ≤ Word.twoSteps ([1, a] : Word) := by
              simp [Word.twoSteps]
              omega
            have h8diff :
                (8 : ℤ) ∣
                  (Word.affineConst (C.word n ++ C.word (n + 1)) : ℤ) -
                    (Word.affineConst (C.word (n + 1) ++ C.word n) : ℤ) := by
              have h :=
                Word.eight_dvd_affineConst_sub_of_commonPrefix_twoSteps_ge_two
                  ([1, a] : Word) ru rv
                  hruValid hrvValid hruNe hrvNe hoddRem hdepth
              simpa [ru, rv, hta, htb, List.append_assoc] using h
            apply hNot8
            rw [← hswap]
            exact h8diff
          have hOne : a = 1 ∨ b = 1 := by
            by_contra hnone
            have haTwo : 2 ≤ a := by omega
            have hbTwo : 2 ≤ b := by omega
            let ru : Word := ua ++ C.word (n + 1)
            let rv : Word := vb ++ C.word n
            have hoddTail : Word.oddSteps ru = Word.oddSteps rv := by
              dsimp [ru, rv]
              rw [Word.oddSteps_append, Word.oddSteps_append]
              have hLenN : Word.oddSteps (C.word n) = Word.oddSteps ua + 2 := by
                rw [hta]
                simp [Word.oddSteps]
              have hLenNs : Word.oddSteps (C.word (n + 1)) = Word.oddSteps vb + 2 := by
                rw [htb]
                simp [Word.oddSteps]
              omega
            have hinner4 :
                (4 : ℤ) ∣
                  (Word.affineConst (a :: ru) : ℤ) -
                    (Word.affineConst (b :: rv) : ℤ) := by
              simpa using
                Word.twoPow_head_dvd_affineConst_sub
                  (m := 2) ru rv hoddTail haTwo hbTwo
            have hoddHead :
                Word.oddSteps (a :: ru) = Word.oddSteps (b :: rv) := by
              simp only [Word.oddSteps_cons]
              omega
            have hprefix :=
              Word.affineConst_sub_commonPrefix_eq
                ([1] : Word) (a :: ru) (b :: rv) hoddHead
            have hprefix' :
                (Word.affineConst (C.word n ++ C.word (n + 1)) : ℤ) -
                    (Word.affineConst (C.word (n + 1) ++ C.word n) : ℤ) =
                  2 *
                    ((Word.affineConst (a :: ru) : ℤ) -
                      (Word.affineConst (b :: rv) : ℤ)) := by
              simpa [ru, rv, hta, htb, Word.twoSteps,
                List.append_assoc] using hprefix
            rcases hinner4 with ⟨q, hq⟩
            have h8diff :
                (8 : ℤ) ∣
                  (Word.affineConst (C.word n ++ C.word (n + 1)) : ℤ) -
                    (Word.affineConst (C.word (n + 1) ++ C.word n) : ℤ) := by
              refine ⟨q, ?_⟩
              rw [hprefix', hq]
              ring
            apply hNot8
            rw [← hswap]
            exact h8diff
          exact ⟨a, ua, b, vb, hta, htb, hab, hOne⟩

/-! ## 3-adic 右境界シグネチャ -/

/-- negative word block の center gap は 3 で割り切れない。 -/
theorem three_not_dvd_centerGap_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    ¬ 3 ∣ (C.transfer n).centerGap := by
  have hneg : (C.transfer n).determinant < 0 := by
    simpa [
      AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant
    ] using hN
  have hCA :
      (C.transfer n).oddCoeff ≤
        (C.transfer n).twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hsum :
      (C.transfer n).centerGap +
          (C.transfer n).oddCoeff =
        (C.transfer n).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCA
  have hp : 0 < Word.oddSteps (C.word n) := by
    simpa [Word.oddSteps] using
      List.length_pos_iff.mpr (C.word_nonempty n)
  obtain ⟨k, hk⟩ :
      ∃ k : ℕ,
        Word.oddSteps (C.word n) = k + 1 :=
    ⟨Word.oddSteps (C.word n) - 1, by omega⟩
  have h3C :
      3 ∣ (C.transfer n).oddCoeff := by
    change 3 ∣ 3 ^ Word.oddSteps (C.word n)
    refine ⟨3 ^ k, ?_⟩
    rw [hk, pow_succ]
    ring
  have hcopA :
      Nat.Coprime 3 (C.transfer n).twoCoeff := by
    change
      Nat.Coprime
        3
        (2 ^ Word.twoSteps (C.word n))
    exact
      (by decide : Nat.Coprime 3 2).pow_right
        (Word.twoSteps (C.word n))
  intro h3G
  have h3A :
      3 ∣ (C.transfer n).twoCoeff := by
    rw [← hsum]
    exact dvd_add h3G h3C
  have h31 : 3 = 1 :=
    Nat.eq_one_of_dvd_coprimes
      hcopA
      (dvd_refl 3)
      h3A
  omega

/-- negative word block の center content も 3 で割り切れない。 -/
theorem three_not_dvd_centerContent_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    ¬ 3 ∣ C.centerContent n := by
  intro h3h
  have h3G : 3 ∣ (C.transfer n).centerGap :=
    dvd_trans h3h (C.centerContent_dvd_centerGap n)
  exact (C.three_not_dvd_centerGap_of_negativeAt hN) h3G

/-- `kappa=1` の adjacent separation は mod 3 で非零。 -/
theorem separationAdjacent_mod_three_ne_zero_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    ((C.separationAdjacent n : ℤ) : ZMod 3) ≠ 0 := by
  have hsep :=
    C.separationAdjacent_eq_four_mul_contents_of_primitiveKappa_eq_one
      hN hNs hstart hk
  have hnDvd :
      ¬ 3 ∣ C.centerContent n :=
    C.three_not_dvd_centerContent_of_negativeAt hN
  have hnsDvd :
      ¬ 3 ∣ C.centerContent (n + 1) :=
    C.three_not_dvd_centerContent_of_negativeAt hNs
  have hcopn :
      Nat.Coprime (C.centerContent n) 3 := by
    rw [Nat.coprime_comm]
    exact
      (Nat.prime_three.coprime_iff_not_dvd).2 hnDvd
  have hcopns :
      Nat.Coprime (C.centerContent (n + 1)) 3 := by
    rw [Nat.coprime_comm]
    exact
      (Nat.prime_three.coprime_iff_not_dvd).2 hnsDvd
  have hun :
      IsUnit (C.centerContent n : ZMod 3) :=
    (ZMod.isUnit_iff_coprime
      (C.centerContent n) 3).2 hcopn
  have huns :
      IsUnit (C.centerContent (n + 1) : ZMod 3) :=
    (ZMod.isUnit_iff_coprime
      (C.centerContent (n + 1)) 3).2 hcopns
  have hfour :
      IsUnit (4 : ZMod 3) := by
    have h41 : (4 : ZMod 3) = 1 := by
      decide
    rw [h41]
    exact isUnit_one
  have hprod :
      IsUnit
        ((4 : ZMod 3) *
          (C.centerContent n : ZMod 3) *
          (C.centerContent (n + 1) : ZMod 3)) :=
    (hfour.mul hun).mul huns
  rw [hsep]
  simpa only [
    Int.cast_mul,
    Int.cast_ofNat,
    Int.cast_natCast
  ] using hprod.ne_zero

/--
primitive `kappa=1` は、二つの adjacent terminal exponent の parity が反対であることを強制する。
-/
theorem terminalExponent_parity_ne_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    (C.word n).getLast (C.word_nonempty n) % 2 ≠
      (C.word (n + 1)).getLast (C.word_nonempty (n + 1)) % 2 := by
  intro hparity
  have hzero :=
    Word.wordSwap_separation_mod_three_eq_zero_of_terminal_same_parity
      (C.word_nonempty n) (C.word_nonempty (n + 1)) hparity
  have hnz :=
    C.separationAdjacent_mod_three_ne_zero_of_primitiveKappa_eq_one
      hN hNs hstart hk
  apply hnz
  simpa [AdjacentTransferChain.separationAdjacent,
    AdjacentTransferChain.transfer] using hzero

/-- primitive `kappa=1` event に対する左右を合わせた symbolic boundary signature。 -/
theorem primitiveKappa_eq_one_boundarySignature
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    (∃ a ua b vb,
      C.word n = 1 :: a :: ua ∧
      C.word (n + 1) = 1 :: b :: vb ∧
      a ≠ b ∧
      (a = 1 ∨ b = 1)) ∧
    ((C.word n).getLast (C.word_nonempty n) % 2 ≠
      (C.word (n + 1)).getLast (C.word_nonempty (n + 1)) % 2) := by
  exact ⟨
    C.exists_secondExponent_signature_of_primitiveKappa_eq_one
      hN hNs hstart hk,
    C.terminalExponent_parity_ne_of_primitiveKappa_eq_one
      hN hNs hstart hk⟩

end AdjacentTransferChain
end Collatz2
