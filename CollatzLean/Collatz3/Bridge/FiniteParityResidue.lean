import CollatzLean.Collatz3.Bridge.CriticalParityCode
import CollatzLean.Collatz3.Bridge.ValidEndpointRuns
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: finite parity prefix と `2^n` 剰余

positive physical depth `n` の `ParityComposition n` は、始点から見た最初の `n` 個の
parity bits を run-length で圧縮したものとして読む。

既存の odd-only `Runs` は各 block の終点まで奇数であることを要求するため、有限 prefix の
最後だけは endpoint の奇偶を要求しない薄い relation `ParityPrefixRuns` を導入する。
proper block endpoint は従来どおり奇数であり、最後の endpoint だけは次の parity bit を
まだ読んでいないので任意でよい。

この prefix semantics により、同じ始点・同じ physical depth を持つ二つの positive
composition は一致する。そこで `Composition n` の canonical odd-endpoint start を
`mod 2^n` へ落とすと、これは finite parity prefix が決める実際の剰余 class になり、
positive depth では

`ParityComposition n ≃ {x < 2^n | Odd x}`

という exact equivalence を得る。
-/

namespace Collatz3
namespace Bridge

/--
positive exponent word の finite parity-prefix semantics。

最後の block だけは endpoint の奇偶を要求しない。それ以前の block は exact `OddStep`。
-/
inductive ParityPrefixRuns : Word → ℕ → ℕ → Prop where
  | single {e x y : ℕ}
      (exponent_pos : 0 < e)
      (equation : 2 ^ e * y = 3 * x + 1) :
      ParityPrefixRuns [e] x y
  | cons {e f x y z : ℕ} {w : Word}
      (head : OddStep e x y)
      (tail : ParityPrefixRuns (f :: w) y z) :
      ParityPrefixRuns (e :: f :: w) x z

namespace ParityPrefixRuns

/-- prefix run の word は valid。 -/
theorem valid
    {w : Word} {x y : ℕ}
    (h : ParityPrefixRuns w x y) :
    Word.Valid w := by
  induction h with
  | @single e x y he hEq =>
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      exact he
  | @cons e f x y z w hHead hTail ih =>
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hHead.exponent_pos
      · apply ih
        simpa only [List.mem_cons] using ha

/-- prefix run の word は非空。 -/
theorem nonempty
    {w : Word} {x y : ℕ}
    (h : ParityPrefixRuns w x y) :
    w ≠ [] := by
  cases h <;> simp

/-- positive exponent equation だけで始点は奇数になる。 -/
theorem start_odd_of_single_equation
    {e x y : ℕ}
    (he : 0 < e)
    (hEq : 2 ^ e * y = 3 * x + 1) :
    Odd x := by
  obtain ⟨k, hEven | hOdd⟩ := x.even_or_odd'
  · obtain ⟨d, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
    have hEq' : 2 * (2 ^ d * y) = 6 * k + 1 := by
      calc
        2 * (2 ^ d * y) = 2 ^ (d + 1) * y := by
          rw [pow_succ]
          ring
        _ = 3 * x + 1 := hEq
        _ = 6 * k + 1 := by
          rw [hEven]
          ring
    omega
  · exact ⟨k, hOdd⟩

/-- finite parity prefix の始点は奇数。 -/
theorem start_odd
    {w : Word} {x y : ℕ}
    (h : ParityPrefixRuns w x y) :
    Odd x := by
  cases h with
  | single he hEq =>
      exact start_odd_of_single_equation he hEq
  | cons hHead hTail =>
      exact hHead.start_odd

/-- single block の endpoint equation。 -/
theorem single_endpointEquation
    {e x y : ℕ}
    (hEq : 2 ^ e * y = 3 * x + 1) :
    Word.EndpointEquation [e] x y := by
  apply (Word.endpointEquation_iff [e] x y).2
  simpa [Word.twoSteps, Word.oddSteps] using hEq

/-- finite parity prefix は word 全体の affine endpoint equation を満たす。 -/
theorem endpointEquation
    {w : Word} {x y : ℕ}
    (h : ParityPrefixRuns w x y) :
    w.EndpointEquation x y := by
  induction h with
  | @single e x y he hEq =>
      exact single_endpointEquation hEq
  | @cons e f x y z w hHead hTail ih =>
      have hHeadEq : Word.EndpointEquation [e] x y :=
        single_endpointEquation hHead.equation
      have hApp := hHeadEq.append ih
      simpa using hApp

/-- prefix run の total physical depth は正。 -/
theorem twoSteps_pos
    {w : Word} {x y : ℕ}
    (h : ParityPrefixRuns w x y) :
    0 < Word.twoSteps w := by
  have hValid := h.valid
  cases w with
  | nil => exact False.elim (h.nonempty rfl)
  | cons e w =>
      have he : 0 < e := hValid e (by simp)
      simp [Word.twoSteps, he]

end ParityPrefixRuns

/--
endpoint equation の start を `2^H` だけずらすと、endpoint は `3^p` だけずれる。
finite parity-prefix residue の周期性に使う。
-/
theorem endpointEquation_prefixLift
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (k : ℕ) :
    w.EndpointEquation
      (x + 2 ^ Word.twoSteps w * k)
      (y + 3 ^ Word.oddSteps w * k) := by
  apply (Word.endpointEquation_iff w _ _).2
  have hMain := (Word.endpointEquation_iff w x y).1 h
  calc
    2 ^ Word.twoSteps w *
        (y + 3 ^ Word.oddSteps w * k)
        =
        2 ^ Word.twoSteps w * y +
          2 ^ Word.twoSteps w * 3 ^ Word.oddSteps w * k := by ring
    _ =
        3 ^ Word.oddSteps w * x + Word.affineConst w +
          2 ^ Word.twoSteps w * 3 ^ Word.oddSteps w * k := by
          rw [hMain]
    _ =
        3 ^ Word.oddSteps w *
            (x + 2 ^ Word.twoSteps w * k) +
          Word.affineConst w := by ring

/--
valid nonempty word の endpoint equation は、最後の endpoint の奇偶を仮定しなくても
finite parity prefix を実現する。
-/
theorem parityPrefixRuns_of_valid_endpointEquation
    {w : Word} {x y : ℕ}
    (hValid : Word.Valid w)
    (hne : w ≠ [])
    (hEq : w.EndpointEquation x y) :
    ParityPrefixRuns w x y := by
  induction w generalizing x y with
  | nil => contradiction
  | cons e w ih =>
      have he : 0 < e := hValid e (by simp)
      by_cases hw : w = []
      · subst w
        apply ParityPrefixRuns.single he
        have hMain := (Word.endpointEquation_iff [e] x y).1 hEq
        simpa [Word.twoSteps, Word.oddSteps] using hMain
      · have hTailValid : Word.Valid w := by
          intro a ha
          exact hValid a (by simp [ha])
        have hMain := (Word.endpointEquation_iff (e :: w) x y).1 hEq
        have hFactor :
            2 ^ e * (2 ^ Word.twoSteps w * y) =
              3 ^ Word.oddSteps w * (3 * x + 1) +
                2 ^ e * Word.affineConst w := by
          calc
            2 ^ e * (2 ^ Word.twoSteps w * y)
                = 2 ^ (e + Word.twoSteps w) * y := by
                    rw [pow_add]
                    ring
            _ = 2 ^ Word.twoSteps (e :: w) * y := by
                    rw [Word.twoSteps_cons]
            _ =
                3 ^ Word.oddSteps (e :: w) * x +
                  Word.affineConst (e :: w) := hMain
            _ =
                3 ^ Word.oddSteps w * (3 * x + 1) +
                  2 ^ e * Word.affineConst w := by
                    rw [Word.oddSteps_cons, Word.affineConst_cons, pow_succ]
                    ring
        have hDvdSum :
            2 ^ e ∣
              3 ^ Word.oddSteps w * (3 * x + 1) +
                2 ^ e * Word.affineConst w := by
          rw [← hFactor]
          exact Nat.dvd_mul_right _ _
        have hDvdTranslate :
            2 ^ e ∣ 2 ^ e * Word.affineConst w :=
          Nat.dvd_mul_right _ _
        have hDvdProduct :
            2 ^ e ∣ 3 ^ Word.oddSteps w * (3 * x + 1) :=
          (Nat.dvd_add_iff_left hDvdTranslate).mpr hDvdSum
        have hCoprime :
            Nat.Coprime (2 ^ e) (3 ^ Word.oddSteps w) :=
          (Arithmetic.coprime_threePow_twoPow
            (Word.oddSteps w) e).symm
        have hDvdHead : 2 ^ e ∣ 3 * x + 1 :=
          hCoprime.dvd_of_dvd_mul_left hDvdProduct
        rcases hDvdHead with ⟨z, hz⟩
        have hCancel :
            2 ^ e * (2 ^ Word.twoSteps w * y) =
              2 ^ e *
                (3 ^ Word.oddSteps w * z + Word.affineConst w) := by
          calc
            2 ^ e * (2 ^ Word.twoSteps w * y)
                =
                3 ^ Word.oddSteps w * (3 * x + 1) +
                  2 ^ e * Word.affineConst w := hFactor
            _ =
                3 ^ Word.oddSteps w * (2 ^ e * z) +
                  2 ^ e * Word.affineConst w := by rw [hz]
            _ =
                2 ^ e *
                  (3 ^ Word.oddSteps w * z + Word.affineConst w) := by ring
        have hTailMain :
            2 ^ Word.twoSteps w * y =
              3 ^ Word.oddSteps w * z + Word.affineConst w :=
          Nat.mul_left_cancel (Arithmetic.twoPow_pos e) hCancel
        have hTailEq : Word.EndpointEquation w z y :=
          (Word.endpointEquation_iff w z y).2 hTailMain
        have hTailRun : ParityPrefixRuns w z y :=
          ih hTailValid hw hTailEq
        have hzOdd : Odd z := hTailRun.start_odd
        cases w with
        | nil => contradiction
        | cons f ws =>
            exact
              ParityPrefixRuns.cons
                ⟨he, hz.symm, hzOdd⟩
                hTailRun

/--
exact OddStep の exponent よりさらに長く同じ `3x+1` を 2 で割れることはない。
-/
theorem no_longer_division_after_oddStep
    {e f x y z : ℕ}
    (hef : e < f)
    (hStep : OddStep e x y)
    (hLong : 2 ^ f * z = 3 * x + 1) :
    False := by
  have hEq : 2 ^ e * y = 2 ^ f * z := by
    calc
      2 ^ e * y = 3 * x + 1 := hStep.equation
      _ = 2 ^ f * z := hLong.symm
  have hle : e ≤ f := Nat.le_of_lt hef
  have hPow : 2 ^ f = 2 ^ e * 2 ^ (f - e) := by
    calc
      2 ^ f = 2 ^ (e + (f - e)) := by
        rw [Nat.add_sub_of_le hle]
      _ = 2 ^ e * 2 ^ (f - e) := by rw [pow_add]
  have hEq' : 2 ^ e * y = 2 ^ e * (2 ^ (f - e) * z) := by
    calc
      2 ^ e * y = 2 ^ f * z := hEq
      _ = (2 ^ e * 2 ^ (f - e)) * z := by rw [hPow]
      _ = 2 ^ e * (2 ^ (f - e) * z) := by ring
  have hyFactor : y = 2 ^ (f - e) * z :=
    Nat.mul_left_cancel (Arithmetic.twoPow_pos e) hEq'
  have hdPos : 0 < f - e := Nat.sub_pos_of_lt hef
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdPos)
  have hyEven : ∃ q : ℕ, y = 2 * q := by
    refine ⟨2 ^ d * z, ?_⟩
    rw [hyFactor, hd, pow_succ]
    ring
  rcases hStep.end_odd with ⟨k, hk⟩
  rcases hyEven with ⟨q, hq⟩
  omega

/--
同じ始点から同じ physical depth だけ読んだ finite parity prefix は一意。
-/
theorem parityPrefixRuns_word_eq_of_common_start_same_twoSteps
    {u v : Word} {x y z : ℕ}
    (hu : ParityPrefixRuns u x y)
    (hv : ParityPrefixRuns v x z)
    (hDepth : Word.twoSteps u = Word.twoSteps v) :
    u = v := by
  induction hu generalizing v z with
  | @single e x y he hEq =>
      cases hv with
      | @single f x z hf hEqF =>
          have hef : e = f := by
            simpa [Word.twoSteps] using hDepth
          subst f
          rfl
      | @cons f g x m z w hHead hTail =>
          have hg : 0 < g := hTail.valid g (by simp)
          have hTailPos : 0 < Word.twoSteps (g :: w) := by
            simp [Word.twoSteps, hg]
          have hDepth' : e = f + Word.twoSteps (g :: w) := by
            simpa [Word.twoSteps] using hDepth
          have hfe : f < e := by omega
          exact False.elim
            (no_longer_division_after_oddStep hfe hHead hEq)
  | @cons e f x m y w hHead hTail ih =>
      cases hv with
      | @single g x z hg hEqG =>
          have hf : 0 < f := hTail.valid f (by simp)
          have hTailPos : 0 < Word.twoSteps (f :: w) := by
            simp [Word.twoSteps, hf]
          have hDepth' : e + Word.twoSteps (f :: w) = g := by
            simpa [Word.twoSteps] using hDepth
          have heg : e < g := by omega
          exact False.elim
            (no_longer_division_after_oddStep heg hHead hEqG)
      | @cons g h x n z v hHead' hTail' =>
          have hDet := OddStep.deterministic hHead hHead'
          rcases hDet with ⟨heg, hmn⟩
          subst g
          subst n
          have hTailDepth :
              Word.twoSteps (f :: w) = Word.twoSteps (h :: v) := by
            have hDepth' :
                e + Word.twoSteps (f :: w) =
                  e + Word.twoSteps (h :: v) := by
              simpa [Word.twoSteps] using hDepth
            omega
          have hTailEq := ih hTail' hTailDepth
          exact congrArg (fun t : Word => e :: t) hTailEq

/-- depth `n` で使う odd residue type。 -/
abbrev OddParityResidue (n : ℕ) :=
  {x : ℕ // x < 2 ^ n ∧ Odd x}

/-- `2^n` 未満の odd residue type は有限。 -/
instance oddParityResidueFinite (n : ℕ) : Finite (OddParityResidue n) :=
  Finite.of_injective
    (fun x : OddParityResidue n => (⟨x.1, x.2.1⟩ : Fin (2 ^ n)))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg Fin.val h)

/-- `n>0` なら `2^n = 2 * 2^(n-1)`。 -/
theorem twoPow_eq_two_mul_pred
    {n : ℕ}
    (hn : 0 < n) :
    2 ^ n = 2 * 2 ^ (n - 1) := by
  have hpred : n - 1 + 1 = n := by omega
  rw [← hpred, pow_succ]
  ring_nf
  simp

/-- `2^n` 未満の odd residue はちょうど `2^(n-1)` 個。 -/
noncomputable def finEquivOddParityResidue
    (n : ℕ)
    (hn : 0 < n) :
    Fin (2 ^ (n - 1)) ≃ OddParityResidue n where
  toFun k := by
    refine ⟨2 * k.1 + 1, ?_, ?_⟩
    · rw [twoPow_eq_two_mul_pred hn]
      omega
    · exact ⟨k.1, rfl⟩
  invFun x := by
    let k := Classical.choose x.2.2
    have hkEq : x.1 = 2 * k + 1 :=
      Classical.choose_spec x.2.2
    refine ⟨k, ?_⟩
    have hx : x.1 < 2 * 2 ^ (n - 1) := by
      rw [← twoPow_eq_two_mul_pred hn]
      exact x.2.1
    omega
  left_inv k := by
    apply Fin.ext
    let x : OddParityResidue n :=
      ⟨2 * k.1 + 1,
        by
          rw [twoPow_eq_two_mul_pred hn]
          omega,
        ⟨k.1, rfl⟩⟩
    let j := Classical.choose x.2.2
    have hj : x.1 = 2 * j + 1 := Classical.choose_spec x.2.2
    change j = k.1
    dsimp [x] at hj
    omega
  right_inv x := by
    apply Subtype.ext
    let k := Classical.choose x.2.2
    have hk : x.1 = 2 * k + 1 := Classical.choose_spec x.2.2
    exact hk.symm

/-- odd residue type の cardinal。 -/
theorem natCard_oddParityResidue
    {n : ℕ}
    (hn : 0 < n) :
    Nat.card (OddParityResidue n) = 2 ^ (n - 1) := by
  calc
    Nat.card (OddParityResidue n)
        = Nat.card (Fin (2 ^ (n - 1))) :=
      (Nat.card_congr (finEquivOddParityResidue n hn)).symm
    _ = 2 ^ (n - 1) := Nat.card_fin _

/--
composition の finite parity prefix が決める actual start residue。
canonical odd-endpoint start を `mod 2^n` へ落とす。
-/
noncomputable def parityCompositionResidue
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    OddParityResidue n := by
  let R := Word.canonicalStart c.blocks
  have hModPos : 0 < 2 ^ n :=
    Arithmetic.twoPow_pos n
  have hValid : Word.Valid c.blocks := by
    intro e he
    exact c.blocks_pos he
  have hNe :
      c.blocks ≠ [] :=
    parityComposition_blocks_ne_nil hn c
  have hRun :
      Runs c.blocks
        (Word.canonicalStart c.blocks)
        (Word.canonicalEnd c.blocks) :=
    Runs.canonical hValid hNe
  have hOddR : Odd R := by
    dsimp [R]
    exact hRun.start_odd_of_nonempty (parityComposition_blocks_ne_nil hn c)
  have hEvenMod : Even (2 ^ n) := by
    rw [twoPow_eq_two_mul_pred hn]
    exact ⟨2 ^ (n - 1), by ring⟩
  refine ⟨R % 2 ^ n, Nat.mod_lt _ hModPos, ?_⟩
  exact (Odd.mod_even_iff hEvenMod).2 hOddR

/-- residue map の underlying value。 -/
@[simp] theorem parityCompositionResidue_val
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    (parityCompositionResidue hn c).1 =
      Word.canonicalStart c.blocks % 2 ^ n := by
  rfl

/--
同じ finite parity residue を持つ二つの composition は同一。
証明では両 canonical start を `2^n` 周期で共通 start へ持ち上げ、prefix determinism を使う。
-/
theorem parityCompositionResidue_injective
    {n : ℕ}
    (hn : 0 < n) :
    Function.Injective (parityCompositionResidue hn) := by
  intro c d hcd
  have hMod :
      Word.canonicalStart c.blocks % 2 ^ n =
        Word.canonicalStart d.blocks % 2 ^ n := by
    exact congrArg Subtype.val hcd
  let Rc := Word.canonicalStart c.blocks
  let Rd := Word.canonicalStart d.blocks
  let qc := Rc / 2 ^ n
  let qd := Rd / 2 ^ n
  have hRc : Rc % 2 ^ n + 2 ^ n * qc = Rc := by
    simpa [qc] using Nat.mod_add_div Rc (2 ^ n)
  have hRd : Rd % 2 ^ n + 2 ^ n * qd = Rd := by
    simpa [qd] using Nat.mod_add_div Rd (2 ^ n)
  have hCommon :
      Rc + 2 ^ n * qd = Rd + 2 ^ n * qc := by
    calc
      Rc + 2 ^ n * qd
          = (Rc % 2 ^ n + 2 ^ n * qc) + 2 ^ n * qd := by
              exact congrArg
                (fun t : ℕ => t + 2 ^ n * qd)
                hRc.symm
      _ = (Rd % 2 ^ n + 2 ^ n * qc) + 2 ^ n * qd := by
              rw [hMod]
      _ = (Rd % 2 ^ n + 2 ^ n * qd) + 2 ^ n * qc := by
              ring
      _ = Rd + 2 ^ n * qc := by
              exact congrArg
                (fun t : ℕ => t + 2 ^ n * qc)
                hRd
  have hCanC := Word.canonical_endpointEquation c.blocks
  have hCanD := Word.canonical_endpointEquation d.blocks
  have hLiftC := endpointEquation_prefixLift hCanC qd
  have hLiftD := endpointEquation_prefixLift hCanD qc
  have hEqC :
      Word.EndpointEquation c.blocks
        (Rc + 2 ^ n * qd)
        (Word.canonicalEnd c.blocks + 3 ^ c.length * qd) := by
    simpa [Rc] using hLiftC
  have hEqD :
      Word.EndpointEquation d.blocks
        (Rc + 2 ^ n * qd)
        (Word.canonicalEnd d.blocks + 3 ^ d.length * qc) := by
    have hLiftD' :
        Word.EndpointEquation d.blocks
          (Rd + 2 ^ n * qc)
          (Word.canonicalEnd d.blocks + 3 ^ d.length * qc) := by
      simpa [Rd] using hLiftD
    rw [← hCommon] at hLiftD'
    exact hLiftD'
  have hValidC : Word.Valid c.blocks := by
    intro e he
    exact c.blocks_pos he
  have hValidD : Word.Valid d.blocks := by
    intro e he
    exact d.blocks_pos he
  have hNeC : c.blocks ≠ [] :=
    parityComposition_blocks_ne_nil hn c
  have hNeD : d.blocks ≠ [] :=
    parityComposition_blocks_ne_nil hn d
  have hRunC :
      ParityPrefixRuns c.blocks
        (Rc + 2 ^ n * qd)
        (Word.canonicalEnd c.blocks + 3 ^ c.length * qd) :=
    parityPrefixRuns_of_valid_endpointEquation
      hValidC hNeC hEqC
  have hRunD :
      ParityPrefixRuns d.blocks
        (Rc + 2 ^ n * qd)
        (Word.canonicalEnd d.blocks + 3 ^ d.length * qc) :=
    parityPrefixRuns_of_valid_endpointEquation
      hValidD hNeD hEqD
  have hWords : c.blocks = d.blocks :=
    parityPrefixRuns_word_eq_of_common_start_same_twoSteps
      hRunC hRunD (by simp)
  apply Composition.ext
  exact hWords

/-- parity composition と actual odd residue modulo `2^n` の exact equivalence。 -/
noncomputable def parityCompositionEquivOddResidue
    (n : ℕ)
    (hn : 0 < n) :
    ParityComposition n ≃ OddParityResidue n := by
  let f := parityCompositionResidue hn
  have hCardDom : Nat.card (ParityComposition n) = 2 ^ (n - 1) := by
    rw [Nat.card_eq_fintype_card]
    exact parityComposition_card n
  have hCardCod : Nat.card (OddParityResidue n) = 2 ^ (n - 1) :=
    natCard_oddParityResidue hn
  have hBij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).2
      ⟨parityCompositionResidue_injective hn, hCardDom.trans hCardCod.symm⟩
  exact Equiv.ofBijective f hBij

/-- every odd residue below `2^n` has a unique finite parity composition。 -/
theorem existsUnique_parityComposition_of_oddResidue
    {n : ℕ}
    (hn : 0 < n)
    (r : OddParityResidue n) :
    ∃! c : ParityComposition n,
      parityCompositionResidue hn c = r := by
  let e := parityCompositionEquivOddResidue n hn
  refine ⟨e.symm r, e.apply_symm_apply r, ?_⟩
  intro c hc
  apply e.injective
  exact hc.trans (e.apply_symm_apply r).symm

end Bridge
end Collatz3
