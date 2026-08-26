import CollatzLean.Collatz2.Canonical.FiniteSurvivalClassification
import CollatzLean.Collatz2.Geometry.Center
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max

/-!
# Collatz2: nested finite survival から infinite survival へ

`FiniteSurvivalClassification` を nested prefix family へ持ち上げる。

正本は、固定 start `x` に対して

* finite survival word が nested に延長されること
* odd-start residue modulus が任意に深くなること

だけを保持する `NestedSurvivalChain` である。

この正本から次を導く。

1. `NestedResidueStabilization`
   深い prefix では canonical start が固定 start `x` そのものになる。
2. `DeepIsolationOfContractingPrefix`
   一つの contracting prefix と十分深い residue modulus があれば、
   その深さで finite survival start は `x` 一点に孤立する。
3. `InfiniteSurvivalDichotomy`
   infinite survival は forever-expanding か eventually-singleton survival のどちらか。
4. `BarrierEnvelopeEventuallyConstant`
   endpoint value が反復しない chain では strict record-low center は有限回しか更新されない。

最後の定理でいう eventual constant は、division-free center envelope の値を
有理除算で新しく定義せず、strict record update が最終的に存在しなくなることとして表す。
-/

namespace Collatz2
namespace Word

/--
固定 start `x` に対する nested finite-survival family。

`endpoint` / `run` を lossless に保持し、finite survival 自体は
`run + survives` から導く。`modulusEscapes` は 2-adic cylinder が
任意の整数閾値を越えて深くなることを表す。
-/
structure NestedSurvivalChain (x : ℕ) where
  word : ℕ → Word
  endpoint : ℕ → ℕ
  valid : ∀ n, (word n).Valid
  nonempty : ∀ n, word n ≠ []
  run : ∀ n, Runs (word n) x (endpoint n)
  survives : ∀ n, AllPrefixesSurviveAt (word n) x
  nested : ∀ {m n : ℕ}, m ≤ n → ∃ v : Word, word m ++ v = word n
  modulusEscapes :
    ∀ K : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (residueModulus (word n) : ℤ)

namespace NestedSurvivalChain

/-- 各段は finite survival start を与える。 -/
theorem finiteSurvival
    {x : ℕ}
    (C : NestedSurvivalChain x)
    (n : ℕ) :
    FiniteSurvivalStart (C.word n) x := by
  exact ⟨⟨C.endpoint n, C.run n⟩, C.survives n⟩

/-- 各 actual endpoint は固定 start 以上。 -/
theorem start_le_endpoint
    {x : ℕ}
    (C : NestedSurvivalChain x)
    (n : ℕ) :
    x ≤ C.endpoint n := by
  exact C.survives n (C.word n) [] (by simp) (C.endpoint n) (C.run n)

/--
## NestedResidueStabilization

固定 `x` を全段で finite-survive し、residue modulus が無限に深くなるなら、
十分深い全 prefix で canonical start は exact に `x` へ固定される。
-/
theorem nestedResidueStabilization
    {x : ℕ}
    (C : NestedSurvivalChain x) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      canonicalStart (C.word n) = x := by
  obtain ⟨N, hN⟩ := C.modulusEscapes (x : ℤ)
  refine ⟨N, ?_⟩
  intro n hn
  have hmodZ : (x : ℤ) < (residueModulus (C.word n) : ℤ) := hN n hn
  have hmodN : x < residueModulus (C.word n) := by
    exact_mod_cast hmodZ
  have hclass :
      x % residueModulus (C.word n) = canonicalStart (C.word n) :=
    ((finiteSurvivalClassification (C.valid n) (C.nonempty n)).1
      (C.finiteSurvival n)).1
  rw [Nat.mod_eq_of_lt hmodN] at hclass
  exact hclass.symm

/--
actual endpoint が start 以上なら、endpoint での displacement は非負であり、
各 prefix transfer は

`-determinant * endpoint ≤ translate`

という division-free barrier を満たす。
-/
theorem endpoint_displacementBarrier
    {x : ℕ}
    (C : NestedSurvivalChain x)
    (n : ℕ) :
    (-(AffineTransfer.ofWord (C.word n)).determinant) *
        (C.endpoint n : ℤ) ≤
      ((AffineTransfer.ofWord (C.word n)).translate : ℤ) := by
  let T := AffineTransfer.ofWord (C.word n)
  have hreal : T.Realizes x (C.endpoint n) := (C.run n).realizes
  have heval := hreal.displacementForm_eval_end
  have hxyN : x ≤ C.endpoint n := C.start_le_endpoint n
  have hxy : (0 : ℤ) ≤ (C.endpoint n : ℤ) - (x : ℤ) := by
    omega
  have hCnonneg : (0 : ℤ) ≤ (T.oddCoeff : ℤ) := by
    positivity
  have hevalNonneg :
      0 ≤ T.displacementForm.eval (C.endpoint n : ℤ) := by
    rw [heval]
    exact mul_nonneg hCnonneg hxy
  change
    0 ≤ (T.translate : ℤ) + T.determinant * (C.endpoint n : ℤ)
    at hevalNonneg
  nlinarith

/--
center が `U` より strict に低い contracting transfer `T` の surviving actual endpoint は、
`U.translate` より小さい。record-low center の endpoint を有限範囲へ押し込む補助定理。
-/
theorem endpoint_lt_translate_of_centerRises
    {x : ℕ}
    (C : NestedSurvivalChain x)
    {m n : ℕ}
    (hmC : Contracting (C.word m))
    (hnC : Contracting (C.word n))
    (hRise :
      (AffineTransfer.ofWord (C.word n)).CenterRises
        (AffineTransfer.ofWord (C.word m))) :
    C.endpoint n < (AffineTransfer.ofWord (C.word m)).translate := by
  let Tn := AffineTransfer.ofWord (C.word n)
  let Tm := AffineTransfer.ofWord (C.word m)
  let gn : ℤ := -Tn.determinant
  let gm : ℤ := -Tm.determinant
  have hnDet : Tn.determinant < 0 := by
    simpa [Tn, Contracting, AffineTransfer.NegativeDeterminant] using hnC
  have hmDet : Tm.determinant < 0 := by
    simpa [Tm, Contracting, AffineTransfer.NegativeDeterminant] using hmC
  have hgn : 0 < gn := by
    dsimp [gn]
    exact neg_pos.mpr hnDet
  have hgm : 0 < gm := by
    dsimp [gm]
    exact neg_pos.mpr hmDet
  have hbar : gn * (C.endpoint n : ℤ) ≤ (Tn.translate : ℤ) := by
    simpa [gn, Tn] using C.endpoint_displacementBarrier n
  have hsep :
      (Tn.translate : ℤ) * gm <
        (Tm.translate : ℤ) * gn := by
    simpa [AffineTransfer.CenterRises, gn, gm, Tn, Tm] using hRise
  have hmul := mul_le_mul_of_nonneg_right hbar (le_of_lt hgm)
  have hchain :
      gn * ((C.endpoint n : ℤ) * gm) <
        gn * (Tm.translate : ℤ) := by
    calc
      gn * ((C.endpoint n : ℤ) * gm)
          = (gn * (C.endpoint n : ℤ)) * gm := by ring
      _ ≤ (Tn.translate : ℤ) * gm := hmul
      _ < (Tm.translate : ℤ) * gn := hsep
      _ = gn * (Tm.translate : ℤ) := by ring
  have hcancel :
      (C.endpoint n : ℤ) * gm < (Tm.translate : ℤ) := by
    exact (Int.mul_lt_mul_left hgn).mp hchain
  have hgmOne : (1 : ℤ) ≤ gm := by omega
  have hyNonneg : (0 : ℤ) ≤ (C.endpoint n : ℤ) := by positivity
  have hyLe :
      (C.endpoint n : ℤ) ≤ (C.endpoint n : ℤ) * gm := by
    calc
      (C.endpoint n : ℤ) = (C.endpoint n : ℤ) * 1 := by ring
      _ ≤ (C.endpoint n : ℤ) * gm :=
        mul_le_mul_of_nonneg_left hgmOne hyNonneg
  have hyLt :
      (C.endpoint n : ℤ) < (Tm.translate : ℤ) :=
    lt_of_le_of_lt hyLe hcancel
  exact_mod_cast hyLt

/--
## DeepIsolationOfContractingPrefix

`m` 段目の contracting prefix の anchored defect を `D`、gap を `G` とする。
深い `n` 段目で

  `D < G * residueModulus(word n)`

となり、かつその深さの canonical start が `x` なら、同じ深さを finite-survive する
任意の start `z` は `x` に一致する。
-/
theorem deepIsolationOfContractingPrefix
    {x : ℕ}
    (C : NestedSurvivalChain x)
    {m n z : ℕ}
    (hmn : m ≤ n)
    (hmC : Contracting (C.word m))
    (hcanonical : canonicalStart (C.word n) = x)
    (hdeep :
      startDefect (C.word m) x <
        (-(AffineTransfer.ofWord (C.word m)).determinant) *
          (residueModulus (C.word n) : ℤ))
    (hz : FiniteSurvivalStart (C.word n) z) :
    z = x := by
  let M : ℕ := residueModulus (C.word n)
  let T := AffineTransfer.ofWord (C.word m)
  let g : ℤ := -T.determinant
  obtain ⟨v, hprefix⟩ := C.nested hmn
  have hzClass :=
    (finiteSurvivalClassification (C.valid n) (C.nonempty n)).1 hz
  have hzMod : z % M = x := by
    dsimp [M]
    simpa [hcanonical] using hzClass.1
  have hxLtM : x < M := by
    dsimp [M]
    have hlt :
        canonicalStart (C.word n) <
          residueModulus (C.word n) :=
      canonicalStart_lt_modulus (C.word n)
    rw [hcanonical] at hlt
    exact hlt
  have hdecomp := Nat.mod_add_div z M
  rw [hzMod] at hdecomp
  let q : ℕ := z / M
  have hzEq : z = x + M * q := by
    dsimp [q]
    simpa [Nat.mul_comm] using hdecomp.symm
  by_cases hq : q = 0
  · rw [hzEq, hq]
    simp
  · have hqPos : 0 < q := Nat.pos_of_ne_zero hq
    have hbarz :
        g * (z : ℤ) ≤ (T.translate : ℤ) := by
      have hmDet : (AffineTransfer.ofWord (C.word m)).determinant < 0 := by
        simpa [Contracting, AffineTransfer.NegativeDeterminant] using hmC
      have h := hzClass.2 (C.word m) v hprefix hmDet
      simpa [g, T] using h
    have hdefEq :
        startDefect (C.word m) x =
          (T.translate : ℤ) - g * (x : ℤ) := by
      change
        (T.translate : ℤ) + T.determinant * (x : ℤ) =
          (T.translate : ℤ) - g * (x : ℤ)
      dsimp [g]
      ring
    have hzEqZ :
        (z : ℤ) = (x : ℤ) + (M : ℤ) * (q : ℤ) := by
      exact_mod_cast hzEq
    have hMqN : M ≤ M * q := by
      have hqOne : 1 ≤ q := hqPos
      calc
        M = M * 1 := by simp
        _ ≤ M * q := Nat.mul_le_mul_left M hqOne
    have hMqZ : (M : ℤ) ≤ (M : ℤ) * (q : ℤ) := by
      exact_mod_cast hMqN
    have hmDet : T.determinant < 0 := by
      simpa [T, Contracting, AffineTransfer.NegativeDeterminant] using hmC
    have hgPos : 0 < g := by
      dsimp [g]
      exact neg_pos.mpr hmDet
    have hGMle :
        g * (M : ℤ) ≤ g * ((M : ℤ) * (q : ℤ)) :=
      mul_le_mul_of_nonneg_left hMqZ (le_of_lt hgPos)
    have hbarz' := hbarz
    rw [hzEqZ] at hbarz'
    have htailLe :
        g * ((M : ℤ) * (q : ℤ)) ≤ startDefect (C.word m) x := by
      rw [hdefEq]
      nlinarith [hbarz']
    exact False.elim ((not_lt_of_ge (le_trans hGMle htailLe)) hdeep)

/-- 全段が expanding である branch。 -/
def ForeverExpanding
    {x : ℕ}
    (C : NestedSurvivalChain x) : Prop :=
  ∀ n : ℕ, Expanding (C.word n)

/-- 十分深い全段で finite-survival start が `x` 一点だけになる branch。 -/
def EventuallySingletonSurvival
    {x : ℕ}
    (C : NestedSurvivalChain x) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ z : ℕ, FiniteSurvivalStart (C.word n) z → z = x

/--
## InfiniteSurvivalDichotomy

nested infinite survival は、全 prefix が forever expanding であるか、
一度 contracting prefix が現れた後 sufficiently deep で survival start が `x` 一点に
孤立するかのどちらか。
-/
theorem infiniteSurvivalDichotomy
    {x : ℕ}
    (C : NestedSurvivalChain x) :
    ForeverExpanding C ∨ EventuallySingletonSurvival C := by
  classical
  by_cases hE : ForeverExpanding C
  · exact Or.inl hE
  · right
    have hex : ∃ m : ℕ, ¬ Expanding (C.word m) := by
      simpa [ForeverExpanding] using hE
    obtain ⟨m, hmNotExp⟩ := hex
    have hmC : Contracting (C.word m) := by
      rcases expanding_or_contracting_of_valid_nonempty
          (C.valid m) (C.nonempty m) with hExp | hCon
      · exact False.elim (hmNotExp hExp)
      · exact hCon
    let D : ℤ := startDefect (C.word m) x
    obtain ⟨N0, hN0⟩ := C.modulusEscapes (max (x : ℤ) D)
    let N : ℕ := max m N0
    refine ⟨N, ?_⟩
    intro n hn z hz
    have hmn : m ≤ n :=
      le_trans (le_max_left m N0) hn
    have hN0n : N0 ≤ n :=
      le_trans (le_max_right m N0) hn
    have hdeepMod :
        max (x : ℤ) D < (residueModulus (C.word n) : ℤ) :=
      hN0 n hN0n
    have hxModZ :
        (x : ℤ) < (residueModulus (C.word n) : ℤ) :=
      lt_of_le_of_lt (le_max_left _ _) hdeepMod
    have hxModN : x < residueModulus (C.word n) := by
      exact_mod_cast hxModZ
    have hxClass :=
      ((finiteSurvivalClassification (C.valid n) (C.nonempty n)).1
        (C.finiteSurvival n)).1
    have hcanonical : canonicalStart (C.word n) = x := by
      rw [Nat.mod_eq_of_lt hxModN] at hxClass
      exact hxClass.symm
    let T := AffineTransfer.ofWord (C.word m)
    let g : ℤ := -T.determinant
    have hmDet : T.determinant < 0 := by
      simpa [T, Contracting, AffineTransfer.NegativeDeterminant] using hmC
    have hgPos : 0 < g := by
      dsimp [g]
      exact neg_pos.mpr hmDet
    have hDltM :
        D < (residueModulus (C.word n) : ℤ) :=
      lt_of_le_of_lt (le_max_right _ _) hdeepMod
    have hMnonneg :
        (0 : ℤ) ≤ (residueModulus (C.word n) : ℤ) := by positivity
    have hgOne : (1 : ℤ) ≤ g := by omega
    have hMleGM :
        (residueModulus (C.word n) : ℤ) ≤
          g * (residueModulus (C.word n) : ℤ) := by
      calc
        (residueModulus (C.word n) : ℤ)
            = 1 * (residueModulus (C.word n) : ℤ) := by ring
        _ ≤ g * (residueModulus (C.word n) : ℤ) :=
          mul_le_mul_of_nonneg_right hgOne hMnonneg
    have hdeep :
        startDefect (C.word m) x <
          (-(AffineTransfer.ofWord (C.word m)).determinant) *
            (residueModulus (C.word n) : ℤ) := by
      have hDltGM :
          D < g * (residueModulus (C.word n) : ℤ) :=
        lt_of_lt_of_le hDltM hMleGM
      simpa [D, g, T] using hDltGM
    exact C.deepIsolationOfContractingPrefix
      hmn hmC hcanonical hdeep hz

/--
contracting center の strict record-low event。
`n` の center が、それ以前の全 contracting center より strict に低いことを表す。
-/
def BarrierRecord
    {x : ℕ}
    (C : NestedSurvivalChain x)
    (n : ℕ) : Prop :=
  Contracting (C.word n) ∧
    ∀ k : ℕ, k < n → Contracting (C.word k) →
      (AffineTransfer.ofWord (C.word n)).CenterRises
        (AffineTransfer.ofWord (C.word k))

/--
## BarrierEnvelopeEventuallyConstant

endpoint value が反復しない aperiodic chain で contracting prefix が一つでも存在するなら、
strict record-low center は有限回しか現れない。
従って division-free contracting-center envelope は有限段階以後更新されない。
-/
theorem barrierEnvelopeEventuallyConstant
    {x : ℕ}
    (C : NestedSurvivalChain x)
    (haperiodic : Function.Injective C.endpoint)
    (hex : ∃ n : ℕ, Contracting (C.word n)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ BarrierRecord C n := by
  classical
  let b : ℕ := Nat.find hex
  have hbC : Contracting (C.word b) := by
    dsimp [b]
    exact Nat.find_spec hex
  have hbMin :
      ∀ k : ℕ, k < b → ¬ Contracting (C.word k) := by
    intro k hk
    exact Nat.find_min hex (by simpa [b] using hk)
  have hbRecord : BarrierRecord C b := by
    refine ⟨hbC, ?_⟩
    intro k hk hkC
    exact False.elim ((hbMin k hk) hkC)
  let RecordIndex := {n : ℕ // BarrierRecord C n}
  let B : ℕ := (AffineTransfer.ofWord (C.word b)).translate
  have hrecordBound :
      ∀ r : RecordIndex, C.endpoint r.1 < B + 1 := by
    intro r
    have hrC : Contracting (C.word r.1) := r.2.1
    have hbLe : b ≤ r.1 := by
      by_contra hnot
      have hrLt : r.1 < b := Nat.lt_of_not_ge hnot
      exact (hbMin r.1 hrLt) hrC
    by_cases hrb : r.1 = b
    · have hbar := C.endpoint_displacementBarrier b
      let Tb := AffineTransfer.ofWord (C.word b)
      let gb : ℤ := -Tb.determinant
      have hbDet : Tb.determinant < 0 := by
        simpa [Tb, Contracting, AffineTransfer.NegativeDeterminant] using hbC
      have hgb : 0 < gb := by
        dsimp [gb]
        exact neg_pos.mpr hbDet
      have hgbOne : (1 : ℤ) ≤ gb := by omega
      have hyNonneg : (0 : ℤ) ≤ (C.endpoint b : ℤ) := by positivity
      have hyLeMul :
          (C.endpoint b : ℤ) ≤ gb * (C.endpoint b : ℤ) := by
        calc
          (C.endpoint b : ℤ) = 1 * (C.endpoint b : ℤ) := by ring
          _ ≤ gb * (C.endpoint b : ℤ) :=
            mul_le_mul_of_nonneg_right hgbOne hyNonneg
      have hyLeB :
          (C.endpoint b : ℤ) ≤ (Tb.translate : ℤ) := by
        exact le_trans hyLeMul (by simpa [gb, Tb] using hbar)
      have hyLeBN :
          C.endpoint b ≤ Tb.translate := by
        exact_mod_cast hyLeB
      have hyrLeBN :
          C.endpoint r.1 ≤ Tb.translate := by
        simpa [hrb] using hyLeBN
      have hyrLeB :
          C.endpoint r.1 ≤
            (AffineTransfer.ofWord (C.word b)).translate := by
        simpa [Tb] using hyrLeBN
      dsimp [B]
      simpa [Nat.succ_eq_add_one] using
        Nat.lt_succ_of_le hyrLeB
    · have hbLt :
          b < r.1 :=
        lt_of_le_of_ne hbLe (Ne.symm hrb)
      have hRise :=
        r.2.2 b hbLt hbC
      have hyLtB :
          C.endpoint r.1 <
            (AffineTransfer.ofWord (C.word b)).translate :=
        C.endpoint_lt_translate_of_centerRises
          hbC hrC hRise
      dsimp [B]
      exact lt_trans hyLtB (Nat.lt_succ_self _)
  let f : RecordIndex → Fin (B + 1) :=
    fun r => ⟨C.endpoint r.1, hrecordBound r⟩
  have hfInjective : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply haperiodic
    exact congrArg Fin.val hrs
  let : Finite RecordIndex := Finite.of_injective f hfInjective
  let : Fintype RecordIndex := Fintype.ofFinite RecordIndex
  let recordValues : Finset ℕ :=
    Finset.univ.image (fun r : RecordIndex => r.1)
  have hrecordValuesNonempty : recordValues.Nonempty := by
    refine ⟨b, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨b, hbRecord⟩, Finset.mem_univ _, rfl⟩
  let m : ℕ := recordValues.max' hrecordValuesNonempty
  refine ⟨m + 1, ?_⟩
  intro n hn hnRecord
  have hnMem : n ∈ recordValues := by
    apply Finset.mem_image.mpr
    exact ⟨⟨n, hnRecord⟩, Finset.mem_univ _, rfl⟩
  have hnLe : n ≤ m := by
    dsimp [m]
    exact Finset.le_max' recordValues n hnMem
  omega

end NestedSurvivalChain
end Word
end Collatz2
