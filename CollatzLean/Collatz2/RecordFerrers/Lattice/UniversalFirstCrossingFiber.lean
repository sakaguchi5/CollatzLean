import CollatzLean.Collatz2.RecordFerrers.Deformation.InteriorPermutation

/-!
# Record–Ferrers RF-A+7: universal FirstCrossing fiber and chord shear

FirstCrossing の proper-prefix geometry は terminal depth `H` ではなく、
`criticalShape p` 以下の Ferrers shape だけで決まる。

このファイルでは H-independent な universal object を導入し、任意の contracting depth
`H` への exact realization と、depth を変えたときの chord-rank shear law を与える。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- length `p` の universal FirstCrossing Ferrers object。terminal depth を持たない。 -/
structure CriticalSubshape (p : ℕ) where
  shape : FerrersShape p
  below : IsCriticalSubshape shape

namespace CriticalSubshape

@[ext] theorem ext
    {p : ℕ}
    {A B : CriticalSubshape p}
    (h : A.shape = B.shape) :
    A = B := by
  cases A
  cases B
  simp_all

/-- contracting terminal depth `H` を指定すると universal shape は exact FiberShape になる。 -/
def toFiberShape
    {p : ℕ}
    (S : CriticalSubshape p)
    (H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) : FiberShape p H := by
  have hCritLt : criticalHeight p < H :=
    criticalHeight_lt_terminalDepth_of_contractingChord hp hContract
  have hpCrit : p ≤ criticalHeight p := index_le_criticalHeight p
  have hpH : p ≤ H := by omega
  refine {
    shape := S.shape
    p_pos := hp
    p_le_H := hpH
    first_zero := ?_
    bounded := ?_
  }
  · have h0 := S.below ⟨0, hp⟩
    have hCrit0 :
        (criticalShape p).column ⟨0, hp⟩ = 0 := by
      simp [criticalShape, criticalExcess, criticalHeight]
    rw [hCrit0] at h0
    omega
  · intro i
    have hMono : criticalExcess i.1 ≤ criticalExcess p :=
      criticalExcess_mono (Nat.le_of_lt i.isLt)
    have hExP : criticalExcess p ≤ H - p := by
      unfold criticalExcess
      omega
    have hCritBound :
        (criticalShape p).column i ≤ H - p := by
      change criticalExcess i.1 ≤ H - p
      exact hMono.trans hExP
    exact (S.below i).trans hCritBound

/-- universal shape の contracting depth `H` realization。 -/
def toFiberPoint
    {p : ℕ}
    (S : CriticalSubshape p)
    (H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) : FiberPoint p H :=
  (S.toFiberShape H hp hContract).toFiberPoint

/-- realization を Ferrers profile へ戻すと universal shape を exact に回収する。 -/
@[simp] theorem toFiberPoint_toFerrersShape
    {p : ℕ}
    (S : CriticalSubshape p)
    (H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    (S.toFiberPoint H hp hContract).toFerrersShape = S.shape := by
  exact (S.toFiberShape H hp hContract).toFerrersShape_toFiberPoint

/-- universal shape の任意 contracting realization は FirstCrossing。 -/
theorem toFiberPoint_firstCrossing
    {p : ℕ}
    (S : CriticalSubshape p)
    (H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossing (S.toFiberPoint H hp hContract).word := by
  have h :=
    (S.toFiberShape H hp hContract).firstCrossing_toFiberPoint_iff hContract
  apply h.2
  exact S.below

/-- terminal depth を変えても proper prefix heights は全く変わらない。 -/
theorem height_acrossDepth_eq
    {p H K : ℕ}
    (S : CriticalSubshape p)
    (hp : 0 < p)
    (hH : ContractingChord p H)
    (hK : ContractingChord p K)
    {k : ℕ}
    (hk : k < p) :
    (S.toFiberPoint H hp hH).height k =
      (S.toFiberPoint K hp hK).height k := by
  change
    prefixTwoDepth (S.toFiberShape H hp hH).toWord k =
      prefixTwoDepth (S.toFiberShape K hp hK).toWord k
  rw [(S.toFiberShape H hp hH).prefixTwoDepth_toWord hk,
      (S.toFiberShape K hp hK).prefixTwoDepth_toWord hk]
  rfl

/-- proper cut では terminal depth change `H -> K` が chord rank に linear shear を与える。 -/
theorem chordRankInt_acrossDepth
    {p H K : ℕ}
    (S : CriticalSubshape p)
    (hp : 0 < p)
    (hH : ContractingChord p H)
    (hK : ContractingChord p K)
    {k : ℕ}
    (hk : k < p) :
    chordRankInt (S.toFiberPoint K hp hK).word k =
      chordRankInt (S.toFiberPoint H hp hH).word k +
        ((K : ℤ) - (H : ℤ)) * (k : ℤ) := by
  let xH := S.toFiberPoint H hp hH
  let xK := S.toFiberPoint K hp hK
  have hHeight := S.height_acrossDepth_eq hp hH hK hk
  unfold chordRankInt
  rw [xH.oddSteps_eq, xK.oddSteps_eq,
      xH.twoSteps_eq, xK.twoSteps_eq]
  change
    (K : ℤ) * (k : ℤ) - (p : ℤ) * (xK.height k : ℤ) =
      (H : ℤ) * (k : ℤ) - (p : ℤ) * (xH.height k : ℤ) +
        ((K : ℤ) - (H : ℤ)) * (k : ℤ)
  rw [hHeight]
  ring

/-- two proper cuts 間の rank gap の terminal-depth shear law。 -/
theorem rankGap_acrossDepth
    {p H K : ℕ}
    (S : CriticalSubshape p)
    (hp : 0 < p)
    (hH : ContractingChord p H)
    (hK : ContractingChord p K)
    {a b : ℕ}
    (ha : a < p)
    (hb : b < p) :
    rankGap (S.toFiberPoint K hp hK) a b =
      rankGap (S.toFiberPoint H hp hH) a b +
        ((K : ℤ) - (H : ℤ)) * ((b : ℤ) - (a : ℤ)) := by
  unfold rankGap
  rw [S.chordRankInt_acrossDepth hp hH hK hb,
      S.chordRankInt_acrossDepth hp hH hK ha]
  ring

/-- `H ≤ K` なら forward proper cuts `a ≤ b < p` の rank gap は depth とともに単調増加する。 -/
theorem rankGap_mono_acrossDepth
    {p H K : ℕ}
    (S : CriticalSubshape p)
    (hp : 0 < p)
    (hH : ContractingChord p H)
    (hK : ContractingChord p K)
    {a b : ℕ}
    (ha : a < p)
    (hb : b < p)
    (hHK : H ≤ K)
    (hab : a ≤ b) :
    rankGap (S.toFiberPoint H hp hH) a b ≤
      rankGap (S.toFiberPoint K hp hK) a b := by
  have hDepthZ : 0 ≤ (K : ℤ) - (H : ℤ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hHK)
  have hCutZ : 0 ≤ (b : ℤ) - (a : ℤ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hab)
  have hProd :
      0 ≤ ((K : ℤ) - (H : ℤ)) * ((b : ℤ) - (a : ℤ)) :=
    mul_nonneg hDepthZ hCutZ
  rw [S.rankGap_acrossDepth hp hH hK ha hb]
  linarith

end CriticalSubshape

/-- fixed `(p,H)` 上の FirstCrossing points。 -/
abbrev FirstCrossingFiber (p H : ℕ) :=
  {x : FiberPoint p H // FirstCrossing x.word}

namespace FirstCrossingFiber

/-- fixed-depth FirstCrossing point から H-independent shape へ忘却する。 -/
def toCriticalSubshape
    {p H : ℕ}
    (x : FirstCrossingFiber p H)
    (hp : 0 < p)
    (hContract : ContractingChord p H) : CriticalSubshape p :=
  { shape := x.1.toFerrersShape
    below :=
      (firstCrossing_iff_criticalSubshape x.1 hp hContract).1 x.2 }

/-- H-independent shape から fixed-depth FirstCrossing point を復号する。 -/
def ofCriticalSubshape
    {p H : ℕ}
    (S : CriticalSubshape p)
    (hp : 0 < p)
    (hContract : ContractingChord p H) : FirstCrossingFiber p H :=
  ⟨S.toFiberPoint H hp hContract,
    S.toFiberPoint_firstCrossing H hp hContract⟩

/--
任意 contracting depth `H` の FirstCrossing fiber は同じ universal critical-subshape space と exact 同値。
-/
def equivCriticalSubshape
    {p H : ℕ}
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossingFiber p H ≃ CriticalSubshape p where
  toFun := fun x => x.toCriticalSubshape hp hContract
  invFun := fun S => ofCriticalSubshape S hp hContract
  left_inv := by
    intro x
    apply Subtype.ext
    apply FiberPoint.toFerrersShape_injective
    have hShape :=
      (x.toCriticalSubshape hp hContract).toFiberPoint_toFerrersShape
        H hp hContract
    simp only [ofCriticalSubshape, toCriticalSubshape, CriticalSubshape.toFiberPoint_toFerrersShape]
  right_inv := by
    intro S
    apply CriticalSubshape.ext
    have hShape := S.toFiberPoint_toFerrersShape H hp hContract
    simp only [toCriticalSubshape, ofCriticalSubshape, CriticalSubshape.toFiberPoint_toFerrersShape]

/-- contracting depths `H,K` 間の canonical FirstCrossing-fiber equivalence。 -/
def equivAcrossDepth
    {p H K : ℕ}
    (hp : 0 < p)
    (hH : ContractingChord p H)
    (hK : ContractingChord p K) :
    FirstCrossingFiber p H ≃ FirstCrossingFiber p K :=
  (equivCriticalSubshape hp hH).trans
    (equivCriticalSubshape hp hK).symm

end FirstCrossingFiber

end RecordFerrers
end Collatz2
