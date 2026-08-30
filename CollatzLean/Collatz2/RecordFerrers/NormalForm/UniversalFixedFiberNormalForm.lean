import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedPotential
import Mathlib.Order.WellFounded

/-!
# Universal Fixed-Fiber Normal Form

RecordFerrers の fixed `(p,H)` fiber 全体に対する、FirstCrossing / primitive /
StripReduced に依存しない普遍的 normal form 層。

このファイルでは項目 1–7 をまとめ、項目 8 の matrix corollary は
`RecordFerrers/Matrix/UniversalExcessRepresentation.lean` に分離する。

1. fixed `(p,H)` に canonical bottom word を置き、validity と chord 保存を示す。
2. 任意の valid nonempty exponent word は adjacent right-transfer の有限列で bottom へ到達する。
3. right-transfer は `affineConst` を strict に下げるため停止し、bottom が一意 normal form で、
   valid fixed fiber 上では合流する。
4. universal excess

      E(x) = weightedArea(x)

   は

      E(x) = affineConst(x) - (3^p - 2^p)

   と exact に一致する。
5. `E(x)=0` と `x=bottom` は同値。
6. fixed `(p,H)` では `E` 一個が FiberPoint を lossless に識別する。
7. adjacent right-transfer 一歩の `E` loss は、その一個の Ferrers cell weight と exact に一致する。
8. （別 bridge）upper-triangular representation は

      M(x) = M_bottom(p,H) + E(x) * e₁₂

   に exact 分解する。

重要なのは、項目 1–7 では record decomposition も CSTMicro の carry/no-carry も使わないこと。
それらはこの universal fixed-fiber normal form の上に載る精密化として扱う。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 0. canonical bottom と universal excess -/

/--
fixed `(p,H)` の canonical bottom word。

`p > 0`, `p ≤ H` のとき

  `[1, 1, ..., 1, H-p+1]`

であり、余分な two-depth をすべて最後の exponent に押し込んだ形になる。
-/
def universalBottomWord (p H : ℕ) : Word :=
  List.replicate (p - 1) 1 ++ [H - p + 1]

/-- universal bottom は odd-step 数 `p` を exact に持つ。 -/
theorem universalBottomWord_oddSteps
    {p H : ℕ}
    (hp : 0 < p) :
    oddSteps (universalBottomWord p H) = p := by
  unfold universalBottomWord oddSteps
  simp
  omega

/-- universal bottom は total two-depth `H` を exact に持つ。 -/
theorem universalBottomWord_twoSteps
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    twoSteps (universalBottomWord p H) = H := by
  unfold universalBottomWord twoSteps
  rw [List.sum_append]
  simp
  omega

/-- universal bottom の全 exponent は正。 -/
theorem universalBottomWord_valid
    {p H : ℕ} :
    Valid (universalBottomWord p H) := by
  intro e he
  unfold universalBottomWord at he
  rw [List.mem_append] at he
  rcases he with hRep | hLast
  · have heq : e = 1 := List.eq_of_mem_replicate hRep
    omega
  · have heq : e = H - p + 1 := by
      simpa using hLast
    omega

/--
`p,H` を一つずつ増やすと bottom の先頭に `1` が一つ付く。
normalization の帰納法で使う recursive law。
-/
theorem universalBottomWord_succ
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    universalBottomWord (p + 1) (H + 1) =
      1 :: universalBottomWord p H := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hLast :
      (H + 1) - ((q + 1) + 1) + 1 =
        H - (q + 1) + 1 := by
    omega
  simp [universalBottomWord, List.replicate_succ]

/-- explicit bottom word を fixed-fiber point として package する。 -/
def universalBottomPoint
    (p H : ℕ)
    (hp : 0 < p)
    (hpH : p ≤ H) : FiberPoint p H :=
  { word := universalBottomWord p H
    valid := universalBottomWord_valid
    oddSteps_eq := universalBottomWord_oddSteps hp
    twoSteps_eq := universalBottomWord_twoSteps hp hpH }

/--
## 1. Bottom chord preservation

canonical bottom は source と同じ `(oddSteps,twoSteps)=(p,H)` を持つ。
型 `FiberPoint p H` 自体がこの保存を担保するが、公開 API として明示する。
-/
theorem universalBottomPoint_same_chord
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    oddSteps (universalBottomPoint p H hp hpH).word = p ∧
      twoSteps (universalBottomPoint p H hp hpH).word = H := by
  exact ⟨
    (universalBottomPoint p H hp hpH).oddSteps_eq,
    (universalBottomPoint p H hp hpH).twoSteps_eq
  ⟩

/--
fixed-fiber 内の普遍的 excess。

これは ordinary Ferrers area ではなく、Collatz affine translation を exact に復元する
`weightedArea` である。
-/
def universalExcess
    {p H : ℕ}
    (x : FiberPoint p H) : ℕ :=
  weightedArea x.toFerrersShape

/-- `B = (3^p-2^p) + E` の内部共通形。 -/
private theorem affineConst_eq_baseline_add_universalExcess_core
    {p H : ℕ}
    (x : FiberPoint p H) :
    affineConst x.word =
      (3 ^ p - 2 ^ p) + universalExcess x := by
  simpa [universalExcess, baseAffineConst_eq_threePow_sub_twoPow] using
    (affineConst_eq_base_add_weightedArea x)

/-- bottom の proper prefix depth は cut index そのもの。 -/
theorem universalBottomWord_prefixTwoDepth
    {p H k : ℕ}
    (hp : 0 < p)
    (hk : k < p) :
    prefixTwoDepth (universalBottomWord p H) k = k := by
  have hkLe : k ≤ p - 1 := by
    omega
  unfold universalBottomWord prefixTwoDepth
  rw [List.take_append_of_le_length (by simpa using hkLe)]
  simp [twoSteps, hkLe]

/-- explicit bottom point の Ferrers shape は all-zero shape。 -/
theorem universalBottomPoint_toFerrersShape
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    (universalBottomPoint p H hp hpH).toFerrersShape =
      FerrersShape.zero p := by
  apply FerrersShape.ext
  intro i
  change
    (universalBottomPoint p H hp hpH).excessAt i.1 = 0
  unfold FiberPoint.excessAt FiberPoint.height universalBottomPoint
  rw [universalBottomWord_prefixTwoDepth hp i.isLt]
  omega

/-- universal bottom の excess は 0。 -/
@[simp] theorem universalExcess_bottom
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    universalExcess (universalBottomPoint p H hp hpH) = 0 := by
  unfold universalExcess
  rw [universalBottomPoint_toFerrersShape hp hpH]
  exact FerrersShape.weightedArea_zero p

/-- explicit bottom は既存 `FiberShape.bottom` と同じ canonical bottom。 -/
theorem universalBottomPoint_eq_latticeBottom
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    universalBottomPoint p H hp hpH =
      (FiberShape.bottom p H hp hpH).toFiberPoint := by
  apply FiberPoint.toFerrersShape_injective
  rw [universalBottomPoint_toFerrersShape hp hpH]
  rw [FiberShape.toFerrersShape_toFiberPoint]
  rfl

/-! ## 2. adjacent right-transfer -/

/--
一つの exponent unit を隣の右 block へ送る局所変形の witness data。

  left ++ (a+1) :: b :: right
    ⟶
  left ++ a :: (b+1) :: right

`a>0` なので source / target の両方で左 exponent は正のまま。
-/
structure AdjacentRightTransferData (source target : Word) where
  left : Word
  right : Word
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  source_eq :
    source = left ++ (a + 1) :: b :: right
  target_eq :
    target = left ++ a :: (b + 1) :: right

namespace AdjacentRightTransferData

/-- 一歩が動かす Ferrers cell の affine weight。 -/
def cellWeight
    {source target : Word}
    (S : AdjacentRightTransferData source target) : ℕ :=
  2 ^ (twoSteps S.left + S.a) * 3 ^ oddSteps S.right

/-- cell weight は常に正。 -/
theorem cellWeight_pos
    {source target : Word}
    (S : AdjacentRightTransferData source target) :
    0 < S.cellWeight := by
  unfold cellWeight
  positivity

/-- adjacent right-transfer は odd-step 数を保存する。 -/
theorem oddSteps_eq
    {source target : Word}
    (S : AdjacentRightTransferData source target) :
    oddSteps source = oddSteps target := by
  calc
    oddSteps source
        = oddSteps
            (S.left ++ (S.a + 1) :: S.b :: S.right) := by
            exact congrArg oddSteps S.source_eq
    _ = oddSteps
          (S.left ++ S.a :: (S.b + 1) :: S.right) := by
          simp [oddSteps]
    _ = oddSteps target := by
          exact (congrArg oddSteps S.target_eq).symm

/-- adjacent right-transfer は total two-depth を保存する。 -/
theorem twoSteps_eq
    {source target : Word}
    (S : AdjacentRightTransferData source target) :
    twoSteps source = twoSteps target := by
  calc
    twoSteps source
        = twoSteps
            (S.left ++ (S.a + 1) :: S.b :: S.right) := by
            exact congrArg twoSteps S.source_eq
    _ = twoSteps
          (S.left ++ S.a :: (S.b + 1) :: S.right) := by
          simp [twoSteps, List.sum_append]
          omega
    _ = twoSteps target := by
          exact (congrArg twoSteps S.target_eq).symm

/-- valid source から得る target も valid。 -/
theorem target_valid
    {source target : Word}
    (S : AdjacentRightTransferData source target)
    (hValid : Valid source) :
    Valid target := by
  intro e he
  rw [S.target_eq] at he
  rw [S.source_eq] at hValid
  simp only [List.mem_append, List.mem_cons] at he
  rcases he with hLeft | hRest
  · exact hValid e (by simp [hLeft])
  · rcases hRest with heA | hRest
    · subst e
      exact S.a_pos
    · rcases hRest with heB | hRight
      · subst e
        omega
      · exact hValid e (by simp [hRight])

/-- pair の内部だけで見た affine translation loss。 -/
private theorem affineConst_local_shift
    (a b : ℕ)
    (right : Word) :
    affineConst ((a + 1) :: b :: right) =
      affineConst (a :: (b + 1) :: right) +
        2 ^ a * 3 ^ oddSteps right := by
  simp only [affineConst_cons, oddSteps_cons, pow_succ]
  ring

/--
right-transfer 一歩で `B = affineConst` は cell weight だけ exact に減る。
-/
theorem affineConst_source_eq_target_add_cellWeight
    {source target : Word}
    (S : AdjacentRightTransferData source target) :
    affineConst source =
      affineConst target + S.cellWeight := by
  have hSource :
      affineConst source =
        affineConst
          (S.left ++ (S.a + 1) :: S.b :: S.right) :=
    congrArg affineConst S.source_eq
  have hTarget :
      affineConst target =
        affineConst
          (S.left ++ S.a :: (S.b + 1) :: S.right) :=
    congrArg affineConst S.target_eq
  calc
    affineConst source
        =
      affineConst
        (S.left ++ (S.a + 1) :: S.b :: S.right) := hSource
    _ =
      affineConst
          (S.left ++ S.a :: (S.b + 1) :: S.right) +
        S.cellWeight := by
        rw [affineConst_append, affineConst_append]
        have hLocal :=
          affineConst_local_shift S.a S.b S.right
        have hOdd :
            oddSteps ((S.a + 1) :: S.b :: S.right) =
              oddSteps (S.a :: (S.b + 1) :: S.right) := by
          simp
        rw [hOdd, hLocal]
        unfold AdjacentRightTransferData.cellWeight
        rw [pow_add]
        ring
    _ =
      affineConst target + S.cellWeight := by
        rw [← hTarget]

/-- right-transfer 一歩では genuine affine translation が strict に減る。 -/
theorem affineConst_target_lt_source
    {source target : Word}
    (S : AdjacentRightTransferData source target) :
    affineConst target < affineConst source := by
  have hEq := S.affineConst_source_eq_target_add_cellWeight
  have hPos := S.cellWeight_pos
  omega

/-- fixed FiberPoint 上の right-transfer target を同じ fiber の点として package する。 -/
def targetPoint
    {p H : ℕ}
    (x : FiberPoint p H)
    {target : Word}
    (S : AdjacentRightTransferData x.word target) : FiberPoint p H :=
  { word := target
    valid := S.target_valid x.valid
    oddSteps_eq := by
      calc
        oddSteps target = oddSteps x.word := S.oddSteps_eq.symm
        _ = p := x.oddSteps_eq
    twoSteps_eq := by
      calc
        twoSteps target = twoSteps x.word := S.twoSteps_eq.symm
        _ = H := x.twoSteps_eq }

end AdjacentRightTransferData

/-- data witness を忘れた one-step relation。 -/
def AdjacentRightTransfer (source target : Word) : Prop :=
  Nonempty (AdjacentRightTransferData source target)

/-- finite right-transfer sequence。 -/
inductive RightTransferChain : Word → Word → Prop
  | refl (w : Word) : RightTransferChain w w
  | step
      {u v z : Word}
      (S : AdjacentRightTransferData u v)
      (tail : RightTransferChain v z) :
      RightTransferChain u z

namespace RightTransferChain

/-- finite chain の連結。 -/
theorem trans
    {u v z : Word}
    (A : RightTransferChain u v)
    (B : RightTransferChain v z) :
    RightTransferChain u z := by
  induction A generalizing z with
  | refl =>
      exact B
  | step S tail ih =>
      exact RightTransferChain.step S (ih B)

/-- right-transfer data の前に共通 head を一つ付ける。 -/
def consData
    {u v : Word}
    (c : ℕ)
    (S : AdjacentRightTransferData u v) :
    AdjacentRightTransferData (c :: u) (c :: v) :=
  { left := c :: S.left
    right := S.right
    a := S.a
    b := S.b
    a_pos := S.a_pos

    source_eq := by
      exact congrArg
        (fun w : Word => c :: w)
        S.source_eq
    target_eq := by
      exact congrArg
        (fun w : Word => c :: w)
        S.target_eq }

/-- finite chain の前に共通 head を一つ付けても finite chain。 -/
theorem cons
    {u v : Word}
    (c : ℕ)
    (C : RightTransferChain u v) :
    RightTransferChain (c :: u) (c :: v) := by
  induction C with
  | refl =>
      exact RightTransferChain.refl _
  | step S tail ih =>
      exact RightTransferChain.step (consData c S) ih

/-- finite chain は odd-step 数を保存する。 -/
theorem oddSteps_eq
    {u v : Word}
    (C : RightTransferChain u v) :
    oddSteps u = oddSteps v := by
  induction C with
  | refl => rfl
  | step S tail ih =>
      exact S.oddSteps_eq.trans ih

/-- finite chain は total two-depth を保存する。 -/
theorem twoSteps_eq
    {u v : Word}
    (C : RightTransferChain u v) :
    twoSteps u = twoSteps v := by
  induction C with
  | refl => rfl
  | step S tail ih =>
      exact S.twoSteps_eq.trans ih

/-- valid source から始まる finite chain の target も valid。 -/
theorem target_valid
    {u v : Word}
    (C : RightTransferChain u v)
    (hValid : Valid u) :
    Valid v := by
  induction C with
  | refl =>
      exact hValid
  | step S tail ih =>
      exact ih (S.target_valid hValid)

/-- fixed FiberPoint から chain target を同じ fixed fiber の点として package する。 -/
def targetPoint
    {p H : ℕ}
    (x : FiberPoint p H)
    {target : Word}
    (C : RightTransferChain x.word target) : FiberPoint p H :=
  { word := target
    valid := C.target_valid x.valid
    oddSteps_eq := by
      calc
        oddSteps target = oddSteps x.word := C.oddSteps_eq.symm
        _ = p := x.oddSteps_eq
    twoSteps_eq := by
      calc
        twoSteps target = twoSteps x.word := C.twoSteps_eq.symm
        _ = H := x.twoSteps_eq }

/-- source が normal なら、そこから出る finite chain は refl しかない。 -/
theorem eq_of_source_normal
    {u v : Word}
    (C : RightTransferChain u v)
    (hNormal : ∀ z, ¬ AdjacentRightTransfer u z) :
    u = v := by
  cases C with
  | refl =>
      rfl
  | step S tail =>
      exact (hNormal _ ⟨S⟩).elim

end RightTransferChain

/--
head exponent `n+1` の余分な `n` 個を一つ右へ押し出す finite chain。

  (n+1) :: b :: right
    ⟶* 1 :: (b+n) :: right
-/
theorem pushHeadRight_chain
    (n b : ℕ)
    (right : Word) :
    RightTransferChain
      ((n + 1) :: b :: right)
      (1 :: (b + n) :: right) := by
  induction n generalizing b with
  | zero =>
      simpa using RightTransferChain.refl (1 :: b :: right)
  | succ n ih =>
      let S : AdjacentRightTransferData
          (((n + 1) + 1) :: b :: right)
          ((n + 1) :: (b + 1) :: right) :=
        { left := []
          right := right
          a := n + 1
          b := b
          a_pos := by omega
          source_eq := by simp
          target_eq := by simp }
      have hTail := ih (b + 1)
      have hEnd : (b + 1) + n = b + (n + 1) := by
        omega
      have hTail' :
          RightTransferChain
            ((n + 1) :: (b + 1) :: right)
            (1 :: (b + (n + 1)) :: right) := by
        simpa [hEnd] using hTail
      exact RightTransferChain.step S hTail'

/--
## 2. Finite normalization

任意の valid nonempty exponent word は adjacent right-transfer の有限列で
`universalBottomWord` へ到達する。
-/
theorem rightTransferChain_to_universalBottom_cons
    (e : ℕ)
    (tail : Word)
    (hValid : Valid (e :: tail)) :
    RightTransferChain
      (e :: tail)
      (universalBottomWord
        (oddSteps (e :: tail))
        (twoSteps (e :: tail))) := by
  induction tail generalizing e with
  | nil =>
      have he : 0 < e := hValid e (by simp)
      have hBottom : universalBottomWord 1 e = [e] := by
        unfold universalBottomWord
        simp
        omega
      simpa [oddSteps, twoSteps, hBottom] using
        RightTransferChain.refl [e]
  | cons f rest ih =>
      have he : 0 < e := hValid e (by simp)
      have hf : 0 < f := hValid f (by simp)
      let t : ℕ := f + (e - 1)
      have ht : 0 < t := by
        dsimp [t]
        omega
      have hHeadRaw := pushHeadRight_chain (e - 1) f rest
      have heSplit : e - 1 + 1 = e := by
        omega
      have hHead :
          RightTransferChain
            (e :: f :: rest)
            (1 :: t :: rest) := by
        simpa [t, heSplit, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hHeadRaw
      have hValidTail : Valid (t :: rest) := by
        intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | haRest
        · exact ht
        · exact hValid a (by simp [haRest])
      have hTail := ih t hValidTail
      have hLift := RightTransferChain.cons 1 hTail
      have hpTail : 0 < oddSteps (t :: rest) := by
        simp [oddSteps]
      have hpHTail :
          oddSteps (t :: rest) ≤ twoSteps (t :: rest) :=
        FiberPoint.oddSteps_le_twoSteps_of_valid hValidTail
      have hP :
          oddSteps (e :: f :: rest) =
            oddSteps (t :: rest) + 1 := by
        simp [oddSteps]
      have hH :
          twoSteps (e :: f :: rest) =
            twoSteps (t :: rest) + 1 := by
        dsimp [t]
        simp [twoSteps]
        omega
      have hBottom :=
        universalBottomWord_succ
          (p := oddSteps (t :: rest))
          (H := twoSteps (t :: rest))
          hpTail hpHTail
      have hTarget :
          universalBottomWord
              (oddSteps (e :: f :: rest))
              (twoSteps (e :: f :: rest)) =
            1 :: universalBottomWord
              (oddSteps (t :: rest))
              (twoSteps (t :: rest)) := by
        rw [hP, hH]
        exact hBottom
      rw [hTarget]
      exact hHead.trans hLift

/-- 任意の valid nonempty word に対する finite normalization。 -/
theorem rightTransferChain_to_universalBottom
    {w : Word}
    (hValid : Valid w)
    (hNonempty : w ≠ []) :
    RightTransferChain w
      (universalBottomWord (oddSteps w) (twoSteps w)) := by
  cases w with
  | nil => contradiction
  | cons e tail =>
      exact rightTransferChain_to_universalBottom_cons e tail hValid

/-- fixed FiberPoint 版：target は同じ `(p,H)` の universal bottom。 -/
theorem FiberPoint.rightTransferChain_to_bottom
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p) :
    RightTransferChain x.word (universalBottomWord p H) := by
  have hNonempty : x.word ≠ [] := by
    intro hNil
    have hpEq := x.oddSteps_eq
    rw [hNil] at hpEq
    simp [oddSteps] at hpEq
    omega
  have h := rightTransferChain_to_universalBottom x.valid hNonempty
  simpa [x.oddSteps_eq, x.twoSteps_eq] using h

/-! ## 3. termination / unique normal form / confluence -/

/-- right-transfer の一歩が存在するという Prop 版 relation。 -/
def CanRightTransfer (source target : Word) : Prop :=
  AdjacentRightTransfer source target

/-- right-transfer normal form。 -/
def IsRightTransferNormal (w : Word) : Prop :=
  ∀ target, ¬ CanRightTransfer w target

/-- relation の各一歩は `affineConst` を strict に下げる。 -/
theorem canRightTransfer_affineConst_lt
    {source target : Word}
    (h : CanRightTransfer source target) :
    affineConst target < affineConst source := by
  rcases h with ⟨S⟩
  exact S.affineConst_target_lt_source

/--
right-transfer は `affineConst : Word → ℕ` を strict に下げるため well-founded。
これが universal rewrite の停止性。
-/
theorem canRightTransfer_wellFounded :
    WellFounded (fun target source : Word =>
      CanRightTransfer source target) := by
  apply Subrelation.wf
    (r := (measure affineConst).rel)
  · intro target source h
    exact canRightTransfer_affineConst_lt h
  · exact (measure affineConst).wf

/-- bottom からは一歩も right-transfer できない。 -/
theorem universalBottomWord_normal
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H) :
    IsRightTransferNormal (universalBottomWord p H) := by
  intro target hStep
  rcases hStep with ⟨S⟩
  let x := universalBottomPoint p H hp hpH
  let y := S.targetPoint x
  have hB := S.affineConst_source_eq_target_add_cellWeight
  have hx := affineConst_eq_baseline_add_universalExcess_core x
  have hy := affineConst_eq_baseline_add_universalExcess_core y
  have hZero : universalExcess x = 0 := by
    simp only [universalExcess_bottom, x]
  have hPos := S.cellWeight_pos
  change affineConst x.word = affineConst y.word + S.cellWeight at hB
  rw [hx, hy, hZero] at hB
  omega

/-- valid fixed fiber では normal form は universal bottom に限る。 -/
theorem rightTransferNormal_iff_eq_universalBottom
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p)
    (hpH : p ≤ H) :
    IsRightTransferNormal x.word ↔
      x.word = universalBottomWord p H := by
  constructor
  · intro hNormal
    have C := x.rightTransferChain_to_bottom hp
    exact C.eq_of_source_normal hNormal
  · intro hEq
    rw [hEq]
    exact universalBottomWord_normal hp hpH

/--
valid fixed fiber 上の right-transfer は合流する。
任意の二経路は共通の universal bottom へさらに下降できる。
-/
theorem rightTransfer_confluent_on_fixedFiber
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p)
    {u v : Word}
    (Cu : RightTransferChain x.word u)
    (Cv : RightTransferChain x.word v) :
    ∃ z : Word,
      RightTransferChain u z ∧
        RightTransferChain v z := by
  let xu := Cu.targetPoint x
  let xv := Cv.targetPoint x
  have CuBottom :
      RightTransferChain u (universalBottomWord p H) := by
    have h := xu.rightTransferChain_to_bottom hp
    simpa [xu, RightTransferChain.targetPoint] using h
  have CvBottom :
      RightTransferChain v (universalBottomWord p H) := by
    have h := xv.rightTransferChain_to_bottom hp
    simpa [xv, RightTransferChain.targetPoint] using h
  exact
    ⟨universalBottomWord p H, CuBottom, CvBottom⟩

/-! ## 4. universal excess = affine excess -/

/--
## 4. Exact universal-excess formula

`E` は genuine affine translation から universal baseline `3^p-2^p` を引いた量と exact に一致する。
-/
theorem universalExcess_eq_affineConst_sub_baseline
    {p H : ℕ}
    (x : FiberPoint p H) :
    universalExcess x =
      affineConst x.word - (3 ^ p - 2 ^ p) := by
  have hFormula := affineConst_eq_base_add_weightedArea x
  rw [baseAffineConst_eq_threePow_sub_twoPow] at hFormula
  have hLower := affineConst_lower_bound x
  unfold universalExcess
  omega

/-- subtraction-free form：`B = baseline + E`。 -/
theorem affineConst_eq_baseline_add_universalExcess
    {p H : ℕ}
    (x : FiberPoint p H) :
    affineConst x.word =
      (3 ^ p - 2 ^ p) + universalExcess x :=
  affineConst_eq_baseline_add_universalExcess_core x

/-- `E` は自然数なので常に nonnegative。 -/
theorem universalExcess_nonneg
    {p H : ℕ}
    (x : FiberPoint p H) :
    0 ≤ universalExcess x := by
  omega

/-- FiberPoint は underlying word equality から equality が決まる。 -/
private theorem fiberPoint_eq_of_word_eq_universalNF
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hWord : x.word = y.word) :
    x = y := by
  cases x with
  | mk xw xv xp xH =>
      cases y with
      | mk yw yv yp yH =>
          dsimp at hWord
          subst yw
          rfl

/-! ## 5. zero iff bottom -/

/--
## 5. Zero characterization

`E=0` は universal bottom と同値。
-/
theorem universalExcess_eq_zero_iff_eq_bottom
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p)
    (hpH : p ≤ H) :
    universalExcess x = 0 ↔
      x = universalBottomPoint p H hp hpH := by
  constructor
  · intro hZero
    have hBottomZero :
        universalExcess (universalBottomPoint p H hp hpH) = 0 :=
      universalExcess_bottom hp hpH
    have hArea :
        universalExcess x =
          universalExcess (universalBottomPoint p H hp hpH) := by
      rw [hZero, hBottomZero]
    unfold universalExcess at hArea
    have hAffine :
        affineConst x.word =
          affineConst (universalBottomPoint p H hp hpH).word := by
      calc
        affineConst x.word =
            baseAffineConst p + weightedArea x.toFerrersShape :=
          affineConst_eq_base_add_weightedArea x
        _ = baseAffineConst p +
              weightedArea
                (universalBottomPoint p H hp hpH).toFerrersShape := by
              rw [hArea]
        _ = affineConst (universalBottomPoint p H hp hpH).word :=
          (affineConst_eq_base_add_weightedArea
            (universalBottomPoint p H hp hpH)).symm
    have hWord :=
      valid_word_unique_of_oddSteps_twoSteps_affineConst
        x.valid
        (universalBottomPoint p H hp hpH).valid
        (x.oddSteps_eq.trans
          (universalBottomPoint p H hp hpH).oddSteps_eq.symm)
        (x.twoSteps_eq.trans
          (universalBottomPoint p H hp hpH).twoSteps_eq.symm)
        hAffine
    exact fiberPoint_eq_of_word_eq_universalNF hWord
  · intro hEq
    rw [hEq]
    exact universalExcess_bottom hp hpH

/-! ## 6. lossless scalar coordinate -/

/--
## 6. Universal excess is lossless on a fixed fiber

fixed `(p,H)` では `E` 一個が FiberPoint を一意に識別する。
-/
theorem universalExcess_eq_iff
    {p H : ℕ}
    (x y : FiberPoint p H) :
    universalExcess x = universalExcess y ↔ x = y := by
  constructor
  · intro hE
    have hx := affineConst_eq_baseline_add_universalExcess x
    have hy := affineConst_eq_baseline_add_universalExcess y
    have hAffine : affineConst x.word = affineConst y.word := by
      rw [hx, hy, hE]
    have hWord :=
      valid_word_unique_of_oddSteps_twoSteps_affineConst
        x.valid y.valid
        (x.oddSteps_eq.trans y.oddSteps_eq.symm)
        (x.twoSteps_eq.trans y.twoSteps_eq.symm)
        hAffine
    exact fiberPoint_eq_of_word_eq_universalNF hWord
  · intro hEq
    subst y
    rfl

/-! ## 7. exact one-cell E loss -/

namespace AdjacentRightTransferData

/--
## 7. Exact one-cell loss

fixed FiberPoint `x` から right-transfer 一歩で `y` へ移ると、

  E(x) = E(y) + cellWeight

が exact に成り立つ。
-/
theorem universalExcess_source_eq_target_add_cellWeight
    {p H : ℕ}
    (x : FiberPoint p H)
    {target : Word}
    (S : AdjacentRightTransferData x.word target) :
    universalExcess x =
      universalExcess (S.targetPoint x) + S.cellWeight := by
  have hB := S.affineConst_source_eq_target_add_cellWeight
  have hx := affineConst_eq_baseline_add_universalExcess x
  have hy :=
    affineConst_eq_baseline_add_universalExcess (S.targetPoint x)
  change
    affineConst x.word =
      affineConst (S.targetPoint x).word + S.cellWeight at hB
  rw [hx, hy] at hB
  omega

/-- right-transfer 一歩では universal excess が strict に減る。 -/
theorem universalExcess_target_lt_source
    {p H : ℕ}
    (x : FiberPoint p H)
    {target : Word}
    (S : AdjacentRightTransferData x.word target) :
    universalExcess (S.targetPoint x) < universalExcess x := by
  have hEq := S.universalExcess_source_eq_target_add_cellWeight x
  have hPos := S.cellWeight_pos
  omega

end AdjacentRightTransferData

/-!
## まとめ

このファイルで得た universal core は `(p,H)` fixed fiber 全体で成立する。

* `(p,H)` は diagonal skeleton。
* `E` は fixed fiber 内の lossless scalar coordinate。
* adjacent right-transfer は `E` を exact cell weight だけ下げる。
* universal bottom は `E=0` の一意 normal form。

upper-triangular matrix への表現定理（項目 8）は
`RecordFerrers/Matrix/UniversalExcessRepresentation.lean` に分離する。
RecordDecomposition / Boolean boundary deletion / CSTMicro の Farey carry ledger は、
この普遍層の上に追加される finer structure として再配置できる。
-/

end RecordFerrers
end Collatz2
