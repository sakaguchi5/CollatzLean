import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.StrongBoundaryAClosure
import CollatzLean.Collatz2.CSTMicro.FerrersBoundarySturmian

set_option linter.style.nativeDecide false

/-!
# Boundary A finite initial range: e < 1538

`criticalHeight` は proof-oriented `Nat.find` object なので、finite evaluator には
同じ mechanical height を一 step recurrence で計算する executable copy を用いる。
それが既存 `criticalPrefixHeight` と一致することを Lean で証明した上で、
length 3..1538 の canonical boundary だけを `native_decide` する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- executable critical prefix height。 -/
def computableCriticalPrefixHeight : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      let h := computableCriticalPrefixHeight n
      if 2 ^ (n + 1) < 3 ^ h then h else h + 1


/--
executable に定義した critical prefix height は、
proof-oriented な `criticalPrefixHeight` と各 index で exact に一致する。
-/
theorem computableCriticalPrefixHeight_eq
    (n : ℕ) :
    computableCriticalPrefixHeight n =
      criticalPrefixHeight n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [computableCriticalPrefixHeight]
      rw [ih]
      by_cases hExp :
          2 ^ (n + 1) <
            3 ^ criticalPrefixHeight n
      · simp only [hExp, ↓reduceIte, criticalPrefixHeight_succ]
        have hle :
            criticalHeight (n + 1) ≤
              criticalPrefixHeight n :=
          criticalHeight_le_of_expanding hExp
        have hmono :
            criticalPrefixHeight n ≤
              criticalPrefixHeight (n + 1) :=
          criticalPrefixHeight_mono n
        have hnext :
            criticalPrefixHeight (n + 1) =
              criticalHeight (n + 1) :=
          rfl
        have hge :
            criticalPrefixHeight n ≤
              criticalHeight (n + 1) := by
          calc
            criticalPrefixHeight n
                ≤ criticalPrefixHeight (n + 1) :=
              hmono
            _ = criticalHeight (n + 1) :=
              hnext
        exact le_antisymm hge hle
      · simp only [hExp, ↓reduceIte, criticalPrefixHeight_succ]
        have hmono :
            criticalPrefixHeight n ≤
              criticalPrefixHeight (n + 1) :=
          criticalPrefixHeight_mono n
        have hstep :
            criticalPrefixHeight (n + 1) ≤
              criticalPrefixHeight n + 1 :=
          criticalPrefixHeight_succ_le n
        have hne :
            criticalPrefixHeight (n + 1) ≠
              criticalPrefixHeight n := by
          intro heq
          have hcrit :
              criticalHeight (n + 1) =
                criticalPrefixHeight n := by
            simpa using heq
          have hexp :=
            criticalHeight_expanding (n + 1)
          rw [hcrit] at hexp
          exact hExp hexp
        have hstepEq :
            criticalPrefixHeight (n + 1) =
              criticalPrefixHeight n + 1 := by
          omega
        have hnext :
            criticalPrefixHeight (n + 1) =
              criticalHeight (n + 1) :=
          rfl
        calc
          criticalPrefixHeight n + 1
              = criticalPrefixHeight (n + 1) :=
            hstepEq.symm
          _ = criticalHeight (n + 1) :=
            hnext

/-- executable critical Sturmian bit。 -/
def computableCriticalSturmianBit (i : ℕ) : Bool :=
  decide
    (computableCriticalPrefixHeight (i + 1) =
      computableCriticalPrefixHeight i + 1)

@[simp] theorem computableCriticalSturmianBit_eq
    (i : ℕ) :
    computableCriticalSturmianBit i = criticalSturmianBit i := by
  unfold computableCriticalSturmianBit criticalSturmianBit
  simp only [computableCriticalPrefixHeight_eq]

/-- executable mechanical prefix。 -/
def computableCriticalSturmianPrefix : ℕ → ParityWord
  | 0 => []
  | n + 1 =>
      computableCriticalSturmianPrefix n ++
        [computableCriticalSturmianBit n]

@[simp] theorem computableCriticalSturmianPrefix_eq
    (n : ℕ) :
    computableCriticalSturmianPrefix n = criticalSturmianPrefix n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [computableCriticalSturmianPrefix,
        criticalSturmianPrefix, ih]

/-- executable canonical critical boundary。 -/
def computableCriticalBoundaryWord : ℕ → ParityWord
  | 0 => []
  | k + 1 => computableCriticalSturmianPrefix k ++ [false]

@[simp] theorem computableCriticalBoundaryWord_eq
    (k : ℕ) :
    computableCriticalBoundaryWord k = criticalBoundaryWord k := by
  cases k with
  | zero => rfl
  | succ k =>
      simp [computableCriticalBoundaryWord, criticalBoundaryWord]

/--
critical prefix の有限確認に必要な量だけを保持する
高速な scalar state。

`twoPow   = 2^n`
`threePow = 3^m`
`affine   = B`
`residue  = prefix の canonical residue`
`endpoint = 対応する affine endpoint`
を意図する。
-/
private structure CriticalBoundaryScanState where
  twoPow : ℕ
  threePow : ℕ
  affine   : ℕ
  residue  : ℕ
  endpoint : ℕ


private def criticalBoundaryScanInitial :
    CriticalBoundaryScanState := {
  twoPow := 1
  threePow := 1
  affine := 0
  residue := 0
  endpoint := 0
}


/-- Bool を parity 0/1 に読む。 -/
private def scanBitNat : Bool → ℕ
  | false => 0
  | true  => 1


/--
次の bit `b` を実現するため、
現在の residue に `0` または `2^n` を加える。
-/
private def CriticalBoundaryScanState.liftEpsilon
    (S : CriticalBoundaryScanState)
    (b : Bool) : ℕ :=
  if S.endpoint % 2 = scanBitNat b then 0 else 1


private def CriticalBoundaryScanState.liftedResidue
    (S : CriticalBoundaryScanState)
    (b : Bool) : ℕ :=
  S.residue + S.liftEpsilon b * S.twoPow


/--
critical mechanical prefix の次 bit。

`2^(n+1) < 3^m` なら height は増えないので false、
そうでなければ true。
-/
private def CriticalBoundaryScanState.nextCriticalBit
    (S : CriticalBoundaryScanState) : Bool :=
  if 2 * S.twoPow < S.threePow then false else true


/--
critical prefix を1 stepだけ進める。

word 自体は構築せず、必要な scalar data だけを更新する。
-/
private def CriticalBoundaryScanState.next
    (S : CriticalBoundaryScanState) :
    CriticalBoundaryScanState :=
  let b := S.nextCriticalBit
  let eps := S.liftEpsilon b
  let u := S.endpoint + eps * S.threePow
  let r := S.residue + eps * S.twoPow
  match b with
  | false =>
      {
        twoPow := 2 * S.twoPow
        threePow := S.threePow
        affine := S.affine
        residue := r
        endpoint := u / 2
      }
  | true =>
      {
        twoPow := 2 * S.twoPow
        threePow := 3 * S.threePow
        affine := 3 * S.affine + S.twoPow
        residue := r
        endpoint := (3 * u + 1) / 2
      }


/--
現在の critical prefix の末尾に `false` を付けた
canonical critical boundary の residue。
-/
private def CriticalBoundaryScanState.boundaryResidue
    (S : CriticalBoundaryScanState) : ℕ :=
  S.liftedResidue false


/--
現在の prefix から得られる terminal-false boundary について、

contracting なら pure separation を直接検査し、
contracting でなければこの finite implication は自動的に真とする。
-/
private def CriticalBoundaryScanState.boundaryGood
    (S : CriticalBoundaryScanState) : Bool :=
  let terminalTwoPow := 2 * S.twoPow
  if S.threePow < terminalTwoPow then
    decide
      (S.affine <
        (terminalTwoPow - S.threePow) *
          S.boundaryResidue)
  else
    true


/--
prefix をゼロから作り直さず、一度だけ前向きに走査する。

state が prefix length `n` を表すとき、
そこで検査する boundary length は `n + 1`。
-/
private def criticalBoundaryFastScan :
    ℕ → ℕ → CriticalBoundaryScanState → Bool
  | 0, _n, _S =>
      true
  | fuel + 1, n, S =>
      let k := n + 1
      let good :=
        if 2 < k then
          S.boundaryGood
        else
          true
      good &&
        criticalBoundaryFastScan
          fuel (n + 1) S.next


private def criticalBoundaryFastCheck1538 : Bool :=
  criticalBoundaryFastScan
    1538
    0
    criticalBoundaryScanInitial

private theorem criticalBoundary_fast_computation_1538 :
    criticalBoundaryFastCheck1538 = true := by
  native_decide

/--
executable critical prefix の odd count は、
executable critical prefix height と一致する。
-/
@[simp] theorem oddCount_computableCriticalSturmianPrefix
    (n : ℕ) :
    oddCount (computableCriticalSturmianPrefix n) =
      computableCriticalPrefixHeight n := by
  rw [computableCriticalSturmianPrefix_eq]
  rw [criticalSturmianPrefix_oddCount]
  rw [← computableCriticalPrefixHeight_eq]


/--
executable critical prefix の長さは、その index `n` に一致する。
-/
@[simp] theorem computableCriticalSturmianPrefix_length
    (n : ℕ) :
    (computableCriticalSturmianPrefix n).length = n := by
  rw [computableCriticalSturmianPrefix_eq]
  exact criticalSturmianPrefix_length n


/--
末尾に `false` を追加しても odd count は変わらない。
-/
@[simp] theorem oddCount_append_false
    (v : ParityWord) :
    oddCount (v ++ [false]) = oddCount v := by
  rw [cstOddCount_append]
  simp only [oddCount, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, add_zero, Nat.add_eq_left]
  decide


/--
word の末尾に `false` を追加しても affine constant は変わらない。
-/
@[simp] theorem affineConst_append_false
    (v : ParityWord) :
    affineConst (v ++ [false]) = affineConst v := by
  induction v with
  | nil =>
      rfl
  | cons b v ih =>
      cases b
      · simp [affineConst, ih]
      · simp [affineConst, ih]

/-- 末尾に `true` を追加すると odd count は 1 増える。 -/
@[simp] theorem oddCount_append_true
    (v : ParityWord) :
    oddCount (v ++ [true]) = oddCount v + 1 := by
  rw [cstOddCount_append]
  simp [oddCount, bitNat]

/--
word の末尾に `true` を追加すると、

`B(v ++ [true]) = 3 B(v) + 2^|v|`

となる。
-/
theorem affineConst_append_true
    (v : ParityWord) :
    affineConst (v ++ [true]) =
      3 * affineConst v + 2 ^ v.length := by
  induction v with
  | nil =>
      norm_num [affineConst]
      decide
  | cons b v ih =>
      cases b
      · simp only [
          List.cons_append,
          affineConst_false_cons,
          List.length_cons
        ]
        rw [ih, pow_succ]
        ring
      · simp only [
          List.cons_append,
          affineConst_true_cons,
          List.length_cons
        ]
        rw [ih]
        rw [oddCount_append_true]
        rw [pow_succ]
        ring


/--
同じ parity cylinder の start に `t * 2^|v|` を加えると、
affine endpoint には `t * 3^m` が加わる。

scanner の 1-bit Hensel lift の基本式。
-/
theorem AffineRealizes.shift_by_parityModulus
    {v : ParityWord}
    {x y : ℕ}
    (h : AffineRealizes v x y)
    (t : ℕ) :
    AffineRealizes
      v
      (x + t * 2 ^ v.length)
      (y + t * 3 ^ oddCount v) := by
  unfold AffineRealizes at h ⊢
  calc
    2 ^ v.length *
        (y + t * 3 ^ oddCount v)
        =
      2 ^ v.length * y +
        t * 2 ^ v.length * 3 ^ oddCount v := by
          ring
    _ =
      (3 ^ oddCount v * x + affineConst v) +
        t * 2 ^ v.length * 3 ^ oddCount v := by
          rw [h]
    _ =
      3 ^ oddCount v *
          (x + t * 2 ^ v.length) +
        affineConst v := by
          ring


/--
scanner state が prefix length `n` の critical prefix を
正しく表している、という意味論的 invariant。

重要なのは、ここでは `leastRepresentative` を field にしないこと。
scanner は純粋な自然数演算だけを保持し、
canonical representative であることは affine realization と
`residue < 2^n` から後で復元する。
-/
private def CriticalBoundaryScanState.CorrectAt
    (S : CriticalBoundaryScanState)
    (n : ℕ) : Prop :=
  S.twoPow = 2 ^ n ∧
  S.threePow =
    3 ^ computableCriticalPrefixHeight n ∧
  S.affine =
    affineConst (computableCriticalSturmianPrefix n) ∧
  AffineRealizes
    (computableCriticalSturmianPrefix n)
    S.residue
    S.endpoint ∧
  S.residue < 2 ^ n


/--
初期 scanner state は empty critical prefix を正しく表す。
-/
private theorem criticalBoundaryScanInitial_correct :
    criticalBoundaryScanInitial.CorrectAt 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · decide


/--
correct scanner state の residue は、
実際にその critical prefix の least representative である。

高速 scanner 自体では ZMod を一切計算しないが、
正しさの証明では standard parity-cylinder uniqueness に戻せる。
-/
private theorem CriticalBoundaryScanState.residue_eq_leastRepresentative
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    S.residue =
      leastRepresentative
        (computableCriticalSturmianPrefix n) := by
  rcases hS with
    ⟨_hTwo, _hThree, _hAffine, hReal, hResidueLt⟩
  have hMod :=
    hReal.start_mod_eq_leastRepresentative
  have hModulus :
      parityModulus
          (computableCriticalSturmianPrefix n) =
        2 ^ n := by
    simp [parityModulus]
  rw [hModulus] at hMod
  have hSelf :
      S.residue % 2 ^ n = S.residue :=
    Nat.mod_eq_of_lt hResidueLt
  rw [hSelf] at hMod
  exact hMod

/--
`3^a` は常に奇数なので、mod 2 では 1。
scanner の parity lift で使う基本補題。
-/
private theorem three_pow_mod_two_eq_one
    (a : ℕ) :
    3 ^ a % 2 = 1 := by
  induction a with
  | zero =>
      norm_num
  | succ a ih =>
      rw [pow_succ, Nat.mul_mod, ih]

/--
correct state が保持する `threePow` は常に奇数。
-/
private theorem CriticalBoundaryScanState.threePow_mod_two_eq_one
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    S.threePow % 2 = 1 := by
  rw [hS.2.1]
  exact three_pow_mod_two_eq_one _


/--
scanner が scalar inequality だけから決める次 bit は、
executable critical Sturmian bit と exact に一致する。
-/
private theorem CriticalBoundaryScanState.nextCriticalBit_eq
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    S.nextCriticalBit =
      computableCriticalSturmianBit n := by
  rcases hS with
    ⟨hTwo, hThree, _hAffine, _hReal, _hResidueLt⟩
  by_cases hExp :
      2 ^ (n + 1) <
        3 ^ computableCriticalPrefixHeight n
  · have hScan :
        2 * S.twoPow < S.threePow := by
      rw [hTwo, hThree]
      simpa [pow_succ, Nat.mul_comm] using hExp
    simp [
      CriticalBoundaryScanState.nextCriticalBit,
      hScan,
      computableCriticalSturmianBit,
      computableCriticalPrefixHeight,
      hExp
    ]
  · have hScan :
        ¬ 2 * S.twoPow < S.threePow := by
      intro hs
      apply hExp
      rw [hTwo, hThree] at hs
      simpa [pow_succ, Nat.mul_comm] using hs
    simp [
      CriticalBoundaryScanState.nextCriticalBit,
      hScan,
      computableCriticalSturmianBit,
      computableCriticalPrefixHeight,
      hExp
    ]

/--
1-bit lift で加える係数は必ず 0 または 1。
-/
private theorem CriticalBoundaryScanState.liftEpsilon_zero_or_one
    (S : CriticalBoundaryScanState)
    (b : Bool) :
    S.liftEpsilon b = 0 ∨
      S.liftEpsilon b = 1 := by
  unfold CriticalBoundaryScanState.liftEpsilon
  split <;> simp


/--
`residue + ε 2^n` への lift に対応して
endpoint に `ε 3^m` を加えると、
その endpoint parity は指定した bit `b` に一致する。
-/
private theorem CriticalBoundaryScanState.liftedEndpoint_mod_two
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n)
    (b : Bool) :
    (S.endpoint +
        S.liftEpsilon b * S.threePow) % 2 =
      scanBitNat b := by
  have hThree :
      S.threePow % 2 = 1 :=
    S.threePow_mod_two_eq_one hS
  have hEndLt :
      S.endpoint % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  cases b with
  | false =>
      simp only [scanBitNat]
      by_cases h0 :
          S.endpoint % 2 = 0
      · simp [
          CriticalBoundaryScanState.liftEpsilon,
          scanBitNat,
          h0
        ]
      · have h1 :
            S.endpoint % 2 = 1 := by
          omega
        simp [
          CriticalBoundaryScanState.liftEpsilon,
          scanBitNat,
          h1,
          hThree,
          Nat.add_mod,
        ]
  | true =>
      simp only [scanBitNat]
      by_cases h1 :
          S.endpoint % 2 = 1
      · simp [
          CriticalBoundaryScanState.liftEpsilon,
          scanBitNat,
          h1
        ]
      · have h0 :
            S.endpoint % 2 = 0 := by
          omega
        simp [
          CriticalBoundaryScanState.liftEpsilon,
          scanBitNat,
          h0,
          hThree,
          Nat.add_mod,
        ]

/--
affine endpoint が偶数なら、
末尾に `false` を追加して endpoint を 2 で割れる。
-/
private theorem AffineRealizes.append_false_of_even_endpoint
    {v : ParityWord}
    {x y : ℕ}
    (h : AffineRealizes v x y)
    (hy : y % 2 = 0) :
    AffineRealizes
      (v ++ [false])
      x
      (y / 2) := by
  have hDiv0 :=
    Nat.mod_add_div y 2
  have hHalf :
      2 * (y / 2) = y := by
    rw [hy] at hDiv0
    omega
  unfold AffineRealizes at h ⊢
  rw [
    affineConst_append_false,
    oddCount_append_false
  ]
  simp only [
    List.length_append,
    List.length_singleton
  ]
  rw [pow_succ]
  calc
    (2 ^ v.length * 2) * (y / 2)
        =
      2 ^ v.length * (2 * (y / 2)) := by
        ring
    _ = 2 ^ v.length * y := by
      rw [hHalf]
    _ =
      3 ^ oddCount v * x +
        affineConst v := h


/--
affine endpoint が奇数なら、
末尾に `true` を追加して `(3y+1)/2` へ進める。
-/
private theorem AffineRealizes.append_true_of_odd_endpoint
    {v : ParityWord}
    {x y : ℕ}
    (h : AffineRealizes v x y)
    (hy : y % 2 = 1) :
    AffineRealizes
      (v ++ [true])
      x
      ((3 * y + 1) / 2) := by
  have hEven :
      (3 * y + 1) % 2 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [hy]
  have hDiv0 :=
    Nat.mod_add_div (3 * y + 1) 2
  have hHalf :
      2 * ((3 * y + 1) / 2) =
        3 * y + 1 := by
    rw [hEven] at hDiv0
    omega
  unfold AffineRealizes at h ⊢
  rw [
    affineConst_append_true,
    oddCount_append_true
  ]
  simp only [
    List.length_append,
    List.length_singleton
  ]
  simp only [pow_succ]
  calc
    (2 ^ v.length * 2) *
          ((3 * y + 1) / 2)
        =
      2 ^ v.length *
        (2 * ((3 * y + 1) / 2)) := by
          ring
    _ =
      2 ^ v.length * (3 * y + 1) := by
        rw [hHalf]
    _ =
      3 * (2 ^ v.length * y) +
        2 ^ v.length := by
          ring
    _ =
      3 *
          (3 ^ oddCount v * x +
            affineConst v) +
        2 ^ v.length := by
          rw [h]
    _ =
      (3 ^ oddCount v * 3) * x +
        (3 * affineConst v +
          2 ^ v.length) := by
            ring

/--
correct state を1 step進めると、
次の critical prefix を表す correct state になる。

proof-oriented な word の再計算はここで一度だけ行い、
executable scanner 自体は scalar recurrence のまま保つ。
-/
private theorem CriticalBoundaryScanState.next_correct
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    S.next.CorrectAt (n + 1) := by
  have hCorrect := hS
  rcases hS with
    ⟨hTwo, hThree, hAffine, hReal, hResidueLt⟩
  have hBitEq :
      S.nextCriticalBit =
        computableCriticalSturmianBit n :=
    S.nextCriticalBit_eq hCorrect
  cases hBit : S.nextCriticalBit with
  | false =>
      /-
      false branch:
      `2^(n+1) < 3^m` なので critical height は増えない。
      -/
      have hScan :
          2 * S.twoPow < S.threePow := by
        by_contra hnot
        have :
            S.nextCriticalBit = true := by
          simp [
            CriticalBoundaryScanState.nextCriticalBit,
            hnot
          ]
        rw [hBit] at this
        contradiction
      have hExp :
          2 ^ (n + 1) <
            3 ^ computableCriticalPrefixHeight n := by
        rw [hTwo, hThree] at hScan
        simpa [pow_succ, Nat.mul_comm] using hScan
      have hHeightStep :
          computableCriticalPrefixHeight (n + 1) =
            computableCriticalPrefixHeight n := by
        simp [
          computableCriticalPrefixHeight,
          hExp
        ]
      have hCompBit :
          computableCriticalSturmianBit n = false := by
        calc
          computableCriticalSturmianBit n
              = S.nextCriticalBit := hBitEq.symm
          _ = false := hBit
      have hPrefixStep :
          computableCriticalSturmianPrefix (n + 1) =
            computableCriticalSturmianPrefix n ++ [false] := by
        change
          computableCriticalSturmianPrefix n ++
              [computableCriticalSturmianBit n] =
            computableCriticalSturmianPrefix n ++ [false]
        rw [hCompBit]
      /-
      現在の residue を同じ parity cylinder 内で
      0 または `2^n` だけ lift する。
      -/
      have hLiftReal :
          AffineRealizes
            (computableCriticalSturmianPrefix n)
            (S.residue +
              S.liftEpsilon false * S.twoPow)
            (S.endpoint +
              S.liftEpsilon false * S.threePow) := by
        have h :=
          AffineRealizes.shift_by_parityModulus
            hReal
            (S.liftEpsilon false)
        rw [
          computableCriticalSturmianPrefix_length,
          oddCount_computableCriticalSturmianPrefix
        ] at h
        rw [← hTwo, ← hThree] at h
        exact h
      have hParity :
          (S.endpoint +
              S.liftEpsilon false * S.threePow) % 2 = 0 := by
        simpa [scanBitNat] using
          S.liftedEndpoint_mod_two hCorrect false
      have hNextReal :
          AffineRealizes
            (computableCriticalSturmianPrefix (n + 1))
            (S.residue +
              S.liftEpsilon false * S.twoPow)
            ((S.endpoint +
                S.liftEpsilon false * S.threePow) / 2) := by
        have h :=
          AffineRealizes.append_false_of_even_endpoint
            hLiftReal hParity
        rw [← hPrefixStep] at h
        exact h
      have hResidueNext :
          S.residue +
              S.liftEpsilon false * S.twoPow <
            2 ^ (n + 1) := by
        rcases
          S.liftEpsilon_zero_or_one false with
          hEps | hEps
        · rw [hEps]
          simp only [zero_mul, add_zero]
          exact lt_trans hResidueLt
            (by
              rw [pow_succ]
              have hpow :
                  0 < 2 ^ n := by
                positivity
              omega)
        · rw [hEps, one_mul, hTwo, pow_succ]
          have hpow :
              0 < 2 ^ n := by
            positivity
          omega
      unfold CriticalBoundaryScanState.CorrectAt
      simp only [
        CriticalBoundaryScanState.next,
        hBit
      ]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hTwo, pow_succ]
        omega
      · rw [hThree, hHeightStep]
      · rw [hPrefixStep, affineConst_append_false]
        exact hAffine
      · exact hNextReal
      · exact hResidueNext
  | true =>
      /-
      true branch:
      `2^(n+1) < 3^m` ではないので critical height は1増える。
      -/
      have hScan :
          ¬ 2 * S.twoPow < S.threePow := by
        intro hs
        have :
            S.nextCriticalBit = false := by
          simp [
            CriticalBoundaryScanState.nextCriticalBit,
            hs
          ]
        rw [hBit] at this
        contradiction
      have hNoExp :
          ¬ 2 ^ (n + 1) <
            3 ^ computableCriticalPrefixHeight n := by
        intro hexp
        apply hScan
        rw [hTwo, hThree]
        simpa [pow_succ, Nat.mul_comm] using hexp
      have hHeightStep :
          computableCriticalPrefixHeight (n + 1) =
            computableCriticalPrefixHeight n + 1 := by
        simp [
          computableCriticalPrefixHeight,
          hNoExp
        ]
      have hCompBit :
          computableCriticalSturmianBit n = true := by
        calc
          computableCriticalSturmianBit n
              = S.nextCriticalBit := hBitEq.symm
          _ = true := hBit
      have hPrefixStep :
          computableCriticalSturmianPrefix (n + 1) =
            computableCriticalSturmianPrefix n ++ [true] := by
        change
          computableCriticalSturmianPrefix n ++
              [computableCriticalSturmianBit n] =
            computableCriticalSturmianPrefix n ++ [true]
        rw [hCompBit]
      have hLiftReal :
          AffineRealizes
            (computableCriticalSturmianPrefix n)
            (S.residue +
              S.liftEpsilon true * S.twoPow)
            (S.endpoint +
              S.liftEpsilon true * S.threePow) := by
        have h :=
          AffineRealizes.shift_by_parityModulus
            hReal
            (S.liftEpsilon true)
        rw [
          computableCriticalSturmianPrefix_length,
          oddCount_computableCriticalSturmianPrefix
        ] at h
        rw [← hTwo, ← hThree] at h
        exact h
      have hParity :
          (S.endpoint +
              S.liftEpsilon true * S.threePow) % 2 = 1 := by
        simpa [scanBitNat] using
          S.liftedEndpoint_mod_two hCorrect true
      have hNextReal :
          AffineRealizes
            (computableCriticalSturmianPrefix (n + 1))
            (S.residue +
              S.liftEpsilon true * S.twoPow)
            ((3 *
                (S.endpoint +
                  S.liftEpsilon true * S.threePow) +
                1) / 2) := by
        have h :=
          AffineRealizes.append_true_of_odd_endpoint
            hLiftReal hParity
        rw [← hPrefixStep] at h
        exact h
      have hResidueNext :
          S.residue +
              S.liftEpsilon true * S.twoPow <
            2 ^ (n + 1) := by
        rcases
          S.liftEpsilon_zero_or_one true with
          hEps | hEps
        · rw [hEps]
          simp only [zero_mul, add_zero]
          exact lt_trans hResidueLt
            (by
              rw [pow_succ]
              have hpow :
                  0 < 2 ^ n := by
                positivity
              omega)
        · rw [hEps, one_mul, hTwo, pow_succ]
          have hpow :
              0 < 2 ^ n := by
            positivity
          omega
      unfold CriticalBoundaryScanState.CorrectAt
      simp only [
        CriticalBoundaryScanState.next,
        hBit
      ]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hTwo, pow_succ]
        omega
      · rw [hHeightStep, hThree, pow_succ]
        ring
      · rw [
          hPrefixStep,
          affineConst_append_true,
          hAffine,
          computableCriticalSturmianPrefix_length,
          hTwo
        ]
      · exact hNextReal
      · exact hResidueNext


/--
affine realization の start が standard modulus 未満なら、
その start 自身が canonical least representative である。
-/
private theorem AffineRealizes.start_eq_leastRepresentative_of_lt
    {v : ParityWord}
    {x y : ℕ}
    (h : AffineRealizes v x y)
    (hx : x < 2 ^ v.length) :
    x = leastRepresentative v := by
  have hMod :=
    h.start_mod_eq_leastRepresentative
  have hModulus :
      parityModulus v = 2 ^ v.length := by
    rfl
  rw [hModulus] at hMod
  have hSelf :
      x % 2 ^ v.length = x :=
    Nat.mod_eq_of_lt hx
  rw [hSelf] at hMod
  exact hMod


/--
correct state の terminal-false lift は、
次 modulus `2^(n+1)` の標準範囲内にある。
-/
private theorem CriticalBoundaryScanState.boundaryResidue_lt
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    S.boundaryResidue < 2 ^ (n + 1) := by
  rcases hS with
    ⟨hTwo, _hThree, _hAffine, _hReal, hResidueLt⟩
  rcases S.liftEpsilon_zero_or_one false with
    hEps | hEps
  · simp only [
      CriticalBoundaryScanState.boundaryResidue,
      CriticalBoundaryScanState.liftedResidue
    ]
    rw [hEps]
    simp only [zero_mul, Nat.add_zero]
    rw [pow_succ]
    have hpow :
        0 < 2 ^ n := by
      positivity
    omega
  · simp only [
      CriticalBoundaryScanState.boundaryResidue,
      CriticalBoundaryScanState.liftedResidue
    ]
    rw [hEps, one_mul, hTwo, pow_succ]
    have hpow :
        0 < 2 ^ n := by
      positivity
    omega


/--
correct prefix state の terminal-false lift は、
実際に canonical critical boundary の affine realization を与える。
-/
private theorem CriticalBoundaryScanState.boundaryAffineRealizes
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    AffineRealizes
      (computableCriticalBoundaryWord (n + 1))
      S.boundaryResidue
      ((S.endpoint +
          S.liftEpsilon false * S.threePow) / 2) := by
  have hCorrect := hS
  rcases hS with
    ⟨hTwo, hThree, _hAffine, hReal, _hResidueLt⟩
  have hLift :
      AffineRealizes
        (computableCriticalSturmianPrefix n)
        (S.residue +
          S.liftEpsilon false * S.twoPow)
        (S.endpoint +
          S.liftEpsilon false * S.threePow) := by
    have h :=
      AffineRealizes.shift_by_parityModulus
        hReal
        (S.liftEpsilon false)
    rw [
      computableCriticalSturmianPrefix_length,
      oddCount_computableCriticalSturmianPrefix
    ] at h
    rw [← hTwo, ← hThree] at h
    exact h
  have hParity :
      (S.endpoint +
          S.liftEpsilon false * S.threePow) % 2 = 0 := by
    simpa [scanBitNat] using
      S.liftedEndpoint_mod_two hCorrect false
  have hBoundary :=
    AffineRealizes.append_false_of_even_endpoint
      hLift hParity
  simpa only [
    computableCriticalBoundaryWord,
    CriticalBoundaryScanState.boundaryResidue,
    CriticalBoundaryScanState.liftedResidue
  ] using hBoundary


/--
fast scanner の `boundaryResidue` は、
proof-oriented な canonical critical boundary の
`leastRepresentative` と exact に一致する。
-/
private theorem
    CriticalBoundaryScanState.boundaryResidue_eq_leastRepresentative
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    S.boundaryResidue =
      leastRepresentative
        (computableCriticalBoundaryWord (n + 1)) := by
  apply
    AffineRealizes.start_eq_leastRepresentative_of_lt
      (S.boundaryAffineRealizes hS)
  simpa only [
    computableCriticalBoundaryWord,
    List.length_append,
    List.length_singleton,
    computableCriticalSturmianPrefix_length,
    Nat.add_comm
  ] using S.boundaryResidue_lt hS

/--
initial state から `n` step 前向きに走査した state。
-/
private def criticalBoundaryScanStateAt :
    ℕ → CriticalBoundaryScanState
  | 0 =>
      criticalBoundaryScanInitial
  | n + 1 =>
      (criticalBoundaryScanStateAt n).next


/--
`n` step 後の scanner state は、
length `n` の executable critical prefix を正しく表す。
-/
private theorem criticalBoundaryScanStateAt_correct
    (n : ℕ) :
    (criticalBoundaryScanStateAt n).CorrectAt n := by
  induction n with
  | zero =>
      exact criticalBoundaryScanInitial_correct
  | succ n ih =>
      exact
        CriticalBoundaryScanState.next_correct ih

/--
correct state の scalar data を
terminal-false critical boundary の quantity に読み替える。
-/
private theorem CriticalBoundaryScanState.boundary_data
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n) :
    (computableCriticalBoundaryWord (n + 1)).length = n + 1 ∧
    oddCount (computableCriticalBoundaryWord (n + 1)) =
      computableCriticalPrefixHeight n ∧
    affineConst (computableCriticalBoundaryWord (n + 1)) =
      S.affine ∧
    leastRepresentative
        (computableCriticalBoundaryWord (n + 1)) =
      S.boundaryResidue := by
  rcases hS with
    ⟨_hTwo, _hThree, hAffine, _hReal, _hResidueLt⟩
  constructor
  · simp [computableCriticalBoundaryWord]
  constructor
  · change
      oddCount
          (computableCriticalSturmianPrefix n ++ [false]) =
        computableCriticalPrefixHeight n
    rw [
      oddCount_append_false,
      oddCount_computableCriticalSturmianPrefix
    ]
  constructor
  · rw [
      computableCriticalBoundaryWord,
      affineConst_append_false
    ]
    exact hAffine.symm
  · exact
      (S.boundaryResidue_eq_leastRepresentative
        ⟨_hTwo, _hThree, hAffine, _hReal, _hResidueLt⟩).symm


/--
`boundaryGood = true` であり、その boundary が contracting なら、
実際の `WordPureSeparation` が成立する。

ここで executable scalar check と proof-oriented predicate が接続される。
-/
private theorem CriticalBoundaryScanState.boundaryGood_sound
    {S : CriticalBoundaryScanState}
    {n : ℕ}
    (hS : S.CorrectAt n)
    (hGood : S.boundaryGood = true)
    (hContract :
      CoefficientContracting
        (computableCriticalBoundaryWord (n + 1))) :
    WordPureSeparation
      (computableCriticalBoundaryWord (n + 1)) := by
  have hData := S.boundary_data hS
  rcases hS with
    ⟨hTwo, hThree, hAffine, _hReal, _hResidueLt⟩
  rcases hData with
    ⟨hLength, hOdd, hAffineBoundary, hLeast⟩
  have hContractScalar :
      S.threePow < 2 * S.twoPow := by
    unfold CoefficientContracting at hContract
    rw [hLength, hOdd] at hContract
    rw [hThree, hTwo]
    simpa [pow_succ, Nat.mul_comm] using hContract
  have hSepScalar :
      S.affine <
        (2 * S.twoPow - S.threePow) *
          S.boundaryResidue := by
    have hDec :
        decide
          (S.affine <
            (2 * S.twoPow - S.threePow) *
              S.boundaryResidue) = true := by
      simpa [
        CriticalBoundaryScanState.boundaryGood,
        hContractScalar
      ] using hGood
    exact of_decide_eq_true hDec
  unfold WordPureSeparation
  unfold wordTerminalGap
  rw [
    hLength,
    hOdd,
    hAffineBoundary,
    hLeast
  ]
  rw [hTwo, hThree] at hSepScalar
  simpa [pow_succ, Nat.mul_comm] using hSepScalar

/--
1 step 以上の fast scan が成功したなら、
現在位置の check と残りの scan はともに成功している。
-/
private theorem criticalBoundaryFastScan_succ_true
    (fuel n : ℕ)
    (S : CriticalBoundaryScanState)
    (h :
      criticalBoundaryFastScan (fuel + 1) n S = true) :
    (if 2 < n + 1 then S.boundaryGood else true) = true ∧
    criticalBoundaryFastScan fuel (n + 1) S.next = true := by
  simpa [criticalBoundaryFastScan] using h

/--
fast scan が成功している区間内では、
terminal contracting な canonical critical boundary は
すべて pure separation を満たす。
-/
private theorem criticalBoundaryFastScan_sound :
    ∀ fuel n : ℕ,
      ∀ S : CriticalBoundaryScanState,
        S.CorrectAt n →
        criticalBoundaryFastScan fuel n S = true →
        ∀ k : ℕ,
          n < k →
          k ≤ n + fuel →
          2 < k →
          CoefficientContracting
            (computableCriticalBoundaryWord k) →
          WordPureSeparation
            (computableCriticalBoundaryWord k) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n S _hS _hScan k hnk hk
      omega
  | succ fuel ih =>
      intro n S hS hScan k hnk hk hNontrivial hContract
      have hSplit :=
        criticalBoundaryFastScan_succ_true
          fuel n S hScan
      rcases hSplit with
        ⟨hHead, hTail⟩
      by_cases hkHead :
          k = n + 1
      · /-
        現在の state が直接検査している boundary。
        -/
        subst k
        have hGood :
            S.boundaryGood = true := by
          simpa [hNontrivial] using hHead
        exact
          CriticalBoundaryScanState.boundaryGood_sound
            hS
            hGood
            hContract
      · /-
        現在位置より後ろなら、next state から始まる
        tail scan に帰納法を適用する。
        -/
        have hnkNext :
            n + 1 < k := by
          omega
        have hkTail :
            k ≤ (n + 1) + fuel := by
          omega
        have hNextCorrect :
            S.next.CorrectAt (n + 1) :=
          CriticalBoundaryScanState.next_correct hS
        exact
          ih
            (n + 1)
            S.next
            hNextCorrect
            hTail
            k
            hnkNext
            hkTail
            hNontrivial
            hContract

/--
canonical critical word が terminal contracting である有限 length について、
高速 scalar scan の verified result から pure separation を得る。
-/
private theorem criticalBoundary_finite_check_1538 :
    ∀ k : Fin 1539,
      2 < k.1 →
      CoefficientContracting
        (computableCriticalBoundaryWord k.1) →
      WordPureSeparation
        (computableCriticalBoundaryWord k.1) := by
  intro k hNontrivial hContract
  have hScan :
      criticalBoundaryFastScan
          1538
          0
          criticalBoundaryScanInitial =
        true := by
    exact criticalBoundary_fast_computation_1538
  have hkPos :
      0 < k.1 := by
    omega
  have hkUpper :
      k.1 ≤ 0 + 1538 := by
    have hkLt :
        k.1 < 1539 :=
      k.isLt
    omega
  exact
    criticalBoundaryFastScan_sound
      1538
      0
      criticalBoundaryScanInitial
      criticalBoundaryScanInitial_correct
      hScan
      k.1
      hkPos
      hkUpper
      hNontrivial
      hContract

/-- Existing final closure theorem が要求する finite side。 -/
theorem actualBoundaryFiniteCheck1538
    {L : LopezStollInstantiation}
    (hFirst : strongFirstPrecision L = 1538) :
    ∀ v : ParityWord,
      IsFerrersBoundary v →
      2 < v.length →
      v.length - 1 < strongFirstPrecision L →
      WordPureSeparation v := by
  intro v hBoundary hNontrivial hSmall
  have hEq :
      v = criticalBoundaryWord v.length :=
    ferrersBoundary_eq_criticalBoundaryWord hBoundary
  have hlt1539 :
      v.length < 1539 := by
    rw [hFirst] at hSmall
    omega
  let k : Fin 1539 :=
    ⟨v.length, hlt1539⟩
  have hContract :
      CoefficientContracting v :=
    hBoundary.1.2.2
  have hContractExec :
      CoefficientContracting
        (computableCriticalBoundaryWord k.1) := by
    dsimp [k]
    rw [computableCriticalBoundaryWord_eq]
    rw [← hEq]
    exact hContract
  have hSep :
      WordPureSeparation
        (computableCriticalBoundaryWord k.1) :=
    criticalBoundary_finite_check_1538
      k
      (by
        dsimp [k]
        exact hNontrivial)
      hContractExec
  dsimp [k] at hSep
  rw [computableCriticalBoundaryWord_eq] at hSep
  rw [hEq]
  exact hSep

end ExternalArithmetic
end CSTMicro
end Collatz2
