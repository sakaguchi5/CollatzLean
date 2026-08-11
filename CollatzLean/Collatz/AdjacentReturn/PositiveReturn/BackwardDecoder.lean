import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.BidirectionalDecoder

/-!
# natural j=0 packet の一般 backward decoder

natural tail `v` の末尾 `r` 文字を一つの状態として扱う。

* `K_r` : 末尾 `r` 文字の総2進指数
* `B_r` : 末尾 `r` 文字の affine constant
* `x_(m-r)` : 末尾 `r` 文字を走る直前の actual odd value
* `t` : natural tail の canonical endpoint

とすると actual suffix run から

  `3^r * x_(m-r) + B_r = 2^K_r * t`

が exact に成立する。
さらに全 suffix contracting により、`r > 0` なら

  `3^r < 2^K_r`

である。

末尾を一文字左へ伸ばす recurrence

  `K_(r+1) = e + K_r`
  `B_(r+1) = 3^r + 2^e * B_r`

も同時に保持する。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/-- segment を `k` 文字 drop すると、開始位置を `k` 進めた残り segment になる。 -/
private theorem segment_drop_of_le
    (O : OddOrbit) {i m k : ℕ}
    (hk : k ≤ m) :
    (O.segment i m).drop k =
      O.segment (i + k) (m - k) := by
  induction k generalizing i m with
  | zero =>
      simp
  | succ k ih =>
      cases m with
      | zero =>
          omega
      | succ m =>
          have hk' : k ≤ m := by
            omega
          simp only [OddOrbit.segment_succ, List.drop_succ_cons]
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using
            ih (i := i + 1) (m := m) hk'

/-- natural tail の list length は `tailLength`。 -/
@[simp] theorem tailWord_length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.tailWord.length = D.tailLength := by
  rfl

/-- natural tail length は first-crossing terminal までの残り長。 -/
theorem tailLength_eq_sub
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.tailLength = F.length - D.cut := by
  simp [
    tailLength,
    tailWord,
    FirstCrossingData.suffixWord,
    Word.oddSteps
  ]

/-- natural tail は cut から terminal までの actual segment そのもの。 -/
theorem tailWord_eq_segment
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.tailWord =
      O.segment (R.startIndex + D.cut) D.tailLength := by
  rw [tailWord, FirstCrossingData.suffixWord, D.tailLength_eq_sub]

/-- natural tail の末尾 `r` 文字。 -/
def tailSuffixWord
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) (r : ℕ) : Collatz.Word :=
  D.tailWord.drop (D.tailLength - r)

/-- 末尾 `r` 文字の cumulative exponent `K_r`。 -/
def tailSuffixExponent
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) (r : ℕ) : ℕ :=
  Word.twoSteps (D.tailSuffixWord r)

/-- 末尾 `r` 文字の affine constant `B_r`。 -/
def tailSuffixAffine
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) (r : ℕ) : ℕ :=
  Word.affineConst (D.tailSuffixWord r)

/-- 末尾 `r` 文字を backward に見た開始 actual value `x_(m-r)`。 -/
def tailBackwardValue
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) (r : ℕ) : ℕ :=
  O.value
    (R.startIndex + D.cut + (D.tailLength - r))

/-- `r ≤ m` なら末尾 `r` 文字は対応する actual segment と一致。 -/
theorem tailSuffixWord_eq_segment
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r ≤ D.tailLength) :
    D.tailSuffixWord r =
      O.segment
        (R.startIndex + D.cut + (D.tailLength - r)) r := by
  unfold tailSuffixWord
  rw [D.tailWord_eq_segment]
  have hk : D.tailLength - r ≤ D.tailLength :=
    Nat.sub_le _ _
  have hdrop :=
    segment_drop_of_le O
      (i := R.startIndex + D.cut)
      (m := D.tailLength)
      (k := D.tailLength - r)
      hk
  rw [hdrop]
  have hlen :
      D.tailLength - (D.tailLength - r) = r := by
    omega
  rw [hlen]

/-- 末尾 `r` 文字の odd-step 数は exactly `r`。 -/
@[simp] theorem tailSuffix_oddSteps
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r ≤ D.tailLength) :
    Word.oddSteps (D.tailSuffixWord r) = r := by
  rw [D.tailSuffixWord_eq_segment hr]
  simp [Word.oddSteps]

/-- 末尾 `r` 文字は `x_(m-r)` から terminal `t` への actual run。 -/
theorem tailSuffix_runs
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r ≤ D.tailLength) :
    Word.Runs
      (D.tailSuffixWord r)
      (D.tailBackwardValue r)
      (Word.canonicalEnd D.tailWord) := by
  let k := D.tailLength - r
  have hrun :=
    O.runsSegment
      (R.startIndex + D.cut + k) r
  have hword := D.tailSuffixWord_eq_segment hr
  rw [← hword] at hrun
  have hm := D.tailLength_eq_sub
  have hcutLt := D.cut_lt
  have hidx :
      (R.startIndex + D.cut + k) + r =
        R.startIndex + F.length := by
    dsimp [k]
    omega
  have hend :
      O.value ((R.startIndex + D.cut + k) + r) =
        Word.canonicalEnd D.tailWord := by
    rw [hidx]
    change F.endpointValue = Word.canonicalEnd D.tailWord
    simpa [tailWord] using D.cutEnd_eq
  rw [hend] at hrun
  simpa [tailBackwardValue, k] using hrun

/--
一般 backward exact equation。

末尾 `r` 文字について
`3^r * x_(m-r) + B_r = 2^K_r * t`。
-/
theorem tail_suffix_exactEquation
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r ≤ D.tailLength) :
    3 ^ r * D.tailBackwardValue r + D.tailSuffixAffine r =
      2 ^ D.tailSuffixExponent r *
        Word.canonicalEnd D.tailWord := by
  have hreal := (D.tailSuffix_runs hr).realizes
  unfold Word.Realizes at hreal
  rw [D.tailSuffix_oddSteps hr] at hreal
  simpa [tailSuffixExponent, tailSuffixAffine] using hreal.symm

/--
一般 backward congruence tower。

`2^K_r * t ≡ B_r (mod 3^r)`。
-/
theorem tail_suffix_mod_threePow
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r ≤ D.tailLength) :
    (2 ^ D.tailSuffixExponent r *
        Word.canonicalEnd D.tailWord) % (3 ^ r) =
      D.tailSuffixAffine r % (3 ^ r) := by
  have hEq := D.tail_suffix_exactEquation hr
  have hmod :=
    congrArg (fun z : ℕ => z % (3 ^ r)) hEq
  calc
    (2 ^ D.tailSuffixExponent r *
        Word.canonicalEnd D.tailWord) % (3 ^ r)
        =
      (3 ^ r * D.tailBackwardValue r +
        D.tailSuffixAffine r) % (3 ^ r) := hmod.symm
    _ = D.tailSuffixAffine r % (3 ^ r) := by
      simp [Nat.add_mod]

/--
endpoint `t = 6*n + 4*d - 1` を代入した backward congruence。
-/
theorem tail_suffix_mod_threePow_arithmetic
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r ≤ D.tailLength) :
    (2 ^ D.tailSuffixExponent r *
        (6 * D.arithmeticData.n +
          4 * D.arithmeticData.d - 1)) % (3 ^ r) =
      D.tailSuffixAffine r % (3 ^ r) := by
  have hendAdd := D.arithmeticData.endpoint_add_one
  have hn := D.arithmeticData.n_pos
  have hd := D.arithmeticData.d_pos
  have hend :
      Word.canonicalEnd D.tailWord =
        6 * D.arithmeticData.n + 4 * D.arithmeticData.d - 1 := by
    omega
  simpa [hend] using D.tail_suffix_mod_threePow hr

/--
`r > 0` なら末尾 `r` 文字は contracting なので `3^r < 2^K_r`。
-/
theorem tailSuffix_threePow_lt_twoPow
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ}
    (hrPos : 0 < r)
    (hr : r ≤ D.tailLength) :
    3 ^ r < 2 ^ D.tailSuffixExponent r := by
  have hk :
      D.tailLength - r < D.tailWord.length := by
    rw [D.tailWord_length]
    omega
  have h :=
    D.tail_drop_threePow_lt_twoPow
      (k := D.tailLength - r) hk
  change
    3 ^ Word.oddSteps (D.tailSuffixWord r) <
      2 ^ Word.twoSteps (D.tailSuffixWord r) at h
  rw [D.tailSuffix_oddSteps hr] at h
  simpa [tailSuffixExponent] using h

/-- 末尾 `r+1` 文字は、一つ左の actual exponent を末尾 `r` 文字へ prepend したもの。 -/
theorem tailSuffixWord_succ
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r < D.tailLength) :
    D.tailSuffixWord (r + 1) =
      O.exponent
        (R.startIndex + D.cut +
          (D.tailLength - (r + 1))) ::
        D.tailSuffixWord r := by
  have hrSucc : r + 1 ≤ D.tailLength := by
    omega
  have hrLe : r ≤ D.tailLength := by
    omega
  have hidx :
      (R.startIndex + D.cut +
          (D.tailLength - (r + 1))) + 1 =
        R.startIndex + D.cut +
          (D.tailLength - r) := by
    omega
  rw [
    D.tailSuffixWord_eq_segment hrSucc,
    D.tailSuffixWord_eq_segment hrLe
  ]
  rw [OddOrbit.segment_succ, hidx]

/-- `K_(r+1) = e + K_r`。 -/
theorem tailSuffixExponent_succ
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r < D.tailLength) :
    D.tailSuffixExponent (r + 1) =
      O.exponent
          (R.startIndex + D.cut +
            (D.tailLength - (r + 1))) +
        D.tailSuffixExponent r := by
  rw [tailSuffixExponent, tailSuffixExponent, D.tailSuffixWord_succ hr]
  exact Word.twoSteps_cons _ _

/-- `B_(r+1) = 3^r + 2^e * B_r`。 -/
theorem tailSuffixAffine_succ
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {r : ℕ} (hr : r < D.tailLength) :
    D.tailSuffixAffine (r + 1) =
      3 ^ r +
        2 ^ O.exponent
          (R.startIndex + D.cut +
            (D.tailLength - (r + 1))) *
          D.tailSuffixAffine r := by
  have hrLe : r ≤ D.tailLength := by
    omega
  rw [tailSuffixAffine, tailSuffixAffine, D.tailSuffixWord_succ hr]
  rw [Word.affineConst_cons, D.tailSuffix_oddSteps hrLe]

end FirstCrossingData.NaturalZeroReplaySignChangeData
end PositiveReturn
end AdjacentReturn
end Collatz
