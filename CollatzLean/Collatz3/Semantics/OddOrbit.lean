import CollatzLean.Collatz3.Semantics.Runs

/-!
# Collatz3: thin infinite odd-only orbit

無限軌道の primitive data は、各時刻の値・2除算指数と、一段ごとの `OddStep` だけ。
FutureMinimum や標準選択、first-passage、Record--Ferrers はここには入れない。

有限区間を既存の `Runs` へ落とす bridge は derived theorem として与える。
-/

namespace Collatz3

/-- actual odd-only Collatz の無限軌道。 -/
structure OddOrbit where
  value : ℕ → ℕ
  exponent : ℕ → ℕ
  step : ∀ n : ℕ, OddStep (exponent n) (value n) (value (n + 1))

namespace OddOrbit

/-- 各軌道値は奇数。 -/
theorem value_odd
    (O : OddOrbit)
    (n : ℕ) :
    Odd (O.value n) :=
  (O.step n).start_odd

/-- 各 odd-only 指数は正。 -/
theorem exponent_pos
    (O : OddOrbit)
    (n : ℕ) :
    0 < O.exponent n :=
  (O.step n).exponent_pos

/-- 位置 `i` から `q` odd steps の exponent word。 -/
def segmentWord (O : OddOrbit) : ℕ → ℕ → Word
  | _i, 0 => []
  | i, q + 1 => O.exponent i :: O.segmentWord (i + 1) q

@[simp] theorem segmentWord_zero
    (O : OddOrbit)
    (i : ℕ) :
    O.segmentWord i 0 = [] :=
  rfl

@[simp] theorem segmentWord_succ
    (O : OddOrbit)
    (i q : ℕ) :
    O.segmentWord i (q + 1) =
      O.exponent i :: O.segmentWord (i + 1) q :=
  rfl

/-- segment word の odd-step 数は指定長そのもの。 -/
@[simp] theorem segmentWord_oddSteps
    (O : OddOrbit)
    (i q : ℕ) :
    Word.oddSteps (O.segmentWord i q) = q := by
  induction q generalizing i with
  | zero =>
      rfl
  | succ q ih =>
      simp [segmentWord, ih]

/-- 無限軌道の有限 segment は既存の `Runs` relation を実現する。 -/
theorem runsSegment
    (O : OddOrbit)
    (i q : ℕ) :
    Runs (O.segmentWord i q) (O.value i) (O.value (i + q)) := by
  induction q generalizing i with
  | zero =>
      simpa [segmentWord] using Runs.nil (O.value i)
  | succ q ih =>
      have hTail := ih (i := i + 1)
      have hTail' :
          Runs (O.segmentWord (i + 1) q)
            (O.value (i + 1))
            (O.value (i + (q + 1))) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail
      exact Runs.cons (O.step i) hTail'

/-- segment word は actual run 由来なので valid。 -/
theorem segmentWord_valid
    (O : OddOrbit)
    (i q : ℕ) :
    Word.Valid (O.segmentWord i q) :=
  (O.runsSegment i q).valid

end OddOrbit
end Collatz3
