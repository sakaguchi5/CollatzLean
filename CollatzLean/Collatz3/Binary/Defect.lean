import CollatzLean.Collatz3.Binary.AlternatingWeight


/-!
# Collatz3 Binary: binary zero defect

固定長二進語に含まれる `0` の個数を binary defect として扱う。

この層では defect を軌道成長や Mersenne block と結び付けない。
`AlternatingWeight` と同じ binary representation 上の組合せ恒等式だけを証明する。
-/

namespace Collatz3
namespace Binary

/-- LSB-first binary word に含まれる `0` の個数。 -/
def zeroCount : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 0 else 1) + zeroCount bs

@[simp] theorem zeroCount_nil : zeroCount [] = 0 := rfl
@[simp] theorem zeroCount_cons_true (bs : List Bool) :
    zeroCount (true :: bs) = zeroCount bs := by
  simp [zeroCount]

@[simp] theorem zeroCount_cons_false (bs : List Bool) :
    zeroCount (false :: bs) = zeroCount bs + 1 := by
  simp [zeroCount, Nat.add_comm]

/-- zero count は append に関して加法的。 -/
theorem zeroCount_append (u v : List Bool) :
    zeroCount (u ++ v) = zeroCount u + zeroCount v := by
  induction u with
  | nil => simp
  | cons b u ih =>
      cases b <;> simp [zeroCount, ih, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem zeroCount_replicate_true (m : ℕ) :
    zeroCount (List.replicate m true) = 0 := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

@[simp] theorem zeroCount_replicate_false (m : ℕ) :
    zeroCount (List.replicate m false) = m := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

/--
各位置は `0` か、偶数位置の `1` か、奇数位置の `1` のちょうど一つに数えられる。
-/
theorem zeroCount_add_alternatingWeight_eq_length
    (bits : List Bool) :
    zeroCount bits + evenOneCount bits + oddOneCount bits = bits.length := by
  induction bits with
  | nil => simp
  | cons b bs ih =>
      cases b <;>
        simp [zeroCount, evenOneCount, oddOneCount] at ih ⊢ <;>
        omega

/-- 自然数 `x` が長さ `length` の表現で zero defect `defect` を持つ。 -/
def HasZeroDefect
    (x defect length : ℕ) : Prop :=
  ∃ bits : List Bool,
    RepresentsAtLength bits x length ∧
      zeroCount bits = defect

namespace HasZeroDefect

/-- 具体的 representation から zero defect を得る。 -/
theorem of_representation
    {bits : List Bool} {x length : ℕ}
    (h : RepresentsAtLength bits x length) :
    HasZeroDefect x (zeroCount bits) length := by
  exact ⟨bits, h, rfl⟩

end HasZeroDefect

/--
alternating weight が分かれば、同じ representation 上の zero defect は
`length - evenWeight - oddWeight` になる。
-/
theorem HasAlternatingWeight.hasZeroDefect
    {x evenWeight oddWeight length : ℕ}
    (h : HasAlternatingWeight x evenWeight oddWeight length) :
    HasZeroDefect
      x (length - evenWeight - oddWeight) length := by
  rcases h with ⟨bits, hRep, hEven, hOdd⟩
  refine ⟨bits, hRep, ?_⟩
  have hCount :=
    zeroCount_add_alternatingWeight_eq_length bits
  rw [hEven, hOdd, hRep.length] at hCount
  omega

end Binary
end Collatz3
