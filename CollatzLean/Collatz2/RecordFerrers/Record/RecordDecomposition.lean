import CollatzLean.Collatz2.RecordFerrers.Record.RecordBlock

/-!
# Record–Ferrers Phase A: record decomposition

record blocks を terminal まで連結する chain を、legacy Geometry 実装と独立に定義する。
chain index に block length list を直接持たせ、後段の skeleton / carry / permutation に使う。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
`start` から terminal `p` までを record blocks で覆う inductive chain。
空 chain は許さない。
-/
inductive RecordChain
    {p H : ℕ}
    (x : FiberPoint p H) : ℕ → List ℕ → Prop
  | last
      {start len : ℕ}
      (block : RecordBlock x start len)
      (terminal : start + len = p) :
      RecordChain x start [len]
  | cons
      {start len : ℕ}
      {rest : List ℕ}
      (block : RecordBlock x start len)
      (interior : start + len < p)
      (tail : RecordChain x (start + len) rest) :
      RecordChain x start (len :: rest)

namespace RecordChain

/-- record chain の length list は nonempty。 -/
theorem nonempty
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    lengths ≠ [] := by
  cases C <;> simp

/-- chain 内の全 block length は positive。 -/
theorem lengths_pos
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    ∀ r ∈ lengths, 0 < r := by
  induction C with
  | last B hTerminal =>
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact B.length_pos
  | cons B hInterior T ih =>
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact B.length_pos
      · exact ih r hr

/-- chain length の総和は terminal までの残り odd-step 数。 -/
theorem start_add_sum_eq_terminal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    start + lengths.sum = p := by
  induction C with
  | last B hTerminal =>
      simpa using hTerminal
  | cons B hInterior T ih =>
      simp only [List.sum_cons]
      omega


/-- start と length list だけから local block words を切り出す pure recursion。 -/
def blockWordsFromLengths
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ) : List ℕ → List Word
  | [] => []
  | len :: rest =>
      blockWord x start len ::
        blockWordsFromLengths x (start + len) rest

/-- chain が保持する local block words。proof object の elimination には依存しない。 -/
def blocks
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (_C : RecordChain x start lengths) : List Word :=
  blockWordsFromLengths x start lengths

/-- endpoint を覆う length list の block slices は元 suffix を exact に貼り直す。 -/
theorem blockWordsFromLengths_flatten_of_end
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ)
    (lengths : List ℕ)
    (hEnd : start + lengths.sum = p) :
    (blockWordsFromLengths x start lengths).flatten = x.word.drop start := by
  induction lengths generalizing start with
  | nil =>
      simp only [List.sum_nil, Nat.add_zero] at hEnd
      subst start
      have hWordLen : x.word.length = p := by
        simpa [oddSteps] using x.oddSteps_eq
      simp [blockWordsFromLengths, hWordLen]
  | cons len rest ih =>
      simp only [List.sum_cons] at hEnd
      have hTailEnd : (start + len) + rest.sum = p := by omega
      have hIH := ih (start + len) hTailEnd
      simp only [blockWordsFromLengths, List.flatten_cons]
      rw [hIH]
      unfold blockWord
      have hDrop :
          (x.word.drop start).drop len = x.word.drop (start + len) := by
        exact List.drop_drop
      rw [← hDrop]
      exact List.take_append_drop len (x.word.drop start)

/-- chain blocks を flatten すると start 以後の suffix を exact に復元する。 -/
theorem blocks_flatten_eq_drop
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    C.blocks.flatten = x.word.drop start := by
  unfold blocks
  exact blockWordsFromLengths_flatten_of_end
    x start lengths C.start_add_sum_eq_terminal

/-- endpoint 内に収まる slicing では各 block の odd length を exact に保つ。 -/
theorem blockWordsFromLengths_oddSteps
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ)
    (lengths : List ℕ)
    (hEnd : start + lengths.sum = p) :
    (blockWordsFromLengths x start lengths).map oddSteps = lengths := by
  induction lengths generalizing start with
  | nil =>
      simp [blockWordsFromLengths]
  | cons len rest ih =>
      simp only [List.sum_cons] at hEnd
      have hThisEnd : start + len ≤ p := by omega
      have hOdd : oddSteps (blockWord x start len) = len :=
        oddSteps_blockWord x hThisEnd
      have hTailEnd : (start + len) + rest.sum = p := by omega
      have hIH := ih (start + len) hTailEnd
      simp [blockWordsFromLengths, hOdd, hIH]

/-- chain block words の odd-step 数列は index の length list と一致。 -/
theorem blocks_oddSteps_eq_lengths
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    C.blocks.map oddSteps = lengths := by
  unfold blocks
  exact blockWordsFromLengths_oddSteps
    x start lengths C.start_add_sum_eq_terminal

/-- chain 内の全 local word は minimal block。 -/
theorem blocks_minimal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    ∀ b ∈ C.blocks, MinimalBlock b := by
  induction C with
  | last B hTerminal =>
      intro b hb
      simp only [blocks, blockWordsFromLengths, List.mem_singleton] at hb
      subst b
      exact B.minimal
  | cons B hInterior T ih =>
      intro b hb
      simp only [blocks, blockWordsFromLengths, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact B.minimal
      · exact ih b hb

/-- chain start は terminal 以下。 -/
theorem start_le_terminal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    start ≤ p := by
  have h := C.start_add_sum_eq_terminal
  omega


end RecordChain

/-- whole FirstCrossing word に付随する genuine record decomposition。 -/
structure RecordDecomposition
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ) where
  lengths : List ℕ
  chain : RecordChain x start lengths
  whole_firstCrossing : FirstCrossing x.word

namespace RecordDecomposition

/-- decomposition length list は nonempty。 -/
theorem lengths_nonempty
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    D.lengths ≠ [] :=
  D.chain.nonempty

/-- decomposition の全 block length は positive。 -/
theorem lengths_pos
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    ∀ r ∈ D.lengths, 0 < r :=
  D.chain.lengths_pos

/-- record lengths は exact に terminal までを覆う。 -/
theorem start_add_sum_eq_terminal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    start + D.lengths.sum = p :=
  D.chain.start_add_sum_eq_terminal

/-- start index は terminal 以下。 -/
theorem start_le_terminal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    start ≤ p :=
  D.chain.start_le_terminal


/-- decomposition の local block words。 -/
def blocks
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) : List Word :=
  D.chain.blocks

/-- decomposition blocks を flatten すると元 suffix を復元する。 -/
theorem blocks_flatten_eq_drop
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    D.blocks.flatten = x.word.drop start :=
  D.chain.blocks_flatten_eq_drop

/-- decomposition block lengths は skeleton lengths と exact に一致。 -/
theorem blocks_oddSteps_eq_lengths
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    D.blocks.map oddSteps = D.lengths :=
  D.chain.blocks_oddSteps_eq_lengths

/-- decomposition の全 local blocks は minimal。 -/
theorem blocks_minimal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    ∀ b ∈ D.blocks, MinimalBlock b :=
  D.chain.blocks_minimal

end RecordDecomposition

end RecordFerrers
end Collatz2
