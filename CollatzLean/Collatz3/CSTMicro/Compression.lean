import CollatzLean.Collatz3.CSTMicro.CriticalExpansion

/-!
# Collatz3 CSTMicro: standard parity word の exponent word への圧縮

positive odd-count を持つ standard first-passage word は先頭が必ず `true`。
その後の各 `true` から次の `true` 直前までの block length を exponent として読むことで、
positive exponent word に exact に圧縮できる。

`p = 0` の trivial even crossing は odd-only exponent word を持たないので、この bridge から分離する。
-/

namespace Collatz3
namespace CSTMicro

/--
すでに一つ `true` を読んだ block の current length `e` を持ちながら残り parity word を圧縮する。
`e > 0` の利用だけを想定する。
-/
def compressAux : ℕ → ParityWord → Word
  | e, [] => [e]
  | e, false :: v => compressAux (e + 1) v
  | e, true :: v => e :: compressAux 1 v

/--
standard parity word の圧縮。
先頭 `true` の場合だけ canonical compression を返す。
先頭 `false` は odd-only block 表現の外なので空語へ送る。
-/
def compressWord : ParityWord → Word
  | [] => []
  | false :: _ => []
  | true :: v => compressAux 1 v

/-- false の homogeneous replicate は末尾に一つ追加する形でも書ける。 -/
private theorem replicate_false_succ_append (n : ℕ) :
    List.replicate (n + 1) false =
      List.replicate n false ++ [false] := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        List.replicate (n + 1 + 1) false
            = false :: List.replicate (n + 1) false := by
                rw [List.replicate_succ]
        _ = false :: (List.replicate n false ++ [false]) := by
              rw [ih]
        _ = List.replicate (n + 1) false ++ [false] := by
              rw [List.replicate_succ]
              simp only [List.cons_append]

/-- positive block は exponent を一つ増やすと末尾に `false` が一つ増える。 -/
theorem parityBlock_succ_of_pos
    {e : ℕ}
    (he : 0 < e) :
    parityBlock (e + 1) = parityBlock e ++ [false] := by
  unfold parityBlock
  have heq : e = (e - 1) + 1 := by omega
  have hRep :
      List.replicate e false =
        List.replicate (e - 1) false ++ [false] := by
    rw [heq]
    exact replicate_false_succ_append (e - 1)
  rw [show e + 1 - 1 = e by omega]
  rw [hRep]
  simp only [List.cons_append]

/-- `compressAux` が作る exponent はすべて正。 -/
theorem compressAux_valid
    {e : ℕ}
    (he : 0 < e) :
    ∀ v : ParityWord,
      Word.Valid (compressAux e v)
  | [] => by
      intro a ha
      simp only [compressAux, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact he
  | false :: v => by
      exact compressAux_valid (e := e + 1) (by omega) v
  | true :: v => by
      have hTail := compressAux_valid (e := 1) (by decide) v
      intro a ha
      simp only [compressAux, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact he
      · exact hTail a ha

/-- unfinished block を含む compression を再展開すると元 parity suffix を exact に戻す。 -/
theorem expandWord_compressAux
    {e : ℕ}
    (he : 0 < e) :
    ∀ v : ParityWord,
      expandWord (compressAux e v) = parityBlock e ++ v
  | [] => by
      simp [compressAux]
  | false :: v => by
      rw [compressAux]
      rw [expandWord_compressAux (e := e + 1) (by omega) v]
      rw [parityBlock_succ_of_pos he]
      simp [List.append_assoc]
  | true :: v => by
      rw [compressAux]
      rw [expandWord_cons]
      rw [expandWord_compressAux (e := 1) (by decide) v]
      simp [parityBlock]

/-- 先頭 `true` の parity word は compress→expand で exact に戻る。 -/
theorem expandWord_compressWord_true
    (v : ParityWord) :
    expandWord (compressWord (true :: v)) = true :: v := by
  unfold compressWord
  rw [expandWord_compressAux (e := 1) (by decide) v]
  simp [parityBlock]

/-- 先頭 `true` の compression は valid exponent word。 -/
theorem compressWord_true_valid
    (v : ParityWord) :
    Word.Valid (compressWord (true :: v)) := by
  unfold compressWord
  exact compressAux_valid (e := 1) (by decide) v

/-- positive odd-count の first-passage path は必ず `true` から始まる。 -/
theorem FirstPassagePath.exists_tail_of_endpointOddCount_pos
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    ∃ v : ParityWord, P.word = true :: v := by
  cases hWord : P.word with
  | nil =>
      exfalso
      exact P.nonempty hWord
  | cons b tail =>
      cases b with
      | true =>
          exact ⟨tail, rfl⟩
      | false =>
          have hTailNe : tail ≠ [] := by
            intro hNil
            subst tail
            have hp0 : P.endpointOddCount = 0 := by
              unfold FirstPassagePath.endpointOddCount
              rw [hWord]
              simp
            omega
          have hLen : 1 < P.word.length := by
            rw [hWord]
            cases tail with
            | nil => contradiction
            | cons c cs => simp
          have hExp := P.proper_expanding 1 (by decide) hLen
          unfold CoefficientExpandingAt at hExp
          rw [hWord] at hExp
          simp [prefixOddCount, oddCount] at hExp

/--
positive odd-count の任意の first-passage path は、ある valid exponent word の parity 展開である。
-/
theorem FirstPassagePath.exists_valid_exponentWord
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    ∃ w : Word,
      Word.Valid w ∧
        expandWord w = P.word := by
  rcases P.exists_tail_of_endpointOddCount_pos hp with ⟨v, hWord⟩
  refine ⟨compressWord (true :: v), compressWord_true_valid v, ?_⟩
  rw [expandWord_compressWord_true]
  exact hWord.symm

/--
positive odd-count の standard first-passage path は、
valid critical exponent word に exact に圧縮できる。
-/
theorem FirstPassagePath.exists_valid_critical_exponentWord
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    ∃ w : Word,
      Word.Valid w ∧
        Word.CriticalFirstPassage w ∧
        expandWord w = P.word := by
  rcases P.exists_valid_exponentWord hp with ⟨w, hValid, hExpand⟩
  have hCritical :=
    criticalFirstPassage_of_expanded_firstPassage
      hValid P hExpand.symm
  exact ⟨w, hValid, hCritical, hExpand⟩

end CSTMicro
end Collatz3
