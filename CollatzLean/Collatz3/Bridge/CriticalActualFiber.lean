import CollatzLean.Collatz3.Bridge.FullCriticalRestrictedPartition
import CollatzLean.Collatz3.Bridge.ValidEndpointRuns
import CollatzLean.Collatz3.Semantics.FirstPassage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Collatz3 Bridge: restricted partition と actual critical fiber

`CriticalWord m ≃ RestrictedCriticalPartition m` と、valid word に対する
canonical lift の actual realization を合成する。

固定幅 `m > 0` では各 restricted partition `P` が一意な critical word を持ち、
その actual start 全体は

`R(P) + 2^(criticalTwoDepth m + 1) * k`

という一本の算術級数になる。

さらに異なる partition の二本の fiber は交わらない。
この非交差は剰余計算を直接展開せず、actual `Runs` の有限決定性から導く。
-/

namespace Collatz3
namespace Bridge

/-- 幅 `m` の全 critical word に共通する odd-endpoint start modulus。 -/
def criticalStartModulus (m : ℕ) : ℕ :=
  2 ^ (Critical.criticalTwoDepth m + 1)

@[simp] theorem criticalStartModulus_pos (m : ℕ) :
    0 < criticalStartModulus m := by
  unfold criticalStartModulus
  exact Arithmetic.twoPow_pos _

/-- positive width の critical word は非空。 -/
theorem criticalWord_nonempty
    {m : ℕ}
    (hm : 0 < m)
    (W : Critical.CriticalWord m) :
    W.1 ≠ [] := by
  intro hNil
  have hSteps := W.2.oddSteps_eq
  rw [hNil] at hSteps
  simp [Word.oddSteps] at hSteps
  omega

/-- `CriticalWord m` は既存の pure `CriticalFirstPassage` を満たす。 -/
theorem criticalWord_criticalFirstPassage
    {m : ℕ}
    (W : Critical.CriticalWord m) :
    Word.CriticalFirstPassage W.1 := by
  constructor
  · rw [W.2.twoSteps_eq, W.2.oddSteps_eq]
  · intro k hk
    apply W.2.prefixTwoDepth_le_beatty
    rw [W.2.oddSteps_eq] at hk
    exact hk

/-- critical word の odd-endpoint modulus は固定幅 `m` だけで決まる。 -/
theorem oddEndpointModulus_eq_criticalStartModulus
    {m : ℕ}
    (W : Critical.CriticalWord m) :
    Word.oddEndpointModulus W.1 = criticalStartModulus m := by
  rw [Word.oddEndpointModulus_eq, W.2.twoSteps_eq]
  rfl

/-- critical word の canonical start は共通 modulus 未満。 -/
theorem canonicalStart_lt_criticalStartModulus
    {m : ℕ}
    (W : Critical.CriticalWord m) :
    Word.canonicalStart W.1 < criticalStartModulus m := by
  have h := Word.canonicalStart_lt_modulus W.1
  rw [oddEndpointModulus_eq_criticalStartModulus W] at h
  exact h

/-- restricted partition が完全符号する critical word。 -/
def criticalWordOfPartition
    (m : ℕ)
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    Critical.CriticalWord m :=
  (criticalWordEquivRestrictedCriticalPartition m hm).symm P

@[simp] theorem partition_criticalWordOfPartition
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    criticalWordEquivRestrictedCriticalPartition m hm
      (criticalWordOfPartition m hm P) = P := by
  exact
    (criticalWordEquivRestrictedCriticalPartition m hm).apply_symm_apply P

@[simp] theorem criticalWordOfPartition_partition
    {m : ℕ}
    (hm : 0 < m)
    (W : Critical.CriticalWord m) :
    criticalWordOfPartition m hm
      (criticalWordEquivRestrictedCriticalPartition m hm W) = W := by
  exact
    (criticalWordEquivRestrictedCriticalPartition m hm).symm_apply_apply W

/-- partition `P` の lift index `k` に対応する actual start。 -/
def liftedCriticalStart
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) : ℕ :=
  Word.canonicalStart (criticalWordOfPartition m hm P).1 +
    criticalStartModulus m * k

/-- partition `P` の lift index `k` に対応する actual endpoint。 -/
def liftedCriticalEnd
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) : ℕ :=
  Word.canonicalEnd (criticalWordOfPartition m hm P).1 +
    2 * (3 ^ m) * k

/--
restricted partition の各 lift は本当に actual run を実現する。
有限 Young shape の上に `k : ℕ` 一本の無限 fiber が乗る。
-/
theorem runs_liftedCritical
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) :
    Runs (criticalWordOfPartition m hm P).1
      (liftedCriticalStart hm P k)
      (liftedCriticalEnd hm P k) := by
  let W := criticalWordOfPartition m hm P
  have hRun :
      Runs W.1
        (Word.canonicalStart W.1 +
          Word.oddEndpointModulus W.1 * k)
        (Word.canonicalEnd W.1 +
          2 * (3 ^ Word.oddSteps W.1) * k) :=
    Runs.canonicalLift
      W.2.valid
      (criticalWord_nonempty hm W)
      k
  have hPow :
      3 ^ Word.oddSteps W.1 = 3 ^ m := by
    exact congrArg (fun n : ℕ => 3 ^ n) W.2.oddSteps_eq
  change
    Runs W.1
      (Word.canonicalStart W.1 +
        criticalStartModulus m * k)
      (Word.canonicalEnd W.1 +
        2 * (3 ^ m) * k)
  rw [← oddEndpointModulus_eq_criticalStartModulus W]
  simpa only [hPow] using hRun

/-- partition lift は actual critical first-passage でもある。 -/
theorem actualFirstPassage_liftedCritical
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) :
    ActualFirstPassage
      (criticalWordOfPartition m hm P).1
      (liftedCriticalStart hm P k)
      (liftedCriticalEnd hm P k) := by
  exact
    ⟨runs_liftedCritical hm P k,
      criticalWord_criticalFirstPassage (criticalWordOfPartition m hm P)⟩

/--
異なる partition の二本の actual fiber は、どの lift index を選んでも交わらない。

同じ start が存在すると二つの actual run は同じ幅 `m` を持つため、
`Runs.word_end_eq_of_common_start_same_oddSteps` により critical word が一致する。
word-partition equivalence の単射性から partition も一致してしまう。
-/
theorem liftedCriticalStart_eq_implies_partition_eq
    {m : ℕ}
    (hm : 0 < m)
    {P Q : RestrictedCriticalPartition m}
    {k l : ℕ}
    (hStart :
      liftedCriticalStart hm P k =
        liftedCriticalStart hm Q l) :
    P = Q := by
  let WP := criticalWordOfPartition m hm P
  let WQ := criticalWordOfPartition m hm Q
  have hRunP :
      Runs WP.1
        (liftedCriticalStart hm P k)
        (liftedCriticalEnd hm P k) := by
    simpa [WP] using runs_liftedCritical hm P k
  have hRunQ :
      Runs WQ.1
        (liftedCriticalStart hm Q l)
        (liftedCriticalEnd hm Q l) := by
    simpa [WQ] using runs_liftedCritical hm Q l
  have hRunQ' :
      Runs WQ.1
        (liftedCriticalStart hm P k)
        (liftedCriticalEnd hm Q l) := by
    rw [hStart]
    exact hRunQ
  have hSteps : Word.oddSteps WP.1 = Word.oddSteps WQ.1 := by
    rw [WP.2.oddSteps_eq, WQ.2.oddSteps_eq]
  have hWords :=
    Runs.word_end_eq_of_common_start_same_oddSteps
      hRunP hRunQ' hSteps
  have hW : WP = WQ := by
    apply Subtype.ext
    exact hWords.1
  change
    (criticalWordEquivRestrictedCriticalPartition m hm).symm P =
      (criticalWordEquivRestrictedCriticalPartition m hm).symm Q at hW
  exact
    (criticalWordEquivRestrictedCriticalPartition m hm).symm.injective hW

/-- 異なる partition の actual start fiber は pairwise disjoint。 -/
theorem liftedCriticalStart_ne_of_partition_ne
    {m : ℕ}
    (hm : 0 < m)
    {P Q : RestrictedCriticalPartition m}
    (hPQ : P ≠ Q)
    (k l : ℕ) :
    liftedCriticalStart hm P k ≠
      liftedCriticalStart hm Q l := by
  intro hStart
  exact hPQ (liftedCriticalStart_eq_implies_partition_eq hm hStart)

/-- canonical representative だけを見ても partition は一意に決まる。 -/
theorem canonicalStartOfPartition_injective
    {m : ℕ}
    (hm : 0 < m) :
    Function.Injective
      (fun P : RestrictedCriticalPartition m =>
        Word.canonicalStart (criticalWordOfPartition m hm P).1) := by
  intro P Q hStart
  apply
    liftedCriticalStart_eq_implies_partition_eq
      (m := m) hm (P := P) (Q := Q) (k := 0) (l := 0)
  simpa [liftedCriticalStart] using hStart

/--
各 partition の canonical start を共通 modulus の剰余として持つ有限座標。
-/
def canonicalCriticalResidue
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    Fin (criticalStartModulus m) :=
  ⟨Word.canonicalStart (criticalWordOfPartition m hm P).1,
    canonicalStart_lt_criticalStartModulus
      (criticalWordOfPartition m hm P)⟩

/-- canonical residue map は単射。異なる Young partition は異なる剰余類を持つ。 -/
theorem canonicalCriticalResidue_injective
    {m : ℕ}
    (hm : 0 < m) :
    Function.Injective (canonicalCriticalResidue (m := m) hm) := by
  intro P Q h
  apply canonicalStartOfPartition_injective hm
  exact congrArg Fin.val h

/--
positive width では restricted critical partition の型は有限。
共通 modulus の有限剰余集合への単射から従う。
-/
theorem restrictedCriticalPartition_finite
    (m : ℕ)
    (hm : 0 < m) :
    Finite (RestrictedCriticalPartition m) := by
  exact
    Finite.of_injective
      (canonicalCriticalResidue (m := m) hm)
      (canonicalCriticalResidue_injective (m := m) hm)

/-- 幅 `m` に存在する restricted critical partition の個数 `N_m`。 -/
noncomputable def criticalPartitionCount (m : ℕ) : ℕ :=
  Nat.card (RestrictedCriticalPartition m)

/-- 幅 `m` で実際に使われる canonical residue の集合。 -/
def criticalCanonicalResidues
    {m : ℕ}
    (hm : 0 < m) :
    Set (Fin (criticalStartModulus m)) :=
  Set.range (canonicalCriticalResidue (m := m) hm)

/--
occupied canonical residue の個数は partition 数 `N_m` と exact に一致する。
従って fixed width の有限基底の大きさをそのまま剰余類の本数として読める。
-/
theorem criticalCanonicalResidues_card_eq_partitionCount
    {m : ℕ}
    (hm : 0 < m) :
    Nat.card ↥(criticalCanonicalResidues hm) =
      criticalPartitionCount m := by
  unfold criticalCanonicalResidues criticalPartitionCount
  exact
    Nat.card_range_of_injective
      (canonicalCriticalResidue_injective (m := m) hm)

/-- partition 数は共通 modulus 以下。 -/
theorem criticalPartitionCount_le_criticalStartModulus
    {m : ℕ}
    (hm : 0 < m) :
    criticalPartitionCount m ≤ criticalStartModulus m := by
  unfold criticalPartitionCount
  calc
    Nat.card (RestrictedCriticalPartition m)
        ≤ Nat.card (Fin (criticalStartModulus m)) :=
      Nat.card_le_card_of_injective
        (canonicalCriticalResidue (m := m) hm)
        (canonicalCriticalResidue_injective (m := m) hm)
    _ = criticalStartModulus m := Nat.card_fin _

end Bridge
end Collatz3
