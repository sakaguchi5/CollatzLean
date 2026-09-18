import CollatzLean.Collatz3.Mersenne.NoHoleMersenneQuotientProof

/-!
# Collatz3 Mersenne: no-hole Mersenne quotient の強い derived theorem

`NoHoleEvenMersenneQuotientResidual` の実証明は、実際には residual interface に含まれる
`k` の偶奇や `L ≥ 3` を本質的には必要としない。

既存の `large_source_shape` からそれらを復元して、外向きにはより薄い theorem

`k ≥ 4`, `n ≥ 3`, `NoHoleEquation k n 1 L` -> False

として公開する。
-/

namespace Collatz3
namespace Mersenne

/--
large-depth Mersenne quotient 型は、`k` の偶奇や `L` の下界を仮定せず排除できる。

既存の no-hole 局所算術から `L>0`, `L≥3`, `k` even を内部で復元し、
完成済み residual theorem へ渡す。
-/
theorem noHole_mersenneQuotient_largeDepth_impossible
    {k n L : ℕ}
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hEq : NoHoleEquation k n 1 L) :
    False := by
  have hkPos : 0 < k := by omega
  have hLOdd : L % 2 = 1 :=
    (hEq.mod_two_residues hkPos).2
  have hLPos : 0 < L := by omega
  rcases hEq.large_source_shape hkPos hn (by omega) hLPos with
    ⟨_hrOne, hLThree, hkEven⟩
  exact
    noHoleEvenMersenneQuotientResidual
      k n L hk hkEven hn hLThree hEq

end Mersenne
end Collatz3
