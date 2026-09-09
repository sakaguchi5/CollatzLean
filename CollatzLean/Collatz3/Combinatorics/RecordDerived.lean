import CollatzLean.Collatz3.Combinatorics.Record


/-!
# Collatz3: generic record block の一意性

Collatz 固有の Profile / Beatty / carry を使わず、任意の整数値 rank に対する
`IsRecordBlock` だけから導く一般補題を置く。
-/

namespace Collatz3
namespace Combinatorics
namespace IsRecordBlock

/--
同じ rank・同じ start から始まる二つの strict record block は長さが一致する。
短い方の endpoint は長い方の interior になれないことだけを使う。
-/
theorem length_eq_of_same_start
    {rank : ℕ → ℤ}
    {a r s : ℕ}
    (R : IsRecordBlock rank a r)
    (S : IsRecordBlock rank a s) :
    r = s := by
  by_cases hrs : r < s
  · have hInt := S.interior R.length_pos hrs
    have hEnd := R.end_drop
    omega
  by_cases hsr : s < r
  · have hInt := R.interior S.length_pos hsr
    have hEnd := S.end_drop
    omega
  omega

end IsRecordBlock
end Combinatorics
end Collatz3
