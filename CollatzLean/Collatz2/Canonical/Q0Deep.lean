import CollatzLean.Collatz2.Local.ContractingClosure
import CollatzLean.Collatz2.Canonical.EndpointFundamentalBound
import CollatzLean.Collatz2.Canonical.PositiveSuffixBudget
import CollatzLean.Collatz2.Canonical.ZeroCoreSlack

/-!
# Collatz2 Canonical: q=0 deep reduction bundle

q=0 canonical-positive FirstCrossing のさらに先で使う、
現時点で独立に証明できる canonical arithmetic をまとめて import する。

* endpoint fundamental bound `canonicalEnd < 2*3^p`
* FirstCrossing 非依存の canonical-positive / all-suffix-contracting budget
* true zero-core coordinate から得る start/end fundamental slack

future-minimum minimalization や sharp suffix-budget lower bound は、
対応する source packet が確定してから別層で接続する。
-/
