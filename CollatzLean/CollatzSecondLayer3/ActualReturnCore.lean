import CollatzLean.CollatzSecondLayer3.ActualReturn.State
import CollatzLean.CollatzSecondLayer3.ActualReturn.Valuation

/-!
# compatibility shim: actual-return 旧入口

発散側 actual-return の正本は `CollatzSecondLayer3/ActualReturn/` へ移動した。
旧 `ActualReturnCore` が公開していた arithmetic / valuation / future-minimum geometry は
新しい正本モジュール経由で引き続き参照できる。

新規コードでは `CollatzLean.CollatzSecondLayer3.ActualReturn.Main` または
必要な個別モジュールを直接 import する。
-/
