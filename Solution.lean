module

public import Freezing2

/-!
# Solution for the statement interface

The theorems compared with `Challenge.lean` are proved in the library module
`Freezing2.Interface.Statements`, with the same fully qualified names
(namespace `FreezingStatements`) and the same statements. Their definitions
come from `Freezing2.Interface.Defs`, of which `Challenge.lean` contains a
verbatim copy. The selected results and the permitted axioms are listed in
`comparator.json`; the encoding is explained in `docs/statement-interface.md`.
This module does not import `Challenge`: the two declaration environments are
compared separately.
-/
