/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import CARDB

/-!
# Solutions to the Challenge

The declaration of `Challenge.lean`, proved. Importing `CARDB` supplies
`card_valid_bases` and the definitions it depends on (`IsBasis`, `ValidBasis`,
`opensOf`, `minimalOpen`, `minimalBasis`), with the same names and types as in
the Challenge module. Comparator compares those declarations.

The proof development is the body of `CARDB.lean`. There is no `sorry` in that
file. The compared theorem uses `propext`, `Classical.choice` and `Quot.sound`
only.
-/
