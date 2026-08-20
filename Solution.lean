/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import CARDB
import CARDB.SmallN
import CARDB.Asymptotics

/-!
# Solutions to the Challenge

The declarations of `Challenge.lean`, proved. Importing `CARDB`,
`CARDB.SmallN` and `CARDB.Asymptotics` supplies `card_valid_bases`,
`card_valid_bases_small`, `card_valid_bases_bounds`,
`card_valid_bases_dominated`, `card_valid_bases_asymptotic` and the
definitions they depend on
(`IsBasis`, `ValidBasis`, `opensOf`, `minimalOpen`, `minimalBasis`),
with the same names and types as in the Challenge module. Comparator
compares those declarations.

The proof development is the body of `CARDB.lean`, `CARDB/SmallN.lean`
and `CARDB/Asymptotics.lean`. There is no `sorry` in those files. The
compared theorems use `propext`, `Classical.choice` and `Quot.sound`
only.
-/
