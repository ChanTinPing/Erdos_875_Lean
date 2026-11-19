# Third-party notices

The replay helpers below adapt Mathlib code under the [Apache License 2.0](LICENSE-APACHE).

- [ReplayCircleChar.lean](ReplayCircleChar.lean) adapts David Loeffler's `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`, copyright © 2024 David Loeffler. The replay retains the primitive complex-character declarations under distinct names.
- [ReplayLattice.lean](ReplayLattice.lean) adapts discrete-lattice lemmas from Xavier Roblot's [`Mathlib.Algebra.Module.ZLattice.Basic`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Module/ZLattice/Basic.lean), copyright © 2023 Xavier Roblot. It uses an integral change-of-basis argument.

The source and adaptation of the externally fetched Erdős #587 dependency are documented in [PUBLIC-STRUCTURE.md](../PUBLIC-STRUCTURE.md).
