# Public Lean source for the lower bound

The sharp lower bound uses a proper generalized arithmetic progression in a
fixed-cardinality layer of subset sums. The following verified declarations
connect that step to the public proof for Erdős #587.

| Role | Declaration | Source |
| --- | --- | --- |
| Extract a proper progression of positive, uniformly bounded rank from arbitrary subset sums | `Erdos587.CFP.exists_delta_dyadic_full_width` | [Pinned source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587/HooleyDyadicModel.lean) |
| Translate the upstream progression object and all required quantitative estimates | `Jsp000726.PublicStructure.dyadicSubsetStructure_from_plby` | [Adapter](upstream/Jsp000726PinnedStructure.lean) |
| Pass from the dyadic condition to an ambient interval bounded by the sixth power of the input cardinality | `Jsp000726.PublicStructure.powerSubsetStructure_of_dyadic` | [DyadicSixth.lean](Jsp000726/DyadicSixth.lean) |
| Translate subset sums of paired differences to a single fixed-cardinality layer | `Jsp000726.eventually_opposite_layer_structure` | [LowerStructuralBridge.lean](Jsp000726/LowerStructuralBridge.lean) |
| Apply the rank estimates and verify both original statements | `Jsp000726.erdos_875`, `Jsp000726.erdos_875_eventual` | [Final entry](upstream/Jsp000726Verified.lean) |

For the opposite pairs in Section 4, a subset of their positive differences
determines a fixed-size set of original indices by selecting the upper endpoint
for a chosen difference and the lower endpoint otherwise. This gives a translated
copy of the entire unrestricted subset-sum set in one cardinality layer. The
sixth-power condition follows because the number of differences is linear in the
prefix length and their ambient interval has a polynomial exponent less than six.
The proof retains the rank-one, rank-two, and higher-rank quantitative gains.

## Version and replay

The public source pin is `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
`HooleyDyadicModel.lean` has SHA-256
`26cb2d72fdc9bfe628e70f5824377dbe092c0d4c96e2e169b19566ccf9d41408`.
The upstream package uses Lean and Mathlib v4.33.0. The driver fetches the pinned
repository and [prepares the required source modules](upstream/prepare_replay.py)
for Lean and Mathlib v4.34.1. It narrows imports, splits large files, and updates
tactic or library calls where required by the toolchain. Generated modules and
build products are stored under `.lake/public-structure`.

All 138 generated upstream modules were built serially. The upstream theorem
and both original JSP endpoints were then audited with `#print axioms`. Each used
only `propext`, `Classical.choice`, and `Quot.sound`. Independently, the 81 project
modules passed `lake --wfail build`, and all 34 declarations in the project audit
listed the same three axioms.
