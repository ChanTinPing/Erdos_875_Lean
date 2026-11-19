# JSP-000726 · Erdős Problem 875

A strictly increasing sequence of positive integers is admissible if finite subsets
with equal sums always have the same number of terms. The problem asks for the real
exponents `c` such that an infinite admissible sequence can satisfy
`a(n+1) - a(n) ≤ n^c` at every positive index.

The verified answer is **`[(5 + √17) / 2, ∞)`**. At the critical exponent the
construction satisfies the bound with coefficient one from the first gap onward.
The same interval is the answer under the eventual-bound convention in Formal Conjectures.

| Lean declaration | Statement |
| --- | --- |
| `Jsp000726.erdos_875` | Exact classification with the gap bound at every positive index |
| `Jsp000726.erdos_875_eventual` | Exact classification with the gap bound at all sufficiently large indices |

Both declarations are in [Jsp000726Verified.lean](upstream/Jsp000726Verified.lean) and
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Proof and attribution

The construction and optimality argument follow
[Howe, Huffman, Kohlmeyer, and Kruer, Theorem 1.1](https://hexagonmath.org/2611.00581v1).
The lower bound uses an opposite-pair translation and a published Lean progression
theorem from Erdős #587. [PUBLIC-STRUCTURE.md](PUBLIC-STRUCTURE.md) records the
source pin, adaptation, and verification. [OriginalStatement.lean](Jsp000726/OriginalStatement.lean)
checks the correspondence to the original cardinality-layer formulation and the
one-based `Nat.nth` gap in Formal Conjectures.

The Lean project is maintained by [@ChanTinPing](https://github.com/ChanTinPing).
The formalization concerns the sharp gap exponent. The paper also proves results
on term growth and joint feasibility for term and gap exponents.

## Verify

From this directory, run the following with the pinned Lean 4.34.1 toolchain and
Python 3.10 or later.

```sh
lake exe cache get
lake build
lake env python upstream/replay.py
```

The last command fetches the pinned public proof source, checks its dependency
closure one file at a time, and prints the axiom audit for both original endpoints.
Under Linux, add `--rss-limit-mib 1850` to cap the compiler's RSS during replay.

[Prize catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000726) · [Original problem](https://www.erdosproblems.com/875)
