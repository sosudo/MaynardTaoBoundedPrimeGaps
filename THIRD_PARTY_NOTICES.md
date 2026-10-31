# Third-party sources

The Lean source modules were adapted for Lean 4.32 from these public repositories:

- `PrimeGapsTheory`, `PrimeGapsCert`: kimihiro64/PrimeGapsLib, commit `ff4fbdcd13d9eeeba06ede80593974531dfe34b6` (original project AxiomMath/PrimeGapsLib).
- `PrimeNumberTheoremAnd`: kimihiro64/PrimeNumberTheoremAnd, commit `0f15a38c619298b5cd786d39a84dd4bb8997324c`.
- `BombieriVinogradov`: kimihiro64/bombieri-vinogradov, commit `7a1748306e026825ed6a5555516cc2f28989b2ac`.
- `Robin1984`: kimihiro64/Robin1984, commit `bfa72aec0c25c8ee29cefe4449d778ff30412bee`.

Original license texts are in `LICENSES/`. The adapted `PrimeGapsTheory/Analysis/Zeta.lean` also incorporates the Mathlib `LogDirichlet` section and compatibility lemmas, with upstream attribution retained in its header.

The source distributions are vendored as ordinary local Lake packages in
`lake-packages/`; all Lean sources and their licenses are included. The frozen
main theorem has also been checked with Lean `#print axioms`, which lists only
`propext`, `Classical.choice`, and `Quot.sound`.
