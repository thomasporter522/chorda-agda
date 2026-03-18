# Mechanization for Incremental Live Programming via Shortcut Memoization

This directory contains the Agda mechanization of the theorems in "Incremental Live Programming via Shortcut Memoization". To check the proofs, an installation of [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download) is required. The proofs are known to load cleanly under Agda `2.7.0.1`.

Once, installed `agda All.agda` in the top-level directory will cause Agda to check all the proofs.

## Contents

- [core.agda](./core.agda) contains definitions 2.1 - 2.5 and 2.8
- [compatibility.agda](compatibility.agda) contains Theorem 2.6 (Compatibility of Rule Composition)
- [existence.agda](./existence.agda) contains Theorem 2.7 (Shortcut Existence)
- [validity.agda](./validity.agda) contains Theorem 2.9 (Shortcut Validity)

## Postulates

The following are postulated in `core.agda`:

- Function extensionality, a standard postulate extending the core type theory of Agda. 
- `Constructor : Set`, so that the development is generic over sets of constructors. 
- `Var : Set` and a few properties, such as decidability of equality, an injection from the naturals, and a bijection between `Var` and `Var + Var`. This could have been instantiated with some concrete set, but again we wish to remain generic over infinite sets of variables. 

