# Stable recovery from magnitudes of unitary operators

This repository contains a Lean 4 formalization accompanying the paper *Stable recovery from magnitudes of unitary operators* by Lukas Liehr, Daniel Omer, Ben Pineau and Mitchell A. Taylor. The Lean project formalizes the two main theorems of this paper, which read as follows.

Let $(X,\Sigma,\mu)$ be a non-atomic measure space such that $L^2(X,\mu)$ is separable, and let $\mathbb{T}$ denote the unit circle in the complex plane. Here $\mu$ is called non-atomic if every measurable set of positive measure can be partitioned into two measurable sets of positive measure. A family of unitary operators $U_1,\dots,U_n$ on $L^2(X,\mu)$ does phase retrieval if all $f,g \in L^2(X,\mu)$ with $|U_jf| = |U_jg|$ for every $j$ satisfy $f = cg$ for some $c \in \mathbb{T}$.

**Theorem 1.1.** There exists an orthogonal projection $P$ on $L^2(X,\mu)$ such that, for every three distinct $\eta_1,\eta_2,\eta_3 \in \mathbb{T}$, the unitary operators $U_j = I+(\eta_j-1)P$, $j = 1,2,3$, do phase retrieval.

**Theorem 1.3.** There exist five unitary operators $U_1,\dots,U_5$ on $L^2(X,\mu)$ and a constant $C > 0$ such that all $f,g \in L^2(X,\mu)$ satisfy

```math
\inf_{\omega \in \mathbb{T}} \lVert f-\omega g \rVert \leq C \cdot \max_{1 \leq j \leq 5} \bigl\lVert \, \lvert U_jf \rvert - \lvert U_jg \rvert \, \bigr\rVert.
```

The numbering of the theorems follows the paper.

## Lean entry points

- [Showcase.lean](Showcase.lean): self-contained formulation of the two theorems, with all definitions needed to read them. It imports only Mathlib and uses `sorry` in place of the proofs. In this file, `H →L[ℂ] H` denotes the bounded linear operators on `H`, a function on `Fin n` is an `n`-tuple, and `⨅`, `⨆` denote infimum and supremum.
- [Showcase_WithProofs.lean](Showcase_WithProofs.lean): the same definitions and statements as in `Showcase.lean`, with every `sorry` replaced by a proof. The two theorems `three_unitaries` and `five_unitary_stability` depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
- [OperatorPhaseRetrieval/MainTheorems.lean](OperatorPhaseRetrieval/MainTheorems.lean): the two theorems in the formulation of the showcase, derived from the proof assembly in [OperatorPhaseRetrieval/SeparableAtomless.lean](OperatorPhaseRetrieval/SeparableAtomless.lean).
- [OperatorPhaseRetrieval.lean](OperatorPhaseRetrieval.lean): root module of the internal library `OperatorPhaseRetrieval`.
- [comparator.json](comparator.json): Comparator configuration pairing the two showcase files.

## Build

The project uses Lean `v4.33.0` and a pinned Mathlib commit (see `lean-toolchain` and `lake-manifest.json`). With [Lean](https://lean-lang.org/install/) installed, run the following commands.

```bash
git clone https://github.com/lukasliehr/Operator-Phase-Retrieval.git
cd Operator-Phase-Retrieval
lake exe cache get
lake build
```

The command `lake exe cache get` downloads the prebuilt Mathlib cache, and `lake build` compiles the library and both showcase files. Building `Showcase.lean` reports two uses of `sorry`, which are the intended placeholders.
