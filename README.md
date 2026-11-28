# Informational completeness for pure quantum states

This repository contains the Lean 4 formalization accompanying the paper *Informational completeness for pure quantum states: minimality and stability* by Lukas Liehr, Daniel Omer, Ben Pineau and Mitchell A. Taylor.

The classical Pauli problem asks whether the position and momentum distributions of a quantum particle determine its wave function, i.e., whether $|\psi|^2$ and $|\mathcal{F}\psi|^2$ determine every pure state $\psi$. The answer is negative. The paper shows that position together with a single further observable does suffice. More precisely, there is a unitary operator $U$ on $L^2(\mathbb{R})$ such that the distributions $|\psi|^2$ and $|U\psi|^2$ determine $\psi$ up to a global phase, which implies a conjecture of Wright. The paper further shows that no two measurements determine the state stably, whereas five suitable measurements do, with an error bound that is uniform over all pure states. Both positive results hold on every non-atomic configuration space and are verified in Lean. They are Theorem A and Theorem B below. Theorem C is a further Lean-verified result on three measurements, which is not part of the paper.

## Verified statements

Let $(X,\mu)$ be a non-atomic measure space such that $L^2(X,\mu)$ is separable. Here $\mu$ is called non-atomic if every measurable set of positive measure is the union of two disjoint measurable sets of positive measure.

Unitary operators $U_1,\dots,U_m$ on $L^2(X,\mu)$ are called *informationally complete with respect to pure states* if all $\psi,\varphi \in L^2(X,\mu)$ with $|U_j\psi| = |U_j\varphi|$ for every $j$ satisfy $\varphi = e^{i\theta}\psi$ for some $\theta \in \mathbb{R}$. They are said to *determine pure states stably* if there exists a constant $C > 0$ such that all $\psi,\varphi \in L^2(X,\mu)$ satisfy

```math
d(\psi,\varphi) \leq C \max_{1 \leq j \leq m} \bigl\lVert \, \lvert U_j\psi \rvert - \lvert U_j\varphi \rvert \, \bigr\rVert,
```

where $d(\psi,\varphi) = \min_{\theta \in \mathbb{R}} \lVert \psi - e^{i\theta}\varphi \rVert$ denotes the distance of $\psi$ and $\varphi$ modulo global phase.

**Theorem A.** For every $\varepsilon > 0$ there exists a unitary operator $U$ on $L^2(X,\mu)$ with $\lVert U - 1 \rVert < \varepsilon$ such that the identity $1$ and $U$ are informationally complete with respect to pure states.

**Theorem B.** There exist unitary operators $U_1,\dots,U_5$ on $L^2(X,\mu)$ with $U_1 = 1$ that determine pure states stably.

**Theorem C.** There exists an orthogonal projection $P$ on $L^2(X,\mu)$ such that, for every three distinct complex numbers $\eta_1,\eta_2,\eta_3$ of modulus one, the unitary operators $U_j = 1 + (\eta_j - 1)P$ with $j = 1,2,3$ are informationally complete with respect to pure states.

Theorems A and B are the two main results of the paper. The correspondence with the Lean declarations is:

| Statement | Declaration in `Challenge.lean` |
| --- | --- |
| Theorem A | `uniqueness_from_two_measurements` |
| Theorem B | `stability_from_five_measurements` |
| Theorem C | `uniqueness_from_three_measurements` |

## Lean entry points

- [Challenge.lean](Challenge.lean): self-contained formulation of the three theorems, with all definitions needed to read them. It imports only Mathlib and uses `sorry` in place of the proofs. In this file, `Operator μ` denotes the bounded linear operators on `L²(μ)`, the expression `![1, U]` is the pair consisting of the identity and `U`, a function on `Fin m` is an `m`-tuple whose indices start at `0`, and `⨅`, `⨆` denote infimum and supremum.
- [Solution.lean](Solution.lean): the same definitions and statements as in `Challenge.lean`, with every `sorry` replaced by a proof. The three theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
- [OperatorPhaseRetrieval/MainTheorems.lean](OperatorPhaseRetrieval/MainTheorems.lean): the three theorems in the formulation of `Challenge.lean`. Theorem A is derived from [OperatorPhaseRetrieval/TwoUnitaryMain.lean](OperatorPhaseRetrieval/TwoUnitaryMain.lean), and Theorems B and C from the proof assembly in [OperatorPhaseRetrieval/SeparableAtomless.lean](OperatorPhaseRetrieval/SeparableAtomless.lean).
- [OperatorPhaseRetrieval.lean](OperatorPhaseRetrieval.lean): root module of the internal library `OperatorPhaseRetrieval`.
- [comparator.json](comparator.json): Comparator configuration pairing `Challenge.lean` and `Solution.lean`.
- [formalization.yaml](formalization.yaml): metadata for the [Palomar](https://palomar-registry.org) registry.

## Build

The project uses Lean `v4.35.0` and a pinned Mathlib commit (see `lean-toolchain` and `lake-manifest.json`). With [Lean](https://lean-lang.org/install/) installed, run the following commands.

```bash
git clone --branch palomar https://github.com/lukasliehr/Informational-Completeness.git
cd Informational-Completeness
lake exe cache get
lake build
```

The command `lake exe cache get` downloads the prebuilt Mathlib cache, and `lake build` compiles the library, `Challenge.lean` and `Solution.lean`. Building `Challenge.lean` reports three uses of `sorry`, which are the intended placeholders.
