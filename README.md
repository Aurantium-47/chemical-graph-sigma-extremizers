# Extremal degree multiplicities of chemical graphs

A proof of the classification in **Conjecture 10** of Knor, Škrekovski, Filipovski and Dimitrov, *Extremizing antiregular graphs by modifying total σ-irregularity* ([arXiv:2411.01530v1](https://arxiv.org/abs/2411.01530v1); [published article](https://doi.org/10.1016/j.amc.2024.129199)).

For every connected simple graph with `n ≥ 7` vertices and maximum degree at most four, consider the sum of `|degree(u) − degree(v)|^(1/n)` over **all unordered pairs of distinct vertices**. The manuscript determines exactly which degree multiplicities maximize this quantity:

| Order | Counts of degree 1, 2, 3, 4 vertices |
|---|---|
| 4k | (k, k, k, k) |
| 4k + 1 | (k, k, k, k + 1) |
| 4k + 2 | (k, k + 1, k, k + 1), or (k + 1, k, k + 1, k) |
| 4k + 3 | (k + 1, k, k + 1, k + 1) |

The result classifies degree multiplicities, not individual graph isomorphism types. Every listed vector has a connected simple realization. The proof covers **every n ≥ 7** and does not infer the theorem from finite examples.

## Read the proof

- [Manuscript PDF](main.pdf)
- [LaTeX source](main.tex)
- [中文简述](README.zh-CN.md)
- [AI assistance and verification status](AI_USAGE.md)

[Dimitrov et al., Discrete Mathematics Letters 18 (2026), 1–7](https://doi.org/10.47443/dml.2026.041) reported the `n ≡ 0 (mod 4)` case. The proof here treats all four residue classes independently of that article's more general parameter statement. This repository does not assert that an exhaustive priority search has been completed.

## Reproduce the finite checks

Run from this directory with Python 3.8 or later; only the standard library is required:

```text
python verify.py
```

Do not use Python's `-O` option: the verifier uses assertions. It writes `verification.json` and `connected_graphs.json` in this directory. A successful run checks:

- all 317,826 multiplicity vectors satisfying the handshaking parity condition for `7 ≤ n ≤ 60`, using strict rational interval bounds with denominator `2^48`;
- all 242 maximizing degree sequences for `7 ≤ n ≤ 200`, with explicit simple connected edge lists;
- the graphicality lemma at `n = 8, 9`, its boundary behavior at `n = 7`, and the explicit seven-vertex example in the proof.

The files included here are output from an actual successful run. Runtime and Python-version metadata can differ between runs. Finite checks are supplementary; they are not a formal proof of the theorem for unbounded n.

## Build the manuscript

The source is a standalone LaTeX article with its bibliography included. With a standard TeX distribution and `latexmk`:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

This version includes a complete mathematical argument and reproducible finite checks. Proof-assistant verification and external peer review are not claimed. Research was completed with AI assistance; see [AI_USAGE.md](AI_USAGE.md).
