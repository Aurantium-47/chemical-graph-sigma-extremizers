# Lean formalization of Conjecture 10

The Lean supplement proves the degree-multiplicity classification in Conjecture 10 of Knor, Škrekovski, Filipovski and Dimitrov, *Extremizing antiregular graphs by modifying total σ-irregularity* ([arXiv:2411.01530v1](https://arxiv.org/abs/2411.01530v1); [published article](https://doi.org/10.1016/j.amc.2024.129199)). It includes a maximizing graph for every listed multiplicity vector.

The checked mathematical source is commit `a74251313cc2afd21efa3e17257c64bbafd019c7`, tree `081e80e7fd18e575cd1d156c629ebb8029d4370e`. The terminal theorem is `W03.chemical_conjecture10` in [Conjecture10.lean](lean-candidate/W03/Conjecture10.lean). This documentation update preserves the 19 mathematical modules, three Lean configuration files, and verification workflow byte for byte.

## Exact scope

For every natural number `n ≥ 7`, the objects are connected simple graphs on `Fin n` with actual vertex degrees at most four. The objective, with `f(n) = 1/n`, is

```text
I(G) = sum over all unordered distinct vertex pairs {x,y}
       of |degree_G(x) - degree_G(y)|^(1/n).
```

The Lean definition uses `x < y` to count each unordered pair exactly once, subtracts degrees after casting to the real numbers, and uses `Real.rpow`. It excludes the diagonal and includes nonadjacent pairs.

Writing `a_i` for the number of vertices of degree `i`, the maximizing vectors are exactly:

| Order | `(a_1, a_2, a_3, a_4)` |
|---|---|
| `4k` | `(k, k, k, k)` |
| `4k + 1` | `(k, k, k, k + 1)` |
| `4k + 2` | `(k, k + 1, k, k + 1)` or `(k + 1, k, k + 1, k)` |
| `4k + 3` | `(k + 1, k, k + 1, k + 1)` |

`Chemical G` means that `G` is connected and every vertex has degree at most four. `Maximizes G` compares `I(G)` with every graph of the same order satisfying `Chemical`. It is defined by that universal inequality. `graphProfile G` consists of the actual four degree multiplicities. In readable notation, the terminal statement is:

```lean
theorem chemical_conjecture10 (n : ℕ) (hn : 7 ≤ n) :
    (∀ G : SimpleGraph (Fin n), Chemical G →
      (Maximizes G ↔ WinnerProfile n (graphProfile G))) ∧
    (∀ p : Fin 4 → ℕ, WinnerProfile n p →
      ∃ G : SimpleGraph (Fin n), Chemical G ∧ graphProfile G = p ∧
        totalIndex G = extremalValue n ∧ Maximizes G)
```

The [actual fully expanded type](formalization/MAIN_THEOREM_TYPE.txt) is copied without alteration from the successful run. The theorem has no extra assumptions about multiplicity feasibility, parity, nearest integers, or graph existence. Both vectors in the `4k + 2` row have their own existence conclusion through the quantification over every `p`.

This formalizes Conjecture 10 for `f(n) = 1/n`. It does not establish Conjecture 11, other choices of `f`, or a classification of graph isomorphism types.

## Proof coverage

The development constructs five base graphs and a four-vertex extension to realize every table vector. It identifies the unordered-pair objective with its degree-multiplicity quadratic, derives the sum and handshaking constraints from the actual graph, and uses integer differences for the transformed coordinates. Real-power coefficient bounds, eight exact penalty cases, and unique parity-class maxima yield a global upper bound and its equality cases. The final modules recover the four counts from those cases and use the graph realizations to establish the extremal equivalence.

In particular, `graph_global_bound_and_equality` proves both `I(G) ≤ extremalValue n` and equality if and only if the original table predicate holds. `winner_profile_attains_bound` calls `exists_graph_of_winnerProfile` to obtain an actual graph. Thus the maximum and attainment conclusions do not assume the existence of a maximizing graph. The historical finite computations are supplementary and are not the proof of the unbounded theorem.

## Recorded execution and trust boundary

[GitHub Actions run 38504445354](https://github.com/Aurantium-47/chemical-graph-sigma-extremizers/actions/runs/38504445354), job `115658595824`, checked the source commit above. The exact run was observed as completed/success, and its complete job log was obtained. All 19 project modules were newly compiled, with their imports bound to the fresh project artifacts. The log contains 171 complete declaration types and corresponding transitive axiom lists, 108 resource-supervised commands with exit code zero and no guard abort, and the final integrity and declaration assertion `PASS`.

The axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`; the terminal theorem uses those three axioms. Of the 171 lists, 155 contain all three, eight contain only `propext` and `Quot.sound`, and eight are empty. The checked declarations do not use `sorryAx`, custom axioms, or native-evaluation trust.

There are five nonblocking tactic-style warnings in `FinalCoordinates.lean`, at lines 149, 155, 162, 166, and 172: `tac1 <;> tac2` could be written as `tac1; tac2`. They do not report a mathematical or elaboration failure. No extra run was performed to change their formatting.

The run used Lean 4.19.0, mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the nine manifest-pinned packages, and 12 external cache roots. It ran on the standard `ubuntu-24.04` runner with one Lean thread and `Elab.async=false`. Peak sampled process-group RSS was 2,211,102,720 bytes, with zero sampled swap usage. Guarded child-command durations sum to 134.1633 seconds; this is not end-to-end wall-clock time.

External libraries used fixed precompiled caches. The original workflow changes two directory-pruning calls in mathlib's `Cache/Requests.lean` from `IO.FS.removeDirAll` to `pure ()`, preserving downloaded build directories. This is a cache-helper modification, not a change to Lean mathematical library sources; the full dependency checkout is therefore not claimed to be byte-for-byte unmodified. The patched helper SHA-256 is `646fed31a48d85ed75746ec09d06c23f5abdaca455518b6760b0dcb2b10c47c0`. Full external dependency source rebuilding and an independent kernel implementation were not performed.

A later metadata retrieval for the same run confirmed its unique job and all three reported steps as completed/success. That response did not provide a job completion timestamp, which remains null. This supplemental metadata does not represent a new build or replace the complete command/type/axiom log. The [public execution summary](formalization/RUN_38504445354.json) distinguishes the original in-progress snapshot from the later terminal observation.

## Historical documents and reproduction

The v0.1.1 manuscript, finite-check code and data, and [AI usage statement](AI_USAGE.md) remain their historical versions. Their statements that proof-assistant verification was not then claimed describe that earlier package. This supplement records the later Lean result without rewriting those files. The old tags and releases are unchanged.

See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for the fixed workflow, guards, source hashes, and its historical branch and file-whitelist restrictions. No new Lean, finite-check, or manuscript build is claimed for the documentation update.

The source references and attribution remain in the manuscript and README. No worldwide-priority or external human peer-review claim is made. This work was completed with AI assistance.
