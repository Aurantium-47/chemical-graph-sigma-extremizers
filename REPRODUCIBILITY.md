# Reproducibility and historical artifacts

## Lean result

The recorded successful build belongs to mathematical commit `a74251313cc2afd21efa3e17257c64bbafd019c7`, tree `081e80e7fd18e575cd1d156c629ebb8029d4370e`, and [run 38504445354](https://github.com/Aurantium-47/chemical-graph-sigma-extremizers/actions/runs/38504445354). The present documentation update does not claim another CI result.

The exact procedure is retained in [.github/workflows/w03-four-vertex-extension.yml](.github/workflows/w03-four-vertex-extension.yml). It includes source hashes, the dependency revisions, 12 cache roots, ordered compilation of all 19 project modules, fresh-import checks, full type/axiom output, and final integrity assertions. The [execution summary](formalization/RUN_38504445354.json) binds that procedure and its results to the fixed mathematical commit. The [formalization note](FORMALIZATION.md) states the scope and trust boundaries.

The workflow is historical verification machinery: it triggers on source/workflow changes on `codex/w03-four-vertex-extension`, and it requires exactly the 23 original additions relative to the former public main `081c9289a709d55457c172f3b355d77c5b6a4688`. The later documentation changes do not satisfy that historical whitelist. Updating the default branch therefore does not automatically rerun or recertify the supplement. Reproducing the recorded procedure requires the exact mathematical commit and original trigger context; a newly adapted workflow would be a separate execution with its own evidence.

Fixed environment:

- Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- All nine package revisions in [lake-manifest.json](lean-candidate/lake-manifest.json), including ProofWidgets tag `v0.0.57`.
- Standard `ubuntu-24.04`; one Lean thread; `Elab.async=false`.
- Initial total memory at least 14 GiB and available memory at least 12 GiB; at least 8 GiB available before each supervised command.
- Process-group RSS limit 6 GiB, swap limit 512 MiB, available-memory floor 2 GiB.
- Ordinary supervised-command limit 180 seconds; the explicit external-cache setup command has a 900-second limit; overall setup/build budget 1,200 seconds; job limit 40 minutes.

The workflow downloads fixed external caches. Before that download, it patches mathlib's `Cache/Requests.lean` in exactly two places: the `IO.FS.removeDirAll (buildDir / "lib")` and `IO.FS.removeDirAll (buildDir / "ir")` calls become `pure ()`, so existing build directories are retained. The patched helper SHA-256 is `646fed31a48d85ed75746ec09d06c23f5abdaca455518b6760b0dcb2b10c47c0`. The dependency-status assertion permits only this helper modification. The mathematical library sources and pinned revisions are unchanged; the entire dependency checkout is not claimed to be unmodified.

The 19 project modules were freshly compiled, but the result does not include a full source rebuild of external dependencies or checking by a separate kernel implementation. Five nonblocking tactic-style warnings are disclosed. Subsequent metadata for the same run confirmed the unique job and all three steps completed/success; the response omitted the completion timestamp. This was additional observation of the original run, not a new execution.

## Historical finite checks and manuscript

The v0.1.1 `verify.py`, `verification.json`, `connected_graphs.json`, `main.tex`, and `main.pdf` are preserved byte for byte. They retain the written proof and finite checks described in the README. Finite verification is a separate kind of evidence from the all-parameter Lean theorem. The old AI usage statement also retains its historical wording; the later formalization is documented in `FORMALIZATION.md`.

To reproduce the old finite checks in a disposable copy with Python 3.8 or later:

```text
python verify.py
```

Use normal Python execution, because the verifier uses assertions. This command rewrites the two JSON result files and may change timing or environment metadata. No finite-check rerun was performed for this documentation update.

The standalone manuscript can be built in a disposable copy with a standard TeX distribution:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

No TeX compilation was performed for this update. The existing PDF, tags, and release assets remain unchanged.

## Distribution integrity

[PUBLIC_FILES.txt](PUBLIC_FILES.txt) enumerates the distributable repository files. [SHA256SUMS.txt](SHA256SUMS.txt) covers every listed file except itself, avoiding self-reference. The mathematical source and workflow hashes in the execution summary describe the checked commit; the distribution checksums also cover the newer documentation. File hashes establish identity, not theorem correctness or independent review.

Existing source references and attribution are retained. This update adds no new licensing grant and does not change the rights attached to the historical files.
