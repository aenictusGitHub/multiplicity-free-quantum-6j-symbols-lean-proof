# Lean proof of the multiplicity-free quantum 6j formula

John Martin · 25 November 2026

This repository contains the manuscript *A representation-theoretic proof of the AMS relation* and its Lean certificate. It proves that the Alekseev–Morozov–Sleptsov factorial formula gives the actual quantum $6j$ coefficients of $U_q(\mathfrak{sl}_N)$ for both multiplicity-free symmetric families.

The formula is Eq. (35) of V. Alekseev, A. Morozov and A. Sleptsov, *Multiplicity-free $U_q(\mathfrak{sl}_N)$ 6-j symbols: Relations, asymptotics, symmetries*, *Nuclear Physics B* **960**, 115164 (2020). [DOI](https://doi.org/10.1016/j.nuclphysb.2020.115164) · [arXiv:1912.13325](https://arxiv.org/abs/1912.13325)

At $N\geq 3$ and real $v>0$, $v\neq 1$, the proof constructs one shared table of isometric intertwiners for both families. The classical and complex results concern the coefficient limits and compatible analytic continuations described in the manuscript.

## Downloads

The [v1.0.1 release](https://github.com/aenictusGitHub/multiplicity-free-quantum-6j-symbols-lean-proof/releases/tag/v1.0.1) contains the manuscript PDF, the self-contained LaTeX source ZIP, the audited Lean certificate ZIP, and SHA-256 checksums. The [manuscript source](manuscript/AMS_Eq35_representation_theoretic_proof.tex) and [Lean project](lean/AMSPhysical) are also browsable here.

## Lean verification

The full source replay and an independent rebuild of the delivered certificate passed with Lean 4.24.0 and Mathlib v4.24.0. Each rebuilt 985 modules and audited 3,346 theorems and 4,482 declaration roots.

- [`AMSPhysical.AMS_Eq35_complete`](lean/AMSPhysical/AMS35Certificate.lean) covers the coefficient identities, the physical classical limits, and the compatible complex continuations.
- [`AMSPhysical.AMS_Eq35_shared_actual_vertex_certificate`](lean/AMSPhysical/AMSSharedVertexCertificate.lean) covers the shared vertex table, the isometric intertwiner roles, and the coefficient identities for both families.

The certificate ZIP contains the pinned toolchain files and the successful audit report and logs. To reproduce the audit, use Lean 4.24.0 and a Mathlib v4.24.0 checkout with its compiled cache. Run the following from `lean/AMSPhysical` in this repository or `AMSPhysical` in the extracted ZIP.

```sh
python3 verify.py --jobs 4 --lean /path/to/lean --mathlib /path/to/mathlib
```

## AI use

John Martin posed the question and directed the work. GPT-6.1 Sol derived the proof and wrote the manuscript. GPT-6.2 Sol reviewed the manuscript. The formal results were checked with Lean and Mathlib.
