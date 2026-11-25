# A representation-theoretic proof of the AMS relation

John Martin · 25 November 2026

This manuscript proves that the factorial formula in Eq. (35) of [Alekseev, Morozov, and Sleptsov](https://doi.org/10.1016/j.nuclphysb.2020.115164) gives the quantum \(6j\) coefficients for both multiplicity-free symmetric families. At \(N\geq 3\) and real \(v>0\), \(v\neq 1\), it constructs one shared table of isometric intertwiners for both families. The classical and complex results concern the coefficient limits and compatible analytic continuations described in the manuscript.

## Downloads

The [v1.0.0 release](https://github.com/aenictusGitHub/ams-eq35-proof/releases/tag/v1.0.0) contains the manuscript PDF, the self-contained LaTeX source ZIP, the audited Lean certificate ZIP, and SHA-256 checksums. The [manuscript source](manuscript/AMS_Eq35_representation_theoretic_proof.tex) and [Lean project](lean/AMSPhysical) are also browsable here.

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
