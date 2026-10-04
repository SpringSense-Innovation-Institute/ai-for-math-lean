# Erdős 732: block-compatible sequences

This Lean project formalizes the affirmative answer to Erdős problem 732:
there is an absolute constant `c > 0` such that, for all sufficiently large `n`,
at least `exp(c * sqrt(n) * log(n))` nonincreasing lists of block sizes are
realized by pairwise balanced designs on `n` points. Blocks have size at least
two; every pair of distinct points lies in exactly one block. `log` is natural.

The mathematical source is Noga Alon's
[Blocking partial designs and block-compatible sequences](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf),
Problem 1.2 and Theorem 2.3. The proof constructs a projective plane over a finite
field, takes prescribed subsets of its lines, fills uncovered pairs with blocks
of size two, and counts the resulting lists. Extension to larger sets and
Bertrand's postulate supply the eventual bound. See
[the statement audit](docs/STATEMENT.md) for scope and source corrections.

`Challenge.lean` is the independently readable mathematical interface;
`Solution.lean` bridges to `ErdosProblems.P732.erdos732_yes` in
`LeanProject/ErdosProblems/P732/LowerBound.lean`. The existing module paths are
preserved. The paper's partial-design blocking result is outside this project.

## Build and verify

Install the toolchain named by `lean-toolchain`, then run from the repository root:

```sh
cd erdos-problems/erdos732
```

Run the following commands from that project directory:

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
bash scripts/verify-comparator.sh --local
```

The last command runs the toolchain's Comparator and the NanoDa and con-ron
kernels without Linux sandbox protection. It is a local audit. The official
protected workflow has its own status in [preflight](stage8/PALOMAR_PREFLIGHT.md).
`Challenge.lean` contains one intentional protocol `sorry`; the solution and
substantive proof contain none. Metadata and intake checks can be run with:

```sh
python3 scripts/audit-release.py --official /path/to/PalomarSubmission --schema /path/to/v0.4.schema.json
```

Use the PalomarSubmission revision recorded in the
[release manifest](stage8/PALOMAR_RELEASE_MANIFEST.json). That audit needs PyYAML
and jsonschema; neither is a Lean build dependency. The manifest and
[Claim Ledger](stage8/CLAIM_LEDGER.md) record exact inputs and evidence. A clean
source checkout may reuse pinned dependency caches, but must build this
project's own modules from source.

## Provenance and release status

The source package included AI-assisted paper analysis. Historical model
identities and proof-engineering provenance were not sufficiently recorded to
attribute them. Codex performed release packaging and compatibility work;
mechanical verification and independent human review are recorded separately.
No independent human peer review is claimed.

Formalization author and responsible maintainer: **Jingxuan Ding**, affiliated
with **SpringSense Innovation Institute**. Released under the [MIT license](LICENSE).
Dependencies retain their own licenses.

The project is included in
[SpringSense Innovation Institute's AI for Math repository](https://github.com/SpringSense-Innovation-Institute/ai-for-math-lean)
under `erdos-problems/erdos732/`. The `stage8/` manifests and evidence are
historical records from the standalone project; their commit identifiers refer
to that project's history. They do not certify this repository's PR or claim
that the official protected Palomar workflow has run. Palomar submission
remains outstanding. The original source and operational records are retained
in the local archive described by the manifest.
