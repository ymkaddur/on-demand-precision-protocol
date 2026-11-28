# on-demand-precision-protocol

## Directional refinement of linear readings

[`DirectionalReaderBudget.lean`](OnDemandPrecision/DirectionalReaderBudget.lean)
gives exact linear-reader endpoints for a product of closed coordinate cells.
Both endpoints are attained by choosing each cell's endpoint according to the
reader sign. The midpoint error is bounded by the sum of half-widths weighted
by the absolute reader coefficients. A block with a common half-width needs
only the sum of those coefficients' absolute values. Bisection halves that
block's contribution, and the acceptance test also accounts for arithmetic and
prior approximation errors.

See `reading_mem_interval`, `lower_attained`, `upper_attained`,
`midpoint_error_le`, `radius_by_blocks`, `radius_refines`, `bisect_enclosure`
and `accept_with_debt`. The statements concern a supplied product enclosure.
Input quantization, rounding bounds and physical layout require separate
verification.

A certified decision protocol in which precision is an action taken on demand, with exact
storage-budget conditions and exact robust certificates for structured perturbations, in Lean 4
with Mathlib.

Logits are first estimated from a low-bit base code with a certified error `εb`. A contrast-margin
filter accepts the decision when every competitor is separated. Only the competitors it cannot
separate are compared again using refinement planes, which are stored for a set `R` of rows and
have error `εr < εb`. Otherwise the protocol abstains and defers.

Every theorem is checked by the Lean kernel, with no `sorry`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Labels:

- **[L]**: a new construction or theorem proved in Lean.
- **[L-known]**: a Lean formalization of a known result.
- **refuted**: a counterexample proved in Lean.
- **open**: a precise statement not resolved here.

The scope of each result is given with it.

## Contents

| Module | Statement | Status | Scope |
|--------|-----------|--------|-------|
| `TwoStageProtocol` | **No false positive**: if the protocol accepts `i`, then `i` is the exact strict argmax | [L] | every input whose estimates satisfy `‖zb − z‖∞ ≤ εb` and `|zr_j − z_j| ≤ εr` on `R`; nothing else is assumed |
| | **Completeness**: the true winner is accepted when each competitor has exact margin `> 4εb`, or both rows lie in `R` and the margin is `> 4εr` | [L] | the bounds `4ε` are sufficient, not claimed optimal |
| | **On demand**: refinement is read only for competitors that the base filter does not separate | [L] | — |
| | **Storage equilibrium**: `b + s/g + f(r + i/m) ≤ 6/5 bpw ⟺ f(r + i/m) ≤ 6/5 − b − s/g` | [L] | base `b` bits, `s`-bit scale per `g` weights, `r` refinement bits and an `i`-bit index on a fraction `f` of rows of length `m` |
| | instance: `b = 1`, `s/g = 16/128`, `r = 2`, `i = 16`, `m = 4096` allows refining a fraction `f ≤ 32/855 ≈ 3.74 %` of rows | [L] | exact rational arithmetic |
| `StructuredRobustCertificates` | low-rank class `δ_j = ⟨u_j, y⟩`, `‖y‖ ≤ ρ`: robust top-1 **iff** `z_i − z_j > ρ‖u_i − u_j‖` | [L-known] | dual-norm characterization; the supremum is attained, so the certificate is exact |
| | sign class `y ≥ 0`, `∑ y_k ≤ ρ`: robust **iff** `z_i − z_j > ρ·max(0, max_k(u_jk − u_ik))` | [L-known] | linear functionals are maximized at vertices of the scaled simplex; `ρ > 0` |
| | **separation**: with the same rows and radius, the sign constraint certifies a margin of `1/2` that the unconstrained ball rejects (it needs `> 1`) | [L] | explicit instance with two classes and one latent coordinate |

Open questions:

- **open**: a lower bound on the number of bits any certificate needs to guarantee top-k
  preservation over a structured class. The exact certificates here use `n − 1` contrast numbers;
  whether fewer bits suffice is not known.
- **open**: protocols that also bound the abstention rate. That requires a distribution of margins,
  which is not modeled here.

## Reproduce

```bash
lake exe cache get
lake build
scripts/audit.sh     # #print axioms for every theorem; fails on sorry, warnings or extra axioms
```

Pinned toolchain: `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`).

## License

MIT
