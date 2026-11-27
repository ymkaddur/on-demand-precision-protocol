# Restoration and side information

Status labels: **[L-known]** formalized here, mathematically known or elementary;
**[L]** formalized here, statement new in this form; **refuted** the claim is false and the
counterexample is formalized; **open** not proved.

## Statement

A transition `T : X → Y` maps histories (or previous states) to current states. An attribute
`φ : X → Z` is *restorable with tags in `W`* if a stored tag `a x ∈ W` and a decoder `g` recover it
from the current state: `g (T x) (a x) = φ x` for every `x`.

**Theorem.** Restoration with tags in `W` is possible if and only if `|W|` is at least the largest
number of values that `φ` takes on a fiber `T⁻¹(y)` (`side_info_card`, `side_info_exists`).

## Motivation

Separate what a representation must keep to answer questions about the present from what it must
keep to restore, revoke or audit the past. The same theorem covers each kind of information by the
choice of `φ`:

| Information | Attribute `φ` of the history | Tags needed |
|-------------|------------------------------|-------------|
| current state, future readings | a function of `T x` | none |
| full history | identity | largest fiber |
| origin, provenance, validity | a label of the history | largest number of labels on a fiber |
| restoring an earlier version | that version | largest number of versions on a fiber |
| revoking one update | the state the history would reach without that update | largest number of such states on a fiber |

Revocation is not restoration: the attribute is a function of the whole history, not of the
previous state, so the two can need different amounts of side information.

## Proof

The decoder at a fixed current state, `w ↦ g y w`, maps the tags onto the values of `φ` on the
fiber of `y`, so there are at least as many tags as values. Conversely, enumerate the values on each
fiber and store the index.

## Counterexamples and instances

* `overwrite_needs_tags` (**refuted**: "answering every current query gives restorability"). After an
  overwrite `(old, new) ↦ new`, every reading of the current value is exact, yet restoring `old`
  needs `N` tags.
* `truncation_needs_tags`. Dropping the `d` low bits of a `(b + d)`-bit integer leaves fibers of
  size `2^d`, so exact restoration needs `2^d` tags, that is `d` stored bits. This is the cost of the
  refinement planes of the two-stage protocol, if they are to restore exact values.
* `fiberValues_prod`, `joint_side_info_card`. For independent components (for instance two
  separate sessions) the values on fibers form a product, so a joint tag needs at least the product
  of the separate alphabets. Keeping the components isolated costs nothing.

## Background

Elementary counting. Related: the history tape of reversible computation (C. H. Bennett, *Logical
reversibility of computation*, 1973) and the cost of erasure (R. Landauer, 1961); homing and
distinguishing experiments for finite automata (E. F. Moore, 1956). Deduplication in a content
addressed store is an injective re-encoding of the stored versions: fibers stay singletons, so it
loses nothing. Forgetting is a non-injective `T`.

## Formalization

`OnDemandPrecision/RestorationFibers.lean`

| Status | Statement | Lean name |
|--------|-----------|-----------|
| [L-known] | tags at least the number of values of `φ` on any fiber | `side_info_card` |
| [L-known] | that number of tags suffices | `side_info_exists` |
| [L-known] | restoring the whole history needs the largest fiber | `restore_card` |
| **refuted** | "a correct answer about the present implies restorability" (overwrite) | `overwrite_needs_tags` |
| [L-known] | dropping `d` low bits: exact restoration needs `2^d` tags | `truncation_needs_tags` |
| [L-known] | independent components: values on fibers form a product; joint tags need the product | `fiberValues_prod`, `joint_side_info_card` |

## Limitations

* Exact restoration only. Approximate restoration (up to a tolerance) and restoration with a
  probability of error are **open** here.
* An external store from which the past is fetched counts as tags: it does not make restoration free.
* Finite history spaces.

## Verification

`scripts/audit.sh` compiles every module with `#print axioms` of each theorem appended, and fails on
`sorry`, on warnings, or on axioms outside `propext`, `Classical.choice` and `Quot.sound`. Pinned
toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`.
