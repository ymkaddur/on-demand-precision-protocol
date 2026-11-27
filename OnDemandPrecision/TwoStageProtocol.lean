import Mathlib

/-!
# A certified two-stage decision protocol with on-demand precision

Exact logits `z` are never computed. Instead the protocol uses:
* base estimates `zb` with `|zb j - z j| ≤ εb` for every class `j` (read from a low-bit base code);
* refined estimates `zr` with `|zr j - z j| ≤ εr`, valid only on a stored set `R` of refined rows
  (read from refinement planes, only when needed).

A competitor `j` is **beaten** by the candidate `i` if `zb j + 2 εb < zb i` (base filter), or if
both rows are refined and `zr j + 2 εr < zr i` (refinement, read on demand). The protocol
**accepts** `i` when every competitor is beaten. Otherwise it abstains and defers.

* `accepts_sound`: no false positive. Whenever the protocol accepts `i`, the class `i` is the
  exact strict argmax of `z`, for every input satisfying the error guarantees;
* `accepts_complete`: it accepts the true winner whenever each competitor has an exact margin
  `> 4 εb`, or both rows are refined and the margin is `> 4 εr`;
* `refinement_reads`: refinement planes are read only for competitors that the base filter cannot
  separate;
* `stored_budget_iff`, `budget_instance`: the storage equilibrium. With a `b`-bit base, an `s`-bit
  scale per `g` weights, and `r` refinement bits plus an `i`-bit row index on a fraction `f` of
  rows of length `m`, the stored cost is `b + s/g + f (r + i/m)` bits per weight. It fits `6/5`
  iff `f (r + i/m) ≤ 6/5 - b - s/g`.
-/

namespace OnDemandPrecision

variable {ι : Type*}

/-- Competitor `j` is beaten by candidate `i`, at base precision or at refined precision. -/
def Beaten (zb zr : ι → ℝ) (εb εr : ℝ) (R : Set ι) (i j : ι) : Prop :=
  zb j + 2 * εb < zb i ∨ (i ∈ R ∧ j ∈ R ∧ zr j + 2 * εr < zr i)

/-- The protocol accepts candidate `i` when every competitor is beaten. -/
def Accepts (zb zr : ι → ℝ) (εb εr : ℝ) (R : Set ι) (i : ι) : Prop :=
  ∀ j, j ≠ i → Beaten zb zr εb εr R i j

/-- **No false positive.** -/
theorem accepts_sound (z zb zr : ι → ℝ) (εb εr : ℝ) (R : Set ι)
    (hb : ∀ j, |zb j - z j| ≤ εb) (hr : ∀ j ∈ R, |zr j - z j| ≤ εr) (i : ι)
    (h : Accepts zb zr εb εr R i) : ∀ j, j ≠ i → z j < z i := by
  intro j hj
  rcases h j hj with hbase | ⟨hiR, hjR, href⟩
  · have h1 := abs_le.mp (hb j)
    have h2 := abs_le.mp (hb i)
    linarith [h1.1, h2.2]
  · have h1 := abs_le.mp (hr j hjR)
    have h2 := abs_le.mp (hr i hiR)
    linarith [h1.1, h2.2]

/-- **Completeness under margin.** The true winner is accepted when every competitor is separated
by more than `4 εb`, or is a refined row (as is the winner) separated by more than `4 εr`. -/
theorem accepts_complete (z zb zr : ι → ℝ) (εb εr : ℝ) (R : Set ι)
    (hb : ∀ j, |zb j - z j| ≤ εb) (hr : ∀ j ∈ R, |zr j - z j| ≤ εr) (i : ι)
    (hm : ∀ j, j ≠ i → z j + 4 * εb < z i ∨ (i ∈ R ∧ j ∈ R ∧ z j + 4 * εr < z i)) :
    Accepts zb zr εb εr R i := by
  intro j hj
  rcases hm j hj with hbase | ⟨hiR, hjR, href⟩
  · left
    have h1 := abs_le.mp (hb j)
    have h2 := abs_le.mp (hb i)
    linarith [h1.2, h2.1]
  · right
    refine ⟨hiR, hjR, ?_⟩
    have h1 := abs_le.mp (hr j hjR)
    have h2 := abs_le.mp (hr i hiR)
    linarith [h1.2, h2.1]

/-- Refinement is on demand. If the protocol accepts and a competitor is not separated by the base
filter, then both rows are refined: those are the only rows whose refinement planes are read. -/
theorem refinement_reads (zb zr : ι → ℝ) (εb εr : ℝ) (R : Set ι) (i : ι)
    (h : Accepts zb zr εb εr R i) (j : ι) (hj : j ≠ i) (hamb : ¬ zb j + 2 * εb < zb i) :
    i ∈ R ∧ j ∈ R := by
  rcases h j hj with hbase | ⟨hiR, hjR, -⟩
  · exact absurd hbase hamb
  · exact ⟨hiR, hjR⟩

/-- Stored bits per weight: `b`-bit base, `s`-bit scale per `g` weights, `r` refinement bits and an
`i`-bit row index on a fraction `f` of rows of length `m`. -/
def storedBits (b s g f r i m : ℚ) : ℚ := b + s / g + f * (r + i / m)

/-- **Storage equilibrium**: the total fits `6/5` bits per weight iff the refinement overhead fits
what the base and the scales leave. -/
theorem stored_budget_iff (b s g f r i m : ℚ) :
    storedBits b s g f r i m ≤ 6 / 5 ↔ f * (r + i / m) ≤ 6 / 5 - b - s / g := by
  unfold storedBits
  constructor <;> intro h <;> linarith

/-- Instance: a 1-bit base, 16-bit scales per 128 weights, 2 refinement bits and a 16-bit index per
refined row of length 4096. The budget allows refining exactly up to the fraction
`f* = (3/40) · (256/513) = 32/855` (about 3.74 %) of the rows. -/
theorem budget_instance (f : ℚ) :
    storedBits 1 16 128 f 2 16 4096 ≤ 6 / 5 ↔ f ≤ 32 / 855 := by
  rw [stored_budget_iff]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

end OnDemandPrecision
