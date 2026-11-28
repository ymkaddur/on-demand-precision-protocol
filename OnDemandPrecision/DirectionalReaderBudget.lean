import Mathlib

/-!
# Directional budgets for a partially decoded vector

Independent closed cells give exact endpoints for a linear reader. A decoded
midpoint has an error bounded by the weighted half-widths. Refinement narrows
that enclosure, and a certificate may add separate prepaid and numerical errors.
-/

namespace OnDemandPrecision.DirectionalReader

open Finset

variable {I : Type*} [Fintype I]

def reading (w x : I → ℝ) : ℝ := ∑ i, w i * x i

def lower (w l u : I → ℝ) : ℝ := ∑ i, min (w i * l i) (w i * u i)

def upper (w l u : I → ℝ) : ℝ := ∑ i, max (w i * l i) (w i * u i)

def radius (w h : I → ℝ) : ℝ := ∑ i, |w i| * h i

/-- Intersecting independent coordinate cells with a linear reader gives this enclosure. -/
theorem reading_mem_interval (w l u x : I → ℝ)
    (valid : ∀ i, l i ≤ x i ∧ x i ≤ u i) :
    lower w l u ≤ reading w x ∧ reading w x ≤ upper w l u := by
  constructor
  · apply sum_le_sum
    intro i _
    by_cases hw : 0 ≤ w i
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (valid i).1 hw)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left (valid i).2 (le_of_not_ge hw))
  · apply sum_le_sum
    intro i _
    by_cases hw : 0 ≤ w i
    · exact (mul_le_mul_of_nonneg_left (valid i).2 hw).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left (valid i).1 (le_of_not_ge hw)).trans (le_max_left _ _)

/-- A sign-dependent choice of endpoints attains the lower bound. -/
theorem lower_attained (w l u : I → ℝ) (nonempty : ∀ i, l i ≤ u i) :
    ∃ x : I → ℝ, (∀ i, l i ≤ x i ∧ x i ≤ u i) ∧ reading w x = lower w l u := by
  refine ⟨fun i => if 0 ≤ w i then l i else u i, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact ⟨le_rfl, nonempty i⟩
    · exact ⟨nonempty i, le_rfl⟩
  · apply sum_congr rfl
    intro i _
    dsimp only
    by_cases hw : 0 ≤ w i
    · rw [if_pos hw, min_eq_left (mul_le_mul_of_nonneg_left (nonempty i) hw)]
    · rw [if_neg hw, min_eq_right (mul_le_mul_of_nonpos_left (nonempty i) (le_of_not_ge hw))]

/-- A sign-dependent choice of endpoints attains the upper bound. -/
theorem upper_attained (w l u : I → ℝ) (nonempty : ∀ i, l i ≤ u i) :
    ∃ x : I → ℝ, (∀ i, l i ≤ x i ∧ x i ≤ u i) ∧ reading w x = upper w l u := by
  refine ⟨fun i => if 0 ≤ w i then u i else l i, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact ⟨nonempty i, le_rfl⟩
    · exact ⟨le_rfl, nonempty i⟩
  · apply sum_congr rfl
    intro i _
    dsimp only
    by_cases hw : 0 ≤ w i
    · rw [if_pos hw, max_eq_right (mul_le_mul_of_nonneg_left (nonempty i) hw)]
    · rw [if_neg hw, max_eq_left (mul_le_mul_of_nonpos_left (nonempty i) (le_of_not_ge hw))]

/-- Half-widths of centered cells are paid in proportion to the reader's absolute weights. -/
theorem centered_error_le (w mid h x : I → ℝ) (bounds : ∀ i, |x i - mid i| ≤ h i) :
    |reading w x - reading w mid| ≤ radius w h := by
  unfold reading radius
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ i, |w i * x i - w i * mid i| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (bounds i) (abs_nonneg _)

theorem midpoint_error_le (w l u x : I → ℝ)
    (inside : ∀ i, l i ≤ x i ∧ x i ≤ u i) :
    |reading w x - reading w (fun i => (l i + u i) / 2)| ≤ radius w (fun i => (u i - l i) / 2) := by
  apply centered_error_le
  intro i
  apply abs_le.mpr
  have hi := inside i
  constructor <;> linarith [hi.1, hi.2]

theorem radius_refines (w h h' : I → ℝ) (narrower : ∀ i, h' i ≤ h i) :
    radius w h' ≤ radius w h := by
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (narrower i) (abs_nonneg _)

/-- The actual result, a decoded midpoint, the stored reference, and the target may have
separate errors. All three contributions are charged to the acceptance test. -/
theorem accept_with_debt (w l u stored : I → ℝ) (actual target η debt ε : ℝ)
    (inside : ∀ i, l i ≤ stored i ∧ stored i ≤ u i)
    (arithmetic : |actual - reading w (fun i => (l i + u i) / 2)| ≤ η)
    (prepaid : |reading w stored - target| ≤ debt)
    (certificate : η + radius w (fun i => (u i - l i) / 2) + debt ≤ ε) :
    |actual - target| ≤ ε := by
  let center := reading w (fun i => (l i + u i) / 2)
  have hsplit : actual - target = ((actual - center) + (center - reading w stored)) +
      (reading w stored - target) := by ring
  have hbox : |center - reading w stored| ≤ radius w (fun i => (u i - l i) / 2) := by
    rw [abs_sub_comm]
    exact midpoint_error_le w l u stored inside
  rw [hsplit]
  exact (abs_add_le _ _).trans
    ((add_le_add (abs_add_le _ _) le_rfl).trans ((add_le_add (add_le_add arithmetic hbox) prepaid).trans certificate))

/-- Equal half-widths in a block require only the sum of the absolute reader weights there. -/
theorem radius_by_blocks {B K : Type*} [Fintype B] [Fintype K]
    (w : B × K → ℝ) (h : B → ℝ) :
    radius w (fun i => h i.1) = ∑ b, (∑ k, |w (b, k)|) * h b := by
  unfold radius
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro b _
  rw [sum_mul]

/-- Refining a cell into either half preserves containment and reduces its half-width by half. -/
theorem bisect_enclosure {l u x : ℝ} (h : l ≤ x ∧ x ≤ u) :
    ((l ≤ x ∧ x ≤ (l + u) / 2) ∨ ((l + u) / 2 ≤ x ∧ x ≤ u)) ∧
    (((l + u) / 2 - l) / 2 = (u - l) / 4) ∧
    ((u - (l + u) / 2) / 2 = (u - l) / 4) := by
  refine ⟨?_, by ring, by ring⟩
  rcases le_total x ((l + u) / 2) with hx | hx
  · exact Or.inl ⟨h.1, hx⟩
  · exact Or.inr ⟨hx, h.2⟩

end OnDemandPrecision.DirectionalReader
