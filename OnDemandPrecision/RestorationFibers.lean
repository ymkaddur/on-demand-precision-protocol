import Mathlib

/-!
# Restoring an attribute of the past needs side information the size of a fiber

A transition `T : X → Y` maps histories (or previous states) to current states. An attribute
`φ : X → Z` of the history is *restorable with tags in `W`* if a stored tag `a x ∈ W` and a decoder
`g` recover it from the current state: `g (T x) (a x) = φ x` for every `x`. The attribute can be the
previous state, an origin, a provenance label, a validity bit, or the state that a revoked update
would have left.

* `side_info_card`: the tag alphabet has at least as many elements as the number of values `φ`
  takes on any fiber `T⁻¹(y)`;
* `side_info_exists`: that number suffices, so the minimal alphabet is exactly the largest number
  of values of `φ` on a fiber;
* `restore_card`: restoring the whole history needs at least the size of the largest fiber;
* `overwrite_needs_tags` (**refutation**): answering every query about the current state is not
  restorability. After an overwrite, the current value is read exactly, yet restoring the
  overwritten value needs `N` tags;
* `truncation_needs_tags`: dropping `d` low bits of a `(b + d)`-bit integer leaves fibers of size
  `2^d`, so exact restoration needs `2^d` tags, that is `d` stored bits;
* `fiberValues_prod`, `joint_side_info_card`: for independent components (for instance two
  conversations) the values on fibers form a product, so a joint tag needs at least the product of
  the separate alphabets. Mixing the components saves nothing over keeping them isolated.
-/

namespace OnDemandPrecision.Restoration

open Finset

variable {X Y Z : Type*} [Fintype X] [DecidableEq Y] [DecidableEq Z]

/-- The values of `φ` over the histories that lead to the current state `y`. -/
def fiberValues (T : X → Y) (φ : X → Z) (y : Y) : Finset Z :=
  (univ.filter fun x => T x = y).image φ

theorem mem_fiberValues (T : X → Y) (φ : X → Z) (x : X) : φ x ∈ fiberValues T φ (T x) :=
  mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩

/-- **Side-information bound**: tags that restore `φ` from the current state number at least the
values of `φ` on any fiber. -/
theorem side_info_card {W : Type*} [Fintype W] (T : X → Y) (φ : X → Z) (a : X → W)
    (g : Y → W → Z) (hg : ∀ x, g (T x) (a x) = φ x) (y : Y) :
    (fiberValues T φ y).card ≤ Fintype.card W := by
  calc (fiberValues T φ y).card ≤ (univ.image (g y)).card := by
        apply card_le_card
        intro z hz
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
        have hxy : T x = y := (mem_filter.mp hx).2
        exact mem_image.mpr ⟨a x, mem_univ _, by rw [← hxy, hg]⟩
    _ ≤ (univ : Finset W).card := card_image_le
    _ = Fintype.card W := card_univ

/-- **Tightness**: `m` tags suffice as soon as every fiber carries at most `m` values of `φ`. -/
theorem side_info_exists [Nonempty Z] (T : X → Y) (φ : X → Z) (m : ℕ)
    (hm : ∀ y, (fiberValues T φ y).card ≤ m) :
    ∃ (a : X → Fin m) (g : Y → Fin m → Z), ∀ x, g (T x) (a x) = φ x := by
  classical
  let e : ∀ y, {z // z ∈ fiberValues T φ y} ≃ Fin (fiberValues T φ y).card :=
    fun y => Fintype.equivFinOfCardEq (Fintype.card_coe (fiberValues T φ y))
  refine ⟨fun x => Fin.castLE (hm (T x)) (e (T x) ⟨φ x, mem_fiberValues T φ x⟩),
    fun y w => if h : (w : ℕ) < (fiberValues T φ y).card then ((e y).symm ⟨w, h⟩ : Z)
      else Classical.arbitrary Z, fun x => ?_⟩
  have hlt : ((Fin.castLE (hm (T x)) (e (T x) ⟨φ x, mem_fiberValues T φ x⟩) : Fin m) : ℕ) <
      (fiberValues T φ (T x)).card := (e (T x) ⟨φ x, mem_fiberValues T φ x⟩).isLt
  dsimp only
  rw [dif_pos hlt]
  have hfin : (⟨_, hlt⟩ : Fin (fiberValues T φ (T x)).card) =
      e (T x) ⟨φ x, mem_fiberValues T φ x⟩ := Fin.ext rfl
  rw [hfin, Equiv.symm_apply_apply]

/-- Restoring the whole history needs at least the size of each fiber. -/
theorem restore_card [DecidableEq X] {W : Type*} [Fintype W] (T : X → Y) (a : X → W)
    (g : Y → W → X) (hg : ∀ x, g (T x) (a x) = x) (y : Y) :
    (univ.filter fun x => T x = y).card ≤ Fintype.card W := by
  have := side_info_card T id a g hg y
  simpa [fiberValues] using this

/-- **Refutation: a correct answer now is not restorability.** An overwrite `(old, new) ↦ new`
answers the query "current value" exactly, but any scheme that restores the old value needs `N`
tags. -/
theorem overwrite_needs_tags (N : ℕ) {W : Type*} [Fintype W] (a : Fin N × Fin N → W)
    (g : Fin N → W → Fin N) (hg : ∀ x, g x.2 (a x) = x.1) (y : Fin N) : N ≤ Fintype.card W := by
  have h := side_info_card (Prod.snd : Fin N × Fin N → Fin N) Prod.fst a g hg y
  have hfull : fiberValues (Prod.snd : Fin N × Fin N → Fin N) Prod.fst y = univ := by
    ext z
    simp only [mem_univ, iff_true]
    exact mem_image.mpr ⟨(z, y), mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩
  rw [hfull, card_univ, Fintype.card_fin] at h
  exact h

/-- Dropping the `d` low bits of a `(b + d)`-bit integer: exact restoration needs `2^d` tags. -/
theorem truncation_needs_tags (b d : ℕ) {W : Type*} [Fintype W] (a : Fin (2 ^ (b + d)) → W)
    (g : ℕ → W → Fin (2 ^ (b + d)))
    (hg : ∀ x : Fin (2 ^ (b + d)), g ((x : ℕ) / 2 ^ d) (a x) = x) :
    2 ^ d ≤ Fintype.card W := by
  have h := restore_card (fun x : Fin (2 ^ (b + d)) => (x : ℕ) / 2 ^ d) a g hg 0
  have hle : 2 ^ d ≤ 2 ^ (b + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine le_trans ?_ h
  have hinj := card_le_card_of_injOn (s := (univ : Finset (Fin (2 ^ d))))
    (t := univ.filter fun x : Fin (2 ^ (b + d)) => (x : ℕ) / 2 ^ d = 0) (Fin.castLE hle)
    (by
      intro j _
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Fin.val_castLE]
      exact Nat.div_eq_of_lt j.isLt)
    (Fin.castLE_injective hle).injOn
  simpa using hinj

/-- For independent components the values on fibers form a product. -/
theorem fiberValues_prod {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type*} [Fintype X₁] [Fintype X₂]
    [DecidableEq Y₁] [DecidableEq Y₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (T₁ : X₁ → Y₁) (T₂ : X₂ → Y₂) (φ₁ : X₁ → Z₁) (φ₂ : X₂ → Z₂) (y₁ : Y₁) (y₂ : Y₂) :
    fiberValues (Prod.map T₁ T₂) (Prod.map φ₁ φ₂) (y₁, y₂) =
      fiberValues T₁ φ₁ y₁ ×ˢ fiberValues T₂ φ₂ y₂ := by
  ext ⟨z₁, z₂⟩
  simp only [fiberValues, mem_image, mem_filter, mem_univ, true_and, mem_product, Prod.exists,
    Prod.map_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨x₁, x₂, ⟨h₁, h₂⟩, e₁, e₂⟩
    exact ⟨⟨x₁, h₁, e₁⟩, ⟨x₂, h₂, e₂⟩⟩
  · rintro ⟨⟨x₁, h₁, e₁⟩, ⟨x₂, h₂, e₂⟩⟩
    exact ⟨x₁, x₂, ⟨h₁, h₂⟩, e₁, e₂⟩

/-- **Isolation costs nothing**: a joint tag for two independent components needs at least the
product of the separate alphabets, which separate tags already achieve (`side_info_exists`). -/
theorem joint_side_info_card {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W : Type*} [Fintype X₁] [Fintype X₂]
    [DecidableEq Y₁] [DecidableEq Y₂] [DecidableEq Z₁] [DecidableEq Z₂] [Fintype W]
    (T₁ : X₁ → Y₁) (T₂ : X₂ → Y₂) (φ₁ : X₁ → Z₁) (φ₂ : X₂ → Z₂) (a : X₁ × X₂ → W)
    (g : Y₁ × Y₂ → W → Z₁ × Z₂) (hg : ∀ x, g (Prod.map T₁ T₂ x) (a x) = Prod.map φ₁ φ₂ x)
    (y₁ : Y₁) (y₂ : Y₂) :
    (fiberValues T₁ φ₁ y₁).card * (fiberValues T₂ φ₂ y₂).card ≤ Fintype.card W := by
  have := side_info_card (Prod.map T₁ T₂) (Prod.map φ₁ φ₂) a g hg (y₁, y₂)
  rwa [fiberValues_prod, card_product] at this

end OnDemandPrecision.Restoration
