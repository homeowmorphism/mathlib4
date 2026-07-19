/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Quasi-isometries

A *quasi-isometry* is the fundamental notion of sameness in coarse geometry and geometric group
theory: it preserves distances up to a multiplicative and an additive error, and its image is only
required to be coarsely dense. Unlike an `Isometry`, a `Dilation`, or a `LipschitzWith`/
`AntilipschitzWith` map, it ignores the small-scale structure of a metric space entirely, so it is
the right notion to compare, for instance, a finitely generated group under a word metric with the
space it acts on (the Milnor–Švarc lemma).

This file sets up the basic definitions and their first closure properties, for maps between
arbitrary `PseudoMetricSpace`s. Everything is stated with `dist` (an `ℝ`-valued distance): the
additive error and the two-sided multiplicative bound both need honest subtraction, which the
extended distance `edist` does not provide.

## Main definitions

* `QuasiIsometryWith K C f`: `f : X → Y` is a `(K, C)`-quasi-isometric embedding, i.e. for all
  `x₁ x₂` both `dist (f x₁) (f x₂) ≤ K * dist x₁ x₂ + C` and `dist x₁ x₂ ≤ K * dist (f x₁) (f x₂)`
  `+ C` hold. Using the same constant `K` on both sides (rather than `K` and `K⁻¹`) avoids division
  and is equivalent up to enlarging `K`.
* `CoarselyDense C f`: the image of `f` is `C`-dense, `∀ y, ∃ x, dist y (f x) ≤ C`.
* `IsQuasiIsometricEmbedding f`: `∃ K C, QuasiIsometryWith K C f`.
* `IsQuasiIsometry f`: a quasi-isometric embedding with coarsely dense image.

## Main statements

* `QuasiIsometryWith.mono`: the property is preserved when the constants are enlarged.
* `QuasiIsometryWith.comp`, `IsQuasiIsometricEmbedding.comp`: quasi-isometric embeddings are closed
  under composition (the explicit-constant version tracks how `K` and `C` combine).
* `quasiIsometryWith_id`, `isQuasiIsometry_id`: the identity is a quasi-isometry.
* `Isometry.quasiIsometryWith`, `Isometry.isQuasiIsometricEmbedding`: an isometry is a
  `(1, 0)`-quasi-isometric embedding (but not a quasi-isometry unless its image is coarsely dense).

## Implementation notes

The constants `K` and `C` have type `ℝ≥0`, matching `LipschitzWith` and `AntilipschitzWith`; we do
not require `1 ≤ K`, since every statement here is monotone in the constants
(`QuasiIsometryWith.mono`) and the `1 ≤ K` normalisation can be recovered when needed.

## Tags

quasi-isometry, quasi-isometric embedding, coarse geometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- `f : X → Y` is a `(K, C)`-quasi-isometric embedding: distances are preserved up to the
multiplicative constant `K` and the additive constant `C`, in both directions. -/
def QuasiIsometryWith (K C : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x₁ x₂ : X, dist (f x₁) (f x₂) ≤ (K : ℝ) * dist x₁ x₂ + C ∧
    dist x₁ x₂ ≤ (K : ℝ) * dist (f x₁) (f x₂) + C

/-- The image of `f : X → Y` is `C`-coarsely dense: every point of `Y` is within `C` of the
image. -/
def CoarselyDense (C : ℝ≥0) (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, dist y (f x) ≤ C

/-- `f : X → Y` is a quasi-isometric embedding: a `(K, C)`-quasi-isometric embedding for some
constants `K` and `C`. -/
def IsQuasiIsometricEmbedding (f : X → Y) : Prop := ∃ K C : ℝ≥0, QuasiIsometryWith K C f

/-- `f : X → Y` is a quasi-isometry: a quasi-isometric embedding whose image is coarsely dense. -/
def IsQuasiIsometry (f : X → Y) : Prop :=
  ∃ K C : ℝ≥0, QuasiIsometryWith K C f ∧ CoarselyDense C f

/-- Enlarging the constants preserves being a quasi-isometric embedding. -/
theorem QuasiIsometryWith.mono {K K' C C' : ℝ≥0} {f : X → Y} (h : QuasiIsometryWith K C f)
    (hK : K ≤ K') (hC : C ≤ C') : QuasiIsometryWith K' C' f := by
  have hKr : (K : ℝ) ≤ K' := by exact_mod_cast hK
  have hCr : (C : ℝ) ≤ C' := by exact_mod_cast hC
  intro x₁ x₂
  obtain ⟨hup, hlo⟩ := h x₁ x₂
  exact ⟨hup.trans (by gcongr), hlo.trans (by gcongr)⟩

/-- A quasi-isometry is in particular a quasi-isometric embedding. -/
theorem IsQuasiIsometry.isQuasiIsometricEmbedding {f : X → Y} (h : IsQuasiIsometry f) :
    IsQuasiIsometricEmbedding f :=
  let ⟨K, C, h, _⟩ := h; ⟨K, C, h⟩

/-- The identity is a `(1, 0)`-quasi-isometric embedding. -/
theorem quasiIsometryWith_id : QuasiIsometryWith 1 0 (id : X → X) := by
  intro x₁ x₂; simp

theorem isQuasiIsometricEmbedding_id : IsQuasiIsometricEmbedding (id : X → X) :=
  ⟨1, 0, quasiIsometryWith_id⟩

/-- The identity is a quasi-isometry: its image is all of `X`, hence `0`-coarsely dense. -/
theorem isQuasiIsometry_id : IsQuasiIsometry (id : X → X) :=
  ⟨1, 0, quasiIsometryWith_id, fun y => ⟨y, by simp⟩⟩

/-- An isometry is a `(1, 0)`-quasi-isometric embedding. -/
theorem Isometry.quasiIsometryWith {f : X → Y} (hf : Isometry f) : QuasiIsometryWith 1 0 f := by
  intro x₁ x₂; rw [hf.dist_eq]; simp

theorem Isometry.isQuasiIsometricEmbedding {f : X → Y} (hf : Isometry f) :
    IsQuasiIsometricEmbedding f :=
  ⟨1, 0, hf.quasiIsometryWith⟩

/-- Quasi-isometric embeddings compose, with the multiplicative constants multiplying and the
additive constants combining. -/
theorem QuasiIsometryWith.comp {g : Y → Z} {f : X → Y} {K K' C C' : ℝ≥0}
    (hg : QuasiIsometryWith K' C' g) (hf : QuasiIsometryWith K C f) :
    QuasiIsometryWith (K' * K) (K' * C + C' + (K * C' + C)) (g ∘ f) := by
  intro x₁ x₂
  obtain ⟨hgup, hglo⟩ := hg (f x₁) (f x₂)
  obtain ⟨hfup, hflo⟩ := hf x₁ x₂
  refine ⟨?_, ?_⟩
  · calc dist (g (f x₁)) (g (f x₂))
        ≤ (K' : ℝ) * dist (f x₁) (f x₂) + C' := hgup
      _ ≤ (K' : ℝ) * ((K : ℝ) * dist x₁ x₂ + C) + C' := by gcongr
      _ ≤ ((K' * K : ℝ≥0) : ℝ) * dist x₁ x₂ + ((K' * C + C' + (K * C' + C) : ℝ≥0) : ℝ) := by
          push_cast; nlinarith [mul_nonneg K.coe_nonneg C'.coe_nonneg, C.coe_nonneg]
  · calc dist x₁ x₂
        ≤ (K : ℝ) * dist (f x₁) (f x₂) + C := hflo
      _ ≤ (K : ℝ) * ((K' : ℝ) * dist (g (f x₁)) (g (f x₂)) + C') + C := by gcongr
      _ ≤ ((K' * K : ℝ≥0) : ℝ) * dist (g (f x₁)) (g (f x₂))
            + ((K' * C + C' + (K * C' + C) : ℝ≥0) : ℝ) := by
          push_cast; nlinarith [mul_nonneg K'.coe_nonneg C.coe_nonneg, C'.coe_nonneg]

theorem IsQuasiIsometricEmbedding.comp {g : Y → Z} {f : X → Y}
    (hg : IsQuasiIsometricEmbedding g) (hf : IsQuasiIsometricEmbedding f) :
    IsQuasiIsometricEmbedding (g ∘ f) := by
  obtain ⟨K', C', hg⟩ := hg
  obtain ⟨K, C, hf⟩ := hf
  exact ⟨_, _, hg.comp hf⟩
