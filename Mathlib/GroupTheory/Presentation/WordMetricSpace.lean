/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Presentation.WordMetric
public import Mathlib.Topology.MetricSpace.QuasiIsometry

/-!
# The word metric as a bundled metric space

The word length of a generating family `P : Group.Generators G α` induces an `ℕ`-valued distance
`Group.Generators.wordDist` on `G` (see `Mathlib/GroupTheory/Presentation/WordMetric.lean`). This
file casts it to `ℝ` and packages it as a genuine `MetricSpace G`, which is the form the
metric-geometry API — in particular `QuasiIsometryWith` and friends — expects.

Because the metric depends on the *choice* of generating family `P`, it is provided as a `def`
(`wordMetricSpace P`), **not** as an instance: there is no canonical generating family on a group.
To use it, activate it locally, e.g. `letI := P.wordMetricSpace`.

## Main definitions

* `Group.Generators.wordMetricSpace P`: the `MetricSpace G` whose distance is
  `fun g h => (P.wordDist g h : ℝ)`. It is a genuine metric (not merely a pseudometric) because
  `wordDist g h = 0 ↔ g = h`.

## Main statements

* `Group.Generators.wordMetricSpace_dist`: the distance is `P.wordDist` cast to `ℝ`.
* `Group.Generators.isometry_mul_left`: left translation `g ↦ x * g` is an isometry of the word
  metric (the word metric is left-invariant).
* `Group.Generators.isQuasiIsometricEmbedding_mul_left`: consequently left translation is a
  quasi-isometric embedding — the first point of contact with the quasi-isometry API.

## TODO

* Compare the word metrics of two different generating families `P` and `Q` on the same group. The
  identity `G → G` is a quasi-isometry when `P` and `Q` are comparable (e.g. both finite). Stating
  this needs two `MetricSpace G` structures at once, so it should go through a type synonym carrying
  the chosen family (à la `WithLp`), rather than the `def` provided here.
-/

@[expose] public section

open scoped NNReal

namespace Group.Generators

variable {G α : Type*} [Group G] (P : Group.Generators G α) [DecidableEq α]

/-- The word metric of the generating family `P`, packaged as a `MetricSpace G` with distance
`fun g h => (P.wordDist g h : ℝ)`.

This is a `def` rather than an instance: the metric depends on the chosen generating family, so
there is no canonical `MetricSpace G`. Use it via `letI := P.wordMetricSpace`. -/
@[reducible] noncomputable def wordMetricSpace : MetricSpace G where
  dist g h := (P.wordDist g h : ℝ)
  dist_self g := by simp
  dist_comm g h := by exact_mod_cast wordDist_comm g h
  dist_triangle g h k := by exact_mod_cast wordDist_triangle g h k
  eq_of_dist_eq_zero := by intro g h hgh; exact wordDist_eq_zero.mp (by exact_mod_cast hgh)

@[simp] theorem wordMetricSpace_dist (g h : G) :
    letI := P.wordMetricSpace; dist g h = (P.wordDist g h : ℝ) := rfl

/-- Left translation `g ↦ x * g` is an isometry of the word metric: the word metric is
left-invariant. -/
theorem isometry_mul_left (x : G) :
    letI := P.wordMetricSpace; Isometry (fun g : G => x * g) := by
  letI := P.wordMetricSpace
  refine Isometry.of_dist_eq fun g h => ?_
  change (P.wordDist (x * g) (x * h) : ℝ) = (P.wordDist g h : ℝ)
  exact_mod_cast wordDist_mul_left x g h

/-- Left translation is a quasi-isometric embedding of the word metric into itself. -/
theorem isQuasiIsometricEmbedding_mul_left (x : G) :
    letI := P.wordMetricSpace; IsQuasiIsometricEmbedding (fun g : G => x * g) := by
  letI := P.wordMetricSpace
  exact (P.isometry_mul_left x).isQuasiIsometricEmbedding

end Group.Generators
