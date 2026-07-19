/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Group presentations as data

`PresentedGroup rels` constructs *the* group presented by a set of relations `rels`. This file
provides the complementary *bundled* notion: a `Group.Presentation` packages a **chosen**
presentation of a given group `G` — a generating family together with a family of relators whose
normal closure is exactly the kernel of the induced map `FreeGroup α →* G`.

Unlike the predicate `IsFinitelyPresented`, which only asserts that *some* presentation exists, this
structure carries an actual presentation as data. This is what lets one define
presentation-dependent invariants (word length, area, the Dehn function, ...) by computing against
the chosen relators `rel`.

## Main definitions

* `Group.Generators G α`: a family `val : α → G` whose induced map `FreeGroup.lift val` is
  surjective, i.e. a generating family for `G` indexed by `α`.
* `Group.Generators.ofClosureEqTop`: build a generating family from the elementary condition
  `Subgroup.closure (Set.range val) = ⊤`.
* `Group.Generators.self`: the tautological generating family of `G` by itself.
* `Group.Presentation G α ρ`: a presentation `⟨α | rel⟩` of `G`, extending `Group.Generators G α`
  with relators `rel : ρ → FreeGroup α` and a proof that their normal closure is the kernel.
* `Group.Presentation.lift`: the induced surjection `FreeGroup α →* G`.
* `Group.Presentation.relSet`: the set of relators, `Set.range rel`.
* `Group.Presentation.presentedGroupEquiv`: the isomorphism `PresentedGroup relSet ≃* G` exhibiting
  `G` as the group presented by `⟨α | rel⟩`.

## Design notes

* A generating family is *finite* exactly when `α` is finite, expressed via `[Finite α]` rather than
  a bundled field. `Group.Generators.fg` shows such a family witnesses `Group.FG G`, and
  `Group.fg_iff_nonempty_finite_generators` is the bridge to the predicate `Group.FG`.
* A presentation is *finite* exactly when `α` and `ρ` are finite. This is expressed downstream via
  `[Finite α] [Finite ρ]` rather than as a bundled field, keeping the structure minimal.
* The bridge to the predicate `IsFinitelyPresented` — a group is finitely presented iff it admits a
  nonempty `Group.Presentation` with finite `α` and `ρ` — is
  `Group.isFinitelyPresented_iff_nonempty_presentation`, in
  `Mathlib/GroupTheory/Presentation/FinitelyPresented.lean`.

## Tags

group presentation, generators and relations
-/

@[expose] public section

variable {G α ρ : Type*} [Group G]

/-- The generators of a group are given by a generating family indexed by `α` such that
the induced homomorphism `FreeGroup.lift val : FreeGroup α →* G` is surjective. -/
structure Group.Generators (G : Type*) [Group G] (α : Type*) where
  val : α → G
  lift_surjective : Function.Surjective (FreeGroup.lift val)

namespace Group.Generators

variable (P : Group.Generators G α)

/-- A generating family generates `G`: the subgroup closure of its image is everything. This is the
elementary form of the defining condition; `Group.Generators.ofClosureEqTop` is the converse. -/
theorem closure_range_val_eq_top : Subgroup.closure (Set.range P.val) = ⊤ := by
  rw [← FreeGroup.range_lift_eq_closure, MonoidHom.range_eq_top]
  exact P.lift_surjective

/-- Build a generating family from the elementary condition that the image of `val` generates `G`
(`Subgroup.closure (Set.range val) = ⊤`), instead of from surjectivity of `FreeGroup.lift val`. -/
def ofClosureEqTop (val : α → G) (h : Subgroup.closure (Set.range val) = ⊤) :
    Group.Generators G α where
  val := val
  lift_surjective := by rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]; exact h

@[simp] theorem val_ofClosureEqTop (val : α → G) (h : Subgroup.closure (Set.range val) = ⊤) :
    (ofClosureEqTop val h).val = val := rfl

/-- The tautological generating family of `G`, indexed by `G` itself via the identity. -/
def self (G : Type*) [Group G] : Group.Generators G G :=
  ofClosureEqTop id (by rw [Set.range_id]; exact Subgroup.closure_univ)

@[simp] theorem val_self : (self G).val = id := rfl

/-- A finite generating family (finitely many generators, `[Finite α]`) witnesses that `G` is
finitely generated: the induced surjection `FreeGroup α →* G` has finitely generated domain. -/
theorem fg [Finite α] (P : Group.Generators G α) : Group.FG G :=
  Group.fg_of_surjective P.lift_surjective

end Group.Generators

/-- A group is finitely generated if and only if it admits a bundled `Group.Generators` with a
finite index type. This is the bridge between the predicate `Group.FG` and the data-carrying
`Group.Generators`, mirroring `Group.isFinitelyPresented_iff_nonempty_presentation`. -/
theorem Group.fg_iff_nonempty_finite_generators :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α), Nonempty (Group.Generators G α) := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_finite]
  constructor
  · rintro ⟨α, hα, φ, hφ⟩
    refine ⟨α, hα, ⟨⟨fun a => φ (FreeGroup.of a), ?_⟩⟩⟩
    have hlift : FreeGroup.lift (fun a => φ (FreeGroup.of a)) = φ := by ext a; simp
    rw [hlift]; exact hφ
  · rintro ⟨α, hα, ⟨P⟩⟩
    exact ⟨α, hα, FreeGroup.lift P.val, P.lift_surjective⟩

/-- A presentation `⟨α | rel⟩` of a group `G`: a generating family `val : α → G` together with a
family of relators `rel : ρ → FreeGroup α` whose normal closure is exactly the kernel of the
induced map `FreeGroup.lift val`. Equivalently (see `Group.Presentation.presentedGroupEquiv`), `G`
is isomorphic to the group presented by these generators and relations. -/
structure Group.Presentation (G : Type*) [Group G] (α ρ : Type*)
    extends Group.Generators G α where
  /-- The relators, as words in the free group on the generators. -/
  rel : ρ → FreeGroup α
  /-- The relators normally generate the kernel of `FreeGroup.lift val`. -/
  ker_eq_normalClosure :
    (FreeGroup.lift val).ker = Subgroup.normalClosure (Set.range rel)

namespace Group.Presentation

variable (P : Group.Presentation G α ρ)

/-- The canonical surjection `FreeGroup α →* G` induced by the generators of the presentation. -/
def lift : FreeGroup α →* G := FreeGroup.lift P.val

/-- The set of relators of the presentation. -/
def relSet : Set (FreeGroup α) := Set.range P.rel

theorem lift_surjective' : Function.Surjective P.lift := P.lift_surjective

@[simp] theorem lift_of (a : α) : P.lift (FreeGroup.of a) = P.val a := by simp [lift]

@[simp] theorem range_lift_eq_top : P.lift.range = ⊤ :=
  MonoidHom.range_eq_top.mpr P.lift_surjective'

theorem rel_mem_relSet (r : ρ) : P.rel r ∈ P.relSet := ⟨r, rfl⟩

/-- The relator set of a presentation with finitely many relators is finite. -/
theorem relSet_finite [Finite ρ] : P.relSet.Finite := Set.finite_range P.rel

theorem ker_lift : P.lift.ker = Subgroup.normalClosure P.relSet := P.ker_eq_normalClosure

/-- Every relator of the presentation maps to `1` in `G`. -/
theorem lift_rel (r : ρ) : P.lift (P.rel r) = 1 := by
  rw [← MonoidHom.mem_ker, ker_lift]
  exact Subgroup.subset_normalClosure (P.rel_mem_relSet r)

/-- A presentation of `G` exhibits `G` as the group presented by its generators and relations. -/
noncomputable def presentedGroupEquiv : PresentedGroup P.relSet ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq P.ker_eq_normalClosure.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective P.lift P.lift_surjective)

@[simp] theorem presentedGroupEquiv_of (a : α) :
    P.presentedGroupEquiv (PresentedGroup.of a) = P.val a := by
  have h : P.presentedGroupEquiv (PresentedGroup.of a) = P.lift (FreeGroup.of a) := rfl
  rw [h, P.lift_of]

end Group.Presentation
