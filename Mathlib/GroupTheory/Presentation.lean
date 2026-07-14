/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

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
* `Group.Presentation G α ρ`: a presentation `⟨α | rel⟩` of `G`, extending `Group.Generators G α`
  with relators `rel : ρ → FreeGroup α` and a proof that their normal closure is the kernel.
* `Group.Presentation.lift`: the induced surjection `FreeGroup α →* G`.
* `Group.Presentation.relSet`: the set of relators, `Set.range rel`.
* `Group.Presentation.presentedGroupEquiv`: the isomorphism `PresentedGroup relSet ≃* G` exhibiting
  `G` as the group presented by `⟨α | rel⟩`.

## Design notes

* A presentation is *finite* exactly when `α` and `ρ` are finite. This is expressed downstream via
  `[Finite α] [Finite ρ]` rather than as a bundled field, keeping the structure minimal.
* TODO: once `IsFinitelyPresented` (`Mathlib/GroupTheory/FinitelyPresentedGroup.lean`) sits in the
  same import graph, add the bridge
  `IsFinitelyPresented G ↔ ∃ (α ρ : Type) (_ : Finite α) (_ : Finite ρ),
    Nonempty (Group.Presentation G α ρ)`.

## Tags

group presentation, generators and relations
-/

@[expose] public section

variable {G α ρ : Type*} [Group G]

/-- A generating family for a group `G` indexed by `α`: the induced homomorphism
`FreeGroup.lift val : FreeGroup α →* G` is surjective. -/
structure Group.Generators (G : Type*) [Group G] (α : Type*) where
  /-- The generators, as elements of `G`. -/
  val : α → G
  /-- The generators generate `G`: the induced map from the free group is surjective. -/
  lift_surjective : Function.Surjective (FreeGroup.lift val)

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

theorem ker_lift : P.lift.ker = Subgroup.normalClosure P.relSet := P.ker_eq_normalClosure

/-- A presentation of `G` exhibits `G` as the group presented by its generators and relations. -/
noncomputable def presentedGroupEquiv : PresentedGroup P.relSet ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq P.ker_eq_normalClosure.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective P.lift P.lift_surjective)

end Group.Presentation
