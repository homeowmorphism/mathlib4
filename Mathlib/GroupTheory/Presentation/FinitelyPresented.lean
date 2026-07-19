/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Presentation
public import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Finite presentations and the finitely-presented predicate

This file connects the bundled `Group.Presentation` (a presentation carried as data) with the
predicate `Group.IsFinitelyPresented` (which merely asserts that *some* finite presentation exists).

A `Group.Presentation G α ρ` is *finite* when both the generating index `α` and the relator index
`ρ` are finite, expressed via the assumptions `[Finite α] [Finite ρ]`. A finite presentation
witnesses `Group.IsFinitelyPresented G`, and conversely every finitely presented group admits such a
presentation.

## Main results

* `Group.Presentation.ker_isFinitelyNormallyGenerated`: for a presentation with finitely many
  relators, the kernel of the induced map `FreeGroup.lift val` is the normal closure of a finite
  set.
* `Group.Presentation.isFinitelyPresented`: a finite presentation (`[Finite α] [Finite ρ]`) of `G`
  witnesses `Group.IsFinitelyPresented G`.
* `Group.IsFinitelyPresented.exists_nonempty_presentation`: a finitely presented group admits a
  finite bundled presentation.
* `Group.isFinitelyPresented_iff_nonempty_presentation`: the two notions agree — `G` is finitely
  presented iff it has a nonempty `Group.Presentation` with finite `α` and `ρ`.

## Tags

group presentation, finitely presented group, generators and relations
-/

@[expose] public section

variable {G α ρ : Type*} [Group G]

namespace Group.Presentation

/-- For a presentation with finitely many relators, the kernel of the induced map
`FreeGroup.lift val` is the normal closure of a finite set. -/
theorem ker_isFinitelyNormallyGenerated (P : Group.Presentation G α ρ) [Finite ρ] :
    P.lift.ker.IsFinitelyNormallyGenerated :=
  ⟨P.relSet, P.relSet_finite, P.ker_lift.symm⟩

/-- A finite presentation of `G` (finitely many generators and relators) witnesses that `G` is
finitely presented. -/
theorem isFinitelyPresented (P : Group.Presentation G α ρ) [Finite α] [Finite ρ] :
    Group.IsFinitelyPresented G := by
  have : Finite P.relSet := P.relSet_finite.to_subtype
  exact .equiv P.presentedGroupEquiv

end Group.Presentation

/-- A finitely presented group admits a finite bundled presentation: there are finite index types
`α`, `ρ` and a `Group.Presentation G α ρ`. -/
theorem Group.IsFinitelyPresented.exists_nonempty_presentation [Group.IsFinitelyPresented G] :
    ∃ (α ρ : Type) (_ : Finite α) (_ : Finite ρ), Nonempty (Group.Presentation G α ρ) := by
  obtain ⟨n, φ, hφ, S, hS, hSφ⟩ := ‹Group.IsFinitelyPresented G›.out
  have hlift : FreeGroup.lift (fun i => φ (FreeGroup.of i)) = φ := by ext i; simp
  refine ⟨Fin n, ↥S, inferInstance, hS.to_subtype, ⟨?_⟩⟩
  exact
    { val := fun i => φ (FreeGroup.of i)
      lift_surjective := by rw [hlift]; exact hφ
      rel := fun s => (s : FreeGroup (Fin n))
      ker_eq_normalClosure := by
        rw [hlift, ← hSφ]
        congr 1
        exact Subtype.range_coe.symm }

/-- A group is finitely presented if and only if it admits a bundled `Group.Presentation` with
finitely many generators and relators. This is the bridge between the predicate
`Group.IsFinitelyPresented` and the data-carrying `Group.Presentation`. -/
theorem Group.isFinitelyPresented_iff_nonempty_presentation :
    Group.IsFinitelyPresented G ↔
      ∃ (α ρ : Type) (_ : Finite α) (_ : Finite ρ), Nonempty (Group.Presentation G α ρ) := by
  refine ⟨fun _ => Group.IsFinitelyPresented.exists_nonempty_presentation, ?_⟩
  rintro ⟨α, ρ, _, _, ⟨P⟩⟩
  exact P.isFinitelyPresented
