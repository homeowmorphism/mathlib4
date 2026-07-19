/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Presentation
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# The word metric of a generating family

Given a generating family `P : Group.Generators G α` (so the induced map
`FreeGroup.lift P.val : FreeGroup α →* G` is surjective), every element of `G` is the image of some
word in the generators and their inverses. This file defines the **word length** of an element —
the length of a shortest such word — and the associated left-invariant **word metric** on `G`.

Because `FreeGroup α` already contains formal inverses, the length of a reduced free-group word
(`FreeGroup.norm`) counts both generators and their inverses; minimising it over all words that map
to a given `g : G` yields the usual word length with respect to the symmetric generating set
`Set.range P.val ∪ (Set.range P.val)⁻¹`.

## Main definitions

* `Group.Generators.wordLength P g`: the word length of `g`, the least `FreeGroup.norm` of a word
  `w : FreeGroup α` with `FreeGroup.lift P.val w = g`.
* `Group.Generators.wordDist P g h`: the word metric, `wordLength P (g⁻¹ * h)`.

## Main statements

* `Group.Generators.wordLength_spec`: the infimum defining `wordLength` is attained by some word.
* `Group.Generators.wordLength_eq_zero`: `wordLength P g = 0 ↔ g = 1`.
* `Group.Generators.wordLength_inv`, `Group.Generators.wordLength_mul_le`: the word length is
  symmetric under inversion and subadditive under multiplication.
* `Group.Generators.wordDist_self`, `Group.Generators.wordDist_eq_zero`,
  `Group.Generators.wordDist_comm`, `Group.Generators.wordDist_triangle`: the word distance is a
  genuine metric (valued in `ℕ`).
* `Group.Generators.wordDist_mul_left`: the word metric is left-invariant.

## Design notes

* `wordLength` and `wordDist` are `ℕ`-valued. Turning `wordDist` into a bundled `MetricSpace G`
  requires a choice of generators and a cast to `ℝ`, so it is deliberately *not* provided as an
  instance; a `def` producing such a metric space is left as future work.
* Everything requires `[DecidableEq α]`, inherited from `FreeGroup.norm`.

## Tags

word metric, word length, generating set, geometric group theory
-/

@[expose] public section

namespace Group.Generators

variable {G α : Type*} [Group G] (P : Group.Generators G α)

section WordLength

variable [DecidableEq α]

/-- The word length of `g : G` with respect to the generating family `P`: the least length
(`FreeGroup.norm`) of a word `w : FreeGroup α` in the generators and their inverses with
`FreeGroup.lift P.val w = g`. -/
noncomputable def wordLength (g : G) : ℕ :=
  sInf (FreeGroup.norm '' {w : FreeGroup α | FreeGroup.lift P.val w = g})

variable {P}

/-- Any word representing `g` bounds its word length from above: this is the defining lower bound of
`wordLength` as an infimum. -/
theorem wordLength_le {g : G} {w : FreeGroup α} (h : FreeGroup.lift P.val w = g) :
    P.wordLength g ≤ FreeGroup.norm w :=
  Nat.sInf_le ⟨w, h, rfl⟩

variable (P) in
/-- The infimum defining `wordLength` is attained: some word of minimal length represents `g`.
Existence relies on surjectivity of `FreeGroup.lift P.val`. -/
theorem wordLength_spec (g : G) :
    ∃ w : FreeGroup α, FreeGroup.lift P.val w = g ∧ FreeGroup.norm w = P.wordLength g := by
  obtain ⟨w₀, hw₀⟩ := P.lift_surjective g
  obtain ⟨w, hw, hnorm⟩ :=
    Nat.sInf_mem (s := FreeGroup.norm '' {w : FreeGroup α | FreeGroup.lift P.val w = g})
      ⟨FreeGroup.norm w₀, w₀, hw₀, rfl⟩
  exact ⟨w, hw, hnorm⟩

@[simp] theorem wordLength_eq_zero {g : G} : P.wordLength g = 0 ↔ g = 1 := by
  rw [wordLength, Nat.sInf_eq_zero]
  constructor
  · rintro (⟨w, hw, hw0⟩ | h)
    · rw [FreeGroup.norm_eq_zero] at hw0
      rw [← hw, hw0, map_one]
    · obtain ⟨w₀, hw₀⟩ := P.lift_surjective g
      exact absurd h (Set.Nonempty.ne_empty ⟨FreeGroup.norm w₀, w₀, hw₀, rfl⟩)
  · rintro rfl
    exact Or.inl ⟨1, map_one _, FreeGroup.norm_one⟩

@[simp] theorem wordLength_one : P.wordLength (1 : G) = 0 :=
  wordLength_eq_zero.mpr rfl

/-- The word length is invariant under inversion. -/
@[simp] theorem wordLength_inv (g : G) : P.wordLength g⁻¹ = P.wordLength g := by
  have key : ∀ x : G, P.wordLength x⁻¹ ≤ P.wordLength x := fun x => by
    obtain ⟨w, hw, hnorm⟩ := P.wordLength_spec x
    calc P.wordLength x⁻¹ ≤ FreeGroup.norm w⁻¹ := wordLength_le (by rw [map_inv, hw])
      _ = FreeGroup.norm w := FreeGroup.norm_inv_eq
      _ = P.wordLength x := hnorm
  exact le_antisymm (key g) (by simpa using key g⁻¹)

/-- The word length is subadditive: `wordLength (g * h) ≤ wordLength g + wordLength h`. This is the
triangle inequality underlying the word metric. -/
theorem wordLength_mul_le (g h : G) :
    P.wordLength (g * h) ≤ P.wordLength g + P.wordLength h := by
  obtain ⟨w, hw, hnw⟩ := P.wordLength_spec g
  obtain ⟨v, hv, hnv⟩ := P.wordLength_spec h
  calc P.wordLength (g * h) ≤ FreeGroup.norm (w * v) := wordLength_le (by rw [map_mul, hw, hv])
    _ ≤ FreeGroup.norm w + FreeGroup.norm v := FreeGroup.norm_mul_le w v
    _ = P.wordLength g + P.wordLength h := by rw [hnw, hnv]

/-- Each generator has word length at most `1`. -/
theorem wordLength_val_le_one (a : α) : P.wordLength (P.val a) ≤ 1 := by
  have h : P.wordLength (P.val a) ≤ FreeGroup.norm (FreeGroup.of a) := wordLength_le (by simp)
  simpa using h

end WordLength

section WordDist

variable [DecidableEq α]

/-- The word metric of the generating family `P`: the word length of `g⁻¹ * h`, i.e. the length of a
shortest word in the generators and their inverses that takes `g` to `h`. -/
noncomputable def wordDist (g h : G) : ℕ := P.wordLength (g⁻¹ * h)

variable {P}

@[simp] theorem wordDist_self (g : G) : P.wordDist g g = 0 := by
  rw [wordDist, inv_mul_cancel, wordLength_one]

@[simp] theorem wordDist_eq_zero {g h : G} : P.wordDist g h = 0 ↔ g = h := by
  rw [wordDist, wordLength_eq_zero, inv_mul_eq_one]

theorem wordDist_comm (g h : G) : P.wordDist g h = P.wordDist h g := by
  rw [wordDist, wordDist, ← wordLength_inv (P := P) (g⁻¹ * h), mul_inv_rev, inv_inv]

/-- The word metric is left-invariant: translating both points by `x` leaves the distance
unchanged. -/
@[simp] theorem wordDist_mul_left (x g h : G) : P.wordDist (x * g) (x * h) = P.wordDist g h := by
  rw [wordDist, wordDist, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- The triangle inequality for the word metric. -/
theorem wordDist_triangle (g h k : G) :
    P.wordDist g k ≤ P.wordDist g h + P.wordDist h k := by
  have hsplit : g⁻¹ * k = g⁻¹ * h * (h⁻¹ * k) := by rw [mul_assoc, mul_inv_cancel_left]
  rw [wordDist, wordDist, wordDist, hsplit]
  exact wordLength_mul_le _ _

end WordDist

end Group.Generators
