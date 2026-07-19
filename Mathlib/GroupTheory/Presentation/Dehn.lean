/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Presentation
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Finite.List

/-!
# The Dehn function of a group presentation

Building on the bundled `Group.Presentation`, this file defines the *area* of a word that is trivial
in `G` and the *Dehn function* of the presentation.

A word `w : FreeGroup α` is trivial in `G` exactly when `P.lift w = 1`, i.e. when it lies in the
kernel `Subgroup.normalClosure P.relSet`. Such a word can be written as a product of conjugates of
relators and their inverses; the least number of factors needed is its *area*, and the largest area
over all trivial words of length at most `n` is the value `dehn P n` of the Dehn function.

Both `area` and `dehn` take values in `ℕ∞`. The value `⊤` marks the genuinely undefined cases:
`area w = ⊤` for a `w` that is *not* trivial in `G` (no filling exists), and `dehn P n = ⊤` when the
areas of loops of length `≤ n` are unbounded (which cannot happen for a finite presentation). Using
`⊤` rather than a junk `0` keeps the honest value `area 1 = 0` unambiguous.

## Main definitions

* `Group.Presentation.symmRelSet P`: the relators together with their inverses.
* `Group.Presentation.IsFilling P w l`: `l` is a *filling* of `w`, a list of conjugates of relators
  or their inverses whose product is `w`.
* `Group.Presentation.area P w`: the combinatorial area of `w`, in `ℕ∞`, the least length of a
  filling (`⊤` iff `w` is not trivial in `G`).
* `Group.Presentation.dehn P n`: the Dehn function, the supremum of the areas of trivial words of
  length at most `n` (`FreeGroup.norm`), in `ℕ∞`.

## Main statements

* `Group.Presentation.exists_isFilling_iff_mem_ker`: a word has a filling iff it is trivial in `G`.
  This is the bridge that makes `area` meaningful, and the key remaining `sorry`.
* `Group.Presentation.area_le_iff`: `area w ≤ N ↔ ∃ l, P.IsFilling w l ∧ l.length ≤ N`; the defining
  infimum is realised by an actual filling.
* `Group.Presentation.area_lt_top_iff`: `area w < ⊤ ↔ P.lift w = 1`.
* `Group.Presentation.dehn_mono`: the Dehn function is monotone — unconditionally, since `ℕ∞` is a
  complete lattice.
* `Group.Presentation.dehn_lt_top`: for a presentation with a finite generating index
  (`[Finite α]`) the Dehn function is finite at every `n`, since there are only finitely many words
  of bounded norm.

## TODO

* Prove `exists_isFilling_iff_mem_ker` from the product-of-conjugates decomposition of
  `Subgroup.normalClosure`.
-/

@[expose] public section

open scoped Pointwise

namespace Group.Presentation

variable {G α ρ : Type*} [Group G] (P : Group.Presentation G α ρ)

/-- The relators of `P` together with their inverses. -/
def symmRelSet : Set (FreeGroup α) := P.relSet ∪ P.relSet⁻¹

/-- `l` is a *filling* of `w`: a list whose entries are conjugates of relators or their inverses and
whose product is `w`. Its length counts the relator applications used to trivialise `w`. -/
def IsFilling (w : FreeGroup α) (l : List (FreeGroup α)) : Prop :=
  (∀ x ∈ l, x ∈ Group.conjugatesOfSet P.symmRelSet) ∧ l.prod = w

/-- The combinatorial area of `w`, valued in `ℕ∞`: the least length of a filling of `w`, or `⊤` when
`w` has no filling (equivalently, `w` is not trivial in `G`; see `area_lt_top_iff`). -/
noncomputable def area (w : FreeGroup α) : ℕ∞ := ⨅ l : {l // P.IsFilling w l}, (l.1.length : ℕ∞)

/-- The Dehn function of `P`, valued in `ℕ∞`: the supremum of the areas of words that are trivial in
`G` and have length at most `n`. -/
noncomputable def dehn [DecidableEq α] (n : ℕ) : ℕ∞ :=
  ⨆ w ∈ {w | P.lift w = 1 ∧ w.norm ≤ n}, P.area w

variable {P}

/-- Any filling of `w` bounds `area w` from above by its length. -/
theorem area_le_of_isFilling {w : FreeGroup α} {l : List (FreeGroup α)} (h : P.IsFilling w l) :
    P.area w ≤ (l.length : ℕ∞) :=
  iInf_le (fun m : {l // P.IsFilling w l} => (m.1.length : ℕ∞)) ⟨l, h⟩

/-- The empty list is a filling of `1`. -/
theorem isFilling_one : P.IsFilling 1 [] := ⟨by simp, rfl⟩

/-- **Bridge lemma.** A word has a filling exactly when it is trivial in `G`.

The forward direction: a product of conjugates of relators lies in
`Subgroup.normalClosure P.relSet`, which is `P.lift.ker` (`P.ker_lift`). The reverse direction:
every element of the normal closure is a product of conjugates of the generating set and their
inverses. -/
theorem exists_isFilling_iff_mem_ker {w : FreeGroup α} :
    (∃ l, P.IsFilling w l) ↔ P.lift w = 1 := by
  sorry

/-- `area w ≤ N` exactly when `w` has a filling of length at most `N`: the infimum defining `area`
is realised by an actual filling. This is the `ℕ∞`-free handle on `area`, and recovers the
"bounded by `N` relator applications" predicate as `area w ≤ N`. -/
theorem area_le_iff {w : FreeGroup α} {N : ℕ} :
    P.area w ≤ (N : ℕ∞) ↔ ∃ l, P.IsFilling w l ∧ l.length ≤ N := by
  refine ⟨fun h => ?_,
    fun ⟨l, hl, hlN⟩ => (area_le_of_isFilling hl).trans (by exact_mod_cast hlN)⟩
  by_contra hcon
  rw [not_exists] at hcon
  have hlb : ((N : ℕ) + 1 : ℕ∞) ≤ P.area w := by
    rw [area]
    refine le_iInf fun i => ?_
    have hlt : N < i.1.length := not_le.mp fun hle => hcon i.1 ⟨i.2, hle⟩
    exact_mod_cast Nat.succ_le_of_lt hlt
  have hbad : ((N : ℕ) + 1 : ℕ∞) ≤ (N : ℕ∞) := hlb.trans h
  norm_cast at hbad
  omega

@[simp] theorem area_one : P.area 1 = 0 :=
  le_antisymm (by simpa using area_le_of_isFilling isFilling_one) bot_le

/-- If `w` is not trivial in `G`, its area is `⊤`: no filling exists. -/
theorem area_eq_top_of_not_mem_ker {w : FreeGroup α} (hw : P.lift w ≠ 1) : P.area w = ⊤ := by
  have h : ¬ ∃ l, P.IsFilling w l := fun h => hw (exists_isFilling_iff_mem_ker.mp h)
  haveI : IsEmpty {l // P.IsFilling w l} := ⟨fun x => h ⟨x.1, x.2⟩⟩
  exact top_le_iff.mp (le_iInf fun m => isEmptyElim m)

/-- For a trivial word the area is finite. -/
theorem area_lt_top_of_mem_ker {w : FreeGroup α} (hw : P.lift w = 1) : P.area w < ⊤ := by
  obtain ⟨l, hl⟩ := exists_isFilling_iff_mem_ker.mpr hw
  exact (area_le_of_isFilling hl).trans_lt (ENat.coe_lt_top _)

/-- `area w` is finite exactly when `w` is trivial in `G`. -/
theorem area_lt_top_iff {w : FreeGroup α} : P.area w < ⊤ ↔ P.lift w = 1 := by
  refine ⟨fun h => ?_, area_lt_top_of_mem_ker⟩
  by_contra hw
  rw [area_eq_top_of_not_mem_ker hw] at h
  exact lt_irrefl _ h

/-- The Dehn function is monotone. No finiteness hypothesis is needed: `ℕ∞` is a complete lattice,
so the supremum over the larger index set dominates. -/
theorem dehn_mono [DecidableEq α] : Monotone P.dehn := by
  intro m n hmn
  refine iSup₂_le fun w hw => ?_
  exact le_iSup₂_of_le w ⟨hw.1, hw.2.trans hmn⟩ le_rfl

/-- For a finite generating index (`[Finite α]`) the Dehn function is finite at every `n`: there are
only finitely many words of norm at most `n`, and each trivial word has finite area. Like the other
`area`/`dehn` results in this file, this rests on `exists_isFilling_iff_mem_ker` (via
`area_lt_top_of_mem_ker`). -/
theorem dehn_lt_top [DecidableEq α] [Finite α] (n : ℕ) : P.dehn n < ⊤ := by
  have hbig : {w : FreeGroup α | w.norm ≤ n}.Finite := by
    have hpre : {w : FreeGroup α | w.norm ≤ n} = FreeGroup.toWord ⁻¹' {l | l.length ≤ n} := by
      ext w; simp [FreeGroup.norm]
    rw [hpre]
    exact (List.finite_length_le (α × Bool) n).preimage FreeGroup.toWord_injective.injOn
  have hSfin : {w : FreeGroup α | P.lift w = 1 ∧ w.norm ≤ n}.Finite :=
    hbig.subset fun w hw => hw.2
  have hconv : P.dehn n = hSfin.toFinset.sup P.area := by
    change ⨆ w ∈ {w : FreeGroup α | P.lift w = 1 ∧ w.norm ≤ n}, P.area w = _
    rw [Finset.sup_eq_iSup]
    simp only [Set.Finite.mem_toFinset]
  rw [hconv, Finset.sup_lt_iff bot_lt_top]
  intro w hw
  rw [Set.Finite.mem_toFinset] at hw
  exact area_lt_top_of_mem_ker hw.1

end Group.Presentation
