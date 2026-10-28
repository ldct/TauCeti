/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Projection

/-!
# Coordinate complements to subspaces

For any fixed basis, every subspace has a complement spanned by a subset of that basis.
The complementary subset gives a second coordinate summand. Projection onto a coordinate
summand retains precisely its coordinates, even when the other subspace being projected
is not itself a coordinate summand. This supplies the coordinate projections used to form
square minors of differentials in an acyclic based complex.

The construction selects a basis from the images of the given basis in the quotient,
using Mathlib's `exists_linearIndepOn_extension`.
-/

public section

noncomputable section

open Submodule Set

namespace Module.Basis

variable {F V ι : Type*} [AddCommGroup V]

section Field

variable [DivisionRing F] [Module F V]

/-- Every subspace has a complement spanned by a subset of any prescribed basis.
No finite-dimensionality hypothesis is needed. -/
theorem exists_isCompl_span (b : Basis ι F V) (P : Submodule F V) :
    ∃ s : Set ι, IsCompl P (span F (b '' s)) := by
  obtain ⟨s, -, -, hs, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty F (P.mkQ ∘ b)) (empty_subset (univ : Set ι))
  have hspan : span F ((P.mkQ ∘ b) '' s) = ⊤ := by
    apply top_unique
    have htop : span F ((P.mkQ ∘ b) '' univ) = ⊤ := by
      rw [image_univ, range_comp, ← map_span, b.span_eq, Submodule.map_top, P.range_mkQ]
    rw [← htop]
    exact span_le.2 hs
  refine ⟨s, ⟨?_, ?_⟩⟩
  · have hd := Submodule.range_ker_disjoint hli
    have hr : range (fun x : s => b x) = b '' s := by ext; simp
    simpa only [ker_mkQ, hr] using hd.symm
  · rw [codisjoint_iff, ← P.map_mkQ_eq_top, map_span]
    simpa only [image_image, Function.comp_def, id_eq] using hspan

end Field

section Ring

variable [Ring F] [Module F V]

/-- Projection along a coordinate span preserves the coordinates in the complementary subset. -/
@[simp]
theorem repr_projection_span_compl (b : Basis ι F V) (s : Set ι) (x : V) (i : ↑(sᶜ)) :
    b.repr ((span F (b '' sᶜ)).projection (span F (b '' s))
      (b.linearIndependent.isCompl_span_image b.span_eq
        (isCompl_compl (x := s))).symm x) i = b.repr x i := by
  have hz : b.repr ((span F (b '' s)).projection (span F (b '' sᶜ))
      (b.linearIndependent.isCompl_span_image b.span_eq (isCompl_compl (x := s))) x) i = 0 := by
    apply Finsupp.notMem_support_iff.1
    intro hi
    exact i.2 ((b.mem_span_image.1 (Submodule.projection_apply_mem _ _)) hi)
  have h := congrArg (fun v => b.repr v i)
    (Submodule.projection_add_projection_eq_self
      (b.linearIndependent.isCompl_span_image b.span_eq (isCompl_compl (x := s))).symm x)
  simpa only [map_add, Finsupp.add_apply, hz, add_zero] using h

end Ring

end Module.Basis
