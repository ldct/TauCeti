/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.Basis.Complement
public import TauCeti.LinearAlgebra.Projection

/-!
# Coordinate splittings of acyclic based complexes

Fix a basis `c i` in each degree of a chain complex. Choose subsets `s i` of the basis
indices so that their spans `D i` complement the kernels of the outgoing differentials.
Write `E i` for the spans of the complementary subsets. For an acyclic complex, the maps

`D (i + 1) → E i`, given by restriction of the differential followed by projection along `D i`,

are isomorphisms. The differential itself need not take `D (i + 1)` into `E i`.
The coordinate formula retains the original differential's entries in the selected rows
and columns. These are the square-minor maps used in computations of based chain torsion.
The coordinate formula follows by simplification with `coordinateDifferential_apply` and
`Module.Basis.repr_projection_span_compl`. No boundedness or finite-dimensionality assumption
is needed for the splitting itself.

The construction uses Mathlib's quotient/complement equivalences and
`Module.Basis.exists_isCompl_span` to choose coordinate complements.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), Section 3.
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
-/

public section

noncomputable section

open CategoryTheory Module Submodule Set

namespace HomologicalComplex

variable {F : Type*} [Ring F] (C : ChainComplex (ModuleCat F) ℤ)
  {ι : ℤ → Type*} (c : ∀ i, Basis (ι i) F (C.X i)) (s : ∀ i, Set (ι i))

/-- The differential restricted to the selected coordinate span in degree `i + 1`, then
projected onto the complementary coordinate span in degree `i` along the selected span. -/
def coordinateDifferential (i : ℤ) :
    span F (c (i + 1) '' s (i + 1)) →ₗ[F] span F (c i '' (s i)ᶜ) :=
  (span F (c i '' (s i)ᶜ)).projectionOnto (span F (c i '' s i))
    ((c i).linearIndependent.isCompl_span_image (c i).span_eq (isCompl_compl (x := s i))).symm ∘ₗ
      (C.d (i + 1) i).hom.domRestrict (span F (c (i + 1) '' s (i + 1)))

/-- The coordinate differential is the composite of the actual differential and the
coordinate projection. -/
@[simp]
theorem coordinateDifferential_apply (i : ℤ) (x : span F (c (i + 1) '' s (i + 1))) :
    C.coordinateDifferential c s i x =
      (span F (c i '' (s i)ᶜ)).projectionOnto (span F (c i '' s i))
        ((c i).linearIndependent.isCompl_span_image (c i).span_eq (isCompl_compl (x := s i))).symm
        ((C.d (i + 1) i).hom x) :=
  (rfl)

variable {C c s}

/-- At an exact degree, the coordinate differential is bijective whenever the selected
spans in the two adjacent degrees complement the outgoing kernels. -/
theorem bijective_coordinateDifferential (i : ℤ) (h : C.ExactAt i)
    (h₁ : IsCompl (LinearMap.ker (C.d (i + 1) i).hom)
      (span F (c (i + 1) '' s (i + 1))))
    (h₀ : IsCompl (LinearMap.ker (C.d i (i - 1)).hom) (span F (c i '' s i))) :
    Function.Bijective (C.coordinateDifferential c s i) := by
  have hr : LinearMap.range (C.d (i + 1) i).hom =
      LinearMap.ker (C.d i (i - 1)).hom := by
    have he := LinearMap.exact_iff.1
      (C.exact_subtype_rangeRestrict (i := i + 1) (j := i) (k := i - 1)
        (by simp) (by simp) h)
    simpa only [LinearMap.ker_rangeRestrict, Submodule.range_subtype] using he.symm
  have hQ : IsCompl (LinearMap.range (C.d (i + 1) i).hom) (span F (c i '' s i)) := by
    rwa [hr]
  let e := (C.d (i + 1) i).hom.projectedEquiv _ _ _ h₁ hQ
    ((c i).linearIndependent.isCompl_span_image (c i).span_eq (isCompl_compl (x := s i))).symm
  have he : (C.coordinateDifferential c s i : _ → _) = e := by
    funext x
    exact ((C.d (i + 1) i).hom.projectedEquiv_apply _ _ _ h₁ hQ _ x).symm
  rw [he]
  exact e.bijective

end HomologicalComplex

namespace HomologicalComplex

variable {F : Type*} [DivisionRing F] (C : ChainComplex (ModuleCat F) ℤ)
  {ι : ℤ → Type*} (c : ∀ i, Basis (ι i) F (C.X i))

/-- An acyclic based complex admits coordinate complements to every outgoing kernel such
that all projected differentials are isomorphisms. The chosen subsets and their complements
refer to the prescribed bases, rather than to newly chosen ambient bases. -/
theorem exists_bijective_coordinateDifferential (h : C.Acyclic) :
    ∃ s : ∀ i, Set (ι i),
      (∀ i, IsCompl (LinearMap.ker (C.d i (i - 1)).hom) (span F (c i '' s i))) ∧
      ∀ i, Function.Bijective (C.coordinateDifferential c s i) := by
  choose s hs using fun i => (c i).exists_isCompl_span
    (LinearMap.ker (C.d i (i - 1)).hom)
  refine ⟨s, hs, fun i => bijective_coordinateDifferential i (h i) ?_ (hs i)⟩
  have hi : (i + 1 : ℤ) - 1 = i := by omega
  have hh := hs (i + 1)
  rw [hi] at hh
  exact hh

end HomologicalComplex
