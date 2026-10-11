/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative

/-!
# The identity chain of a standard cube

The identity map of the standard cube `Iⁿ` is its oriented cubical singular chain. Modulo the union
of its codimension-one faces, this chain is a cycle. This is the basic relative model for
fundamental chains of manifolds with corners.

The conventions for singular cubes and their orientation follow Massey, *Singular Homology
Theory*, Chapter II.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

/-- The identity singular cube on the standard cube `Iⁿ = Fin n → I`. -/
def standardSingularCube (n : ℕ) : SingularCube (Fin n → I) n := ContinuousMap.id _

/-- Evaluation of the standard singular cube is the identity. -/
@[simp]
theorem standardSingularCube_apply (n : ℕ) (x : Fin n → I) : standardSingularCube n x = x := (rfl)

/-- The normalized chain of the standard cube's identity singular cube. -/
def standardCubeChain (R : Type*) [Ring R] (n : ℕ) :
    NormalizedCubicalChain (Fin n → I) R n :=
  NormalizedCubicalChain.ofCube _ _ (standardSingularCube n)

/-- The standard cube chain is the class of its identity singular cube. -/
@[simp]
theorem standardCubeChain_def (R : Type*) [Ring R] (n : ℕ) :
    standardCubeChain R n = NormalizedCubicalChain.ofCube _ _ (standardSingularCube n) := (rfl)

/-- The union of the codimension-one faces of the standard cube. -/
def standardCubeBoundary (n : ℕ) : Set (Fin n → I) :=
  {x | ∃ i, x i = 0 ∨ x i = 1}

/-- Membership in the standard cube boundary means that some coordinate is an endpoint. -/
@[simp]
theorem mem_standardCubeBoundary_iff {n : ℕ} (x : Fin n → I) :
    x ∈ standardCubeBoundary n ↔ ∃ i, x i = 0 ∨ x i = 1 := Iff.rfl

/-- The relative class of the standard cube's identity chain modulo its cubical boundary. -/
def standardCubeRelativeChain (R : Type*) [Ring R] (n : ℕ) :
    RelativeCubicalChain (Fin n → I) (standardCubeBoundary n) R n :=
  Submodule.Quotient.mk (standardCubeChain R n)

/-- The standard relative cube chain is represented by the normalized identity chain. -/
@[simp]
theorem standardCubeRelativeChain_def (R : Type*) [Ring R] (n : ℕ) :
    standardCubeRelativeChain R n = Submodule.Quotient.mk (standardCubeChain R n) := (rfl)

private def standardCubeFaceToBoundary {n : ℕ} (i : Fin (n + 1)) (t : I)
    (ht : t = 0 ∨ t = 1) : C(Fin n → I, standardCubeBoundary (n + 1)) :=
  ⟨fun x ↦ ⟨i.insertNth t x, ⟨i, by simp [ht]⟩⟩,
    Continuous.subtype_mk (by fun_prop) _⟩

private theorem standardCubeFace_mem_supportedIn {R : Type*} [Ring R] {n : ℕ}
    (i : Fin (n + 1)) (t : I) (ht : t = 0 ∨ t = 1) :
    NormalizedCubicalChain.ofCube (Fin (n + 1) → I) R
        (SingularCube.face i t (standardSingularCube (n + 1))) ∈
      NormalizedCubicalChain.supportedIn R (standardCubeBoundary (n + 1)) n := by
  rw [NormalizedCubicalChain.supportedIn_def]
  refine ⟨NormalizedCubicalChain.ofCube _ _ (standardCubeFaceToBoundary i t ht), ?_⟩
  rw [NormalizedCubicalChain.map_ofCube]
  congr 1
  ext x
  simp [standardCubeFaceToBoundary, standardSingularCube, SingularCube.face_apply]

/-- The identity cube is a relative cycle modulo its cubical boundary. -/
theorem standardCubeRelativeChain_isCycle (R : Type*) [Ring R] (n : ℕ) :
    RelativeCubicalChain.boundary (Fin (n + 1) → I) R (standardCubeBoundary (n + 1)) n
      (standardCubeRelativeChain R (n + 1)) = 0 := by
  rw [standardCubeRelativeChain_def, RelativeCubicalChain.boundary_mk, standardCubeChain_def,
    NormalizedCubicalChain.boundary_ofCube]
  apply (Submodule.Quotient.mk_eq_zero _).2
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact standardCubeFace_mem_supportedIn i 0 (Or.inl rfl)
  · exact standardCubeFace_mem_supportedIn i 1 (Or.inr rfl)

end TauCeti

end
