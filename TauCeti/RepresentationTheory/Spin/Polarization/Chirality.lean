/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock
-- Private: the involution eigenspaces, the orthonormal-frame orthogonality and the half-spin
-- dimensions are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.RepresentationTheory.Spin.Dimension

/-!
# Chirality of the Fock module

Let `V` be an oriented real inner product space of even dimension `n = 2ℓ`, `Q v = -‖v‖²`, and
`J` an orthogonal complex structure on `V`. The `i`-eigenspace `W` of the complexified `J`
polarizes `Q.baseChange ℂ`, and the normalized Fock action
`c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))` makes the exterior algebra `⋀ W` a module over the
complexified Clifford algebra (`TauCeti.AlmostComplexStructure.fockAction`). This is the native
model of the complex spinor module of `V`.

On the other hand, the orientation of `V` defines the normalized complex volume element
`Γ = i ^ ℓ c(e₁) ⋯ c(e₂ₗ)` (`CliffordAlgebra.complexVolume`), whose `±1` eigenspaces are the
half-spinors `S±` of the geometric model. This file compares the two when the orientation is the
one induced by `J`, that is, when some positively oriented orthonormal basis has the form
`(u₁, J u₁, …, uₗ, J uₗ)`: then **`Γ` acts on `⋀ W` by exterior parity**, the grade involution of
the exterior algebra. Consequently the positive half-spinors are the even forms, which contain the
vacuum `1`, the negative half-spinors are the odd forms, and for `ℓ ≥ 1` both have complex
dimension `2 ^ (ℓ - 1)`. In rank zero `Γ = 1` acts as the identity on `⋀ W = ℂ`, which is again
exterior parity.

In dimension four the chirality element `Γ = -c(e₁) c(e₂) c(e₃) c(e₄)` of
`CliffordAlgebra.chirality` is a real element of the Clifford algebra whose complexification is
`CliffordAlgebra.complexVolume` (`CliffordAlgebra.ofBaseChangeAux_chirality`). The second part of
this file specializes the comparison to the real Fock action
`TauCeti.AlmostComplexStructure.realFockAction` of that element. Every orthogonal complex
structure on a four-space admits an adapted basis
(`TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`), so one of the two orientations
of `V` is always of this kind.

## Main results

* `TauCeti.AlmostComplexStructure.fockAction_complexVolume`: for the orientation induced by `J`,
  `Γ` acts on `⋀ W` by the grade involution `CliffordAlgebra.involute`.
* `TauCeti.AlmostComplexStructure.eigenspace_fockAction_complexVolume_one` and
  `TauCeti.AlmostComplexStructure.eigenspace_fockAction_complexVolume_neg_one`: the `+1` and `-1`
  eigenspaces of `Γ` are the even and odd half-spin summands `TauCeti.spinPlus` and
  `TauCeti.spinMinus`.
* `TauCeti.AlmostComplexStructure.finrank_eigenspace_fockAction_complexVolume_one` and
  `TauCeti.AlmostComplexStructure.finrank_eigenspace_fockAction_complexVolume_neg_one`: in
  positive even dimension `n` both half-spinor spaces have complex dimension `2 ^ (n / 2 - 1)`.
* `TauCeti.AlmostComplexStructure.realFockAction_chirality`,
  `TauCeti.AlmostComplexStructure.positiveHalfSpinors_realFockAction` and
  `TauCeti.AlmostComplexStructure.eigenspace_realFockAction_chirality_neg_one`: the same for the
  real chirality element of an oriented four-space, whose half-spinor spaces have complex
  dimension two.

## Implementation notes

The vacuum is fixed by `Γ` because `c(u) c(J u) 1 = i Q(u) 1 = -i 1` for every unit vector `u`, so
the `ℓ` pairs of the adapted basis contribute `(-i) ^ ℓ`, which cancels the normalization `i ^ ℓ`.
The identity then propagates along exterior multiplication: a vector of `W` acts by `√2` times
exterior multiplication and anticommutes with `Γ`, as every complex vector does in even
dimension.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Module
open scoped RealInnerProductSpace TensorProduct

/-! ### The normalized complex volume element in even dimension -/

section ComplexVolume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v)
  (hQnd : Q.Nondegenerate)

/-- In even dimension `Γ` anticommutes with exterior multiplication by a vector of `W`. -/
private theorem fockAction_complexVolume_ι_mul (hn : Even n)
    (x : (J.spinPolarizationData hQJ hQnd).W)
    (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    J.fockAction hQJ hQnd (complexVolume Q o) (ExteriorAlgebra.ι ℂ x * s) =
      -(ExteriorAlgebra.ι ℂ x * J.fockAction hQJ hQnd (complexVolume Q o) s) := by
  have h := congr(J.fockAction hQJ hQnd $(complexVolume_mul_ι_of_even o hn (x : ℂ ⊗[ℝ] V)) s)
  simp only [map_mul, map_neg, Module.End.mul_apply, LinearMap.neg_apply,
    J.fockAction_ι_coe_W hQJ hQnd, LinearMap.smul_apply, SpinPolarizationData.wedge_apply,
    map_smul, ← smul_neg] at h
  exact smul_right_injective _ (r := (Real.sqrt 2 : ℂ)) (by norm_num) h

include hQ in
/-- **`Γ` fixes the vacuum** of the Fock module, for the orientation of an adapted basis
`(u₁, J u₁, …, uₗ, J uₗ)`. -/
private theorem fockAction_complexVolume_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (i : ℕ) (hi : 2 * i + 1 < n), b ⟨2 * i + 1, hi⟩ = J (b ⟨2 * i, by omega⟩))
    (hn : Even n) :
    J.fockAction hQJ hQnd (complexVolume Q o) 1 = 1 := by
  obtain ⟨ℓ, rfl⟩ := hn.two_dvd
  set c : V → Module.End ℂ (ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :=
    fun v ↦ J.fockAction hQJ hQnd (ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v))
  -- Each pair `c(u) c(J u)` of the adapted basis multiplies the vacuum by `i Q(u) = -i`.
  have hpair (k : Fin ℓ) :
      (c (b ⟨2 * k, by omega⟩) * c (J (b ⟨2 * k, by omega⟩))) 1 = (-Complex.I) • 1 := by
    have h := J.realFockAction_ι_mul_ι_apply_apply_one hQJ hQnd (b ⟨2 * k, by omega⟩)
    rw [realFockAction_apply, map_mul, ofBaseChangeAux_ι, ofBaseChangeAux_ι, hQ,
      b.orthonormal.1] at h
    simpa [c] using h
  -- Group the ordered product `c(e₁) ⋯ c(e₂ₗ)` into these `ℓ` pairs.
  have hprod : J.fockAction hQJ hQnd
      (((List.finRange (2 * ℓ)).map b).map fun v ↦ ι (Q.baseChange ℂ) ((1 : ℂ) ⊗ₜ v)).prod =
        (List.ofFn fun k : Fin ℓ ↦
          c (b ⟨2 * k, by omega⟩) * c (J (b ⟨2 * k, by omega⟩))).prod := by
    rw [map_list_prod, List.map_map, List.map_map, ← List.ofFn_eq_map, List.ofFn_mul',
      List.prod_flatten, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k ↦ ?_)
    simp [c, hbJ]
  -- A product of `m` operators each multiplying the vacuum by `-i` multiplies it by `(-i) ^ m`.
  have hpow : ∀ (m : ℕ)
      (T : Fin m → Module.End ℂ (ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W)),
      (∀ k, T k 1 = (-Complex.I) • 1) → (List.ofFn T).prod 1 = (-Complex.I) ^ m • 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro T hT
      rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, ih _ fun k ↦ hT k.succ, map_smul,
        hT, smul_smul, pow_succ]
  rw [complexVolume_eq o b hb (b.isOrthoᵢ_associated hQ), map_smul, LinearMap.smul_apply, hprod,
    hpow ℓ _ hpair, smul_smul, (by omega : (2 * ℓ + 1) / 2 = ℓ), ← mul_pow, mul_neg,
    Complex.I_mul_I, neg_neg, one_pow, one_smul]

include hQ in
/-- **Chirality is exterior parity on the Fock module.** If the orientation of `V` is induced by
`J`, in the sense that some positively oriented orthonormal basis has the form
`(u₁, J u₁, …, uₗ, J uₗ)`, then the normalized complex volume element `Γ` acts on `⋀ W` by the
grade involution. -/
theorem fockAction_complexVolume (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (i : ℕ) (hi : 2 * i + 1 < n), b ⟨2 * i + 1, hi⟩ = J (b ⟨2 * i, by omega⟩))
    (hn : Even n) :
    J.fockAction hQJ hQnd (complexVolume Q o) = involute.toLinearMap := by
  refine LinearMap.ext fun s ↦ ?_
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one, J.fockAction_complexVolume_one o hQ hQJ hQnd b hb hbJ hn]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul x m hx => simp [J.fockAction_complexVolume_ι_mul o hQJ hQnd hn, hx]

include hQ in
/-- **The positive half-spinors of the Fock module are the even forms**: for the orientation
induced by `J`, the `+1` eigenspace of `Γ` is `S⁺ = ⋀ᵉᵛᵉⁿ W`. -/
theorem eigenspace_fockAction_complexVolume_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (i : ℕ) (hi : 2 * i + 1 < n), b ⟨2 * i + 1, hi⟩ = J (b ⟨2 * i, by omega⟩))
    (hn : Even n) :
    Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) 1 =
      spinPlus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [Module.End.mem_eigenspace_iff, J.fockAction_complexVolume o hQ hQJ hQnd b hb hbJ hn,
    AlgHom.toLinearMap_apply, one_smul, involute_eq_self_iff, mem_spinPlus]

include hQ in
/-- **The negative half-spinors of the Fock module are the odd forms**: for the orientation
induced by `J`, the `-1` eigenspace of `Γ` is `S⁻ = ⋀ᵒᵈᵈ W`. -/
theorem eigenspace_fockAction_complexVolume_neg_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (i : ℕ) (hi : 2 * i + 1 < n), b ⟨2 * i + 1, hi⟩ = J (b ⟨2 * i, by omega⟩))
    (hn : Even n) :
    Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) (-1) =
      spinMinus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [Module.End.mem_eigenspace_iff, J.fockAction_complexVolume o hQ hQJ hQnd b hb hbJ hn,
    AlgHom.toLinearMap_apply, neg_one_smul, involute_eq_neg_iff, mem_spinMinus]

/-- In even dimension `n`, the isotropic summand `W` of a complex structure has complex dimension
`n / 2`. -/
private theorem finrank_spinPolarizationData_W (hn : Even n) :
    finrank ℂ (J.spinPolarizationData hQJ hQnd).W = n / 2 :=
  (J.spinPolarizationData hQJ hQnd).finrank_W_eq_of_finrank_eq_two_mul
    (by rw [finrank_baseChange, Fact.out (p := finrank ℝ V = n), Nat.two_mul_div_two_of_even hn])

/-- In positive even dimension, the isotropic summand `W` of a complex structure is nonzero. -/
private theorem spinPolarizationData_W_ne_bot (hn : Even n) (hn₀ : n ≠ 0) :
    (J.spinPolarizationData hQJ hQnd).W ≠ ⊥ := by
  intro h
  have h₂ := J.finrank_spinPolarizationData_W hQJ hQnd hn
  rw [h, finrank_bot] at h₂
  obtain ⟨ℓ, rfl⟩ := hn.two_dvd
  omega

include hQ in
/-- In positive even dimension `n`, the positive half-spinors of the Fock module have complex
dimension `2 ^ (n / 2 - 1)`. -/
theorem finrank_eigenspace_fockAction_complexVolume_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (i : ℕ) (hi : 2 * i + 1 < n), b ⟨2 * i + 1, hi⟩ = J (b ⟨2 * i, by omega⟩))
    (hn : Even n) (hn₀ : n ≠ 0) :
    finrank ℂ (Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) 1) =
      2 ^ (n / 2 - 1) := by
  rw [J.eigenspace_fockAction_complexVolume_one o hQ hQJ hQnd b hb hbJ hn,
    finrank_spinPlus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd hn hn₀),
    J.finrank_spinPolarizationData_W hQJ hQnd hn]

include hQ in
/-- In positive even dimension `n`, the negative half-spinors of the Fock module have complex
dimension `2 ^ (n / 2 - 1)`. -/
theorem finrank_eigenspace_fockAction_complexVolume_neg_one (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o)
    (hbJ : ∀ (i : ℕ) (hi : 2 * i + 1 < n), b ⟨2 * i + 1, hi⟩ = J (b ⟨2 * i, by omega⟩))
    (hn : Even n) (hn₀ : n ≠ 0) :
    finrank ℂ (Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) (-1)) =
      2 ^ (n / 2 - 1) := by
  rw [J.eigenspace_fockAction_complexVolume_neg_one o hQ hQJ hQnd b hb hbJ hn,
    finrank_spinMinus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd hn hn₀),
    J.finrank_spinPolarizationData_W hQJ hQnd hn]

end ComplexVolume

/-! ### The chirality element of an oriented four-space -/

section Four

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- In the real Fock action the chirality element acts by the normalized complex volume
element. -/
private theorem realFockAction_chirality_eq_fockAction :
    J.realFockAction hQJ hQnd (chirality Q o) = J.fockAction hQJ hQnd (complexVolume Q o) := by
  rw [realFockAction_apply, ofBaseChangeAux_chirality]

/-- The positive half-spinors of the real Fock action are the `+1` eigenspace of the normalized
complex volume element. -/
private theorem positiveHalfSpinors_realFockAction_eq_eigenspace :
    positiveHalfSpinors o (J.realFockAction hQJ hQnd) =
      Module.End.eigenspace (J.fockAction hQJ hQnd (complexVolume Q o)) 1 := by
  ext s
  rw [mem_positiveHalfSpinors, Module.End.mem_eigenspace_iff, one_smul,
    realFockAction_chirality_eq_fockAction]

omit [Fact (finrank ℝ V = 4)] in
/-- An adapted basis `(u₁, J u₁, u₂, J u₂)` of the four-space pairs each even-indexed vector with
its image under `J`. -/
private theorem adapted_of_four {b : OrthonormalBasis (Fin 4) ℝ V} (hb₁ : b 1 = J (b 0))
    (hb₃ : b 3 = J (b 2)) (i : ℕ) (hi : 2 * i + 1 < 4) :
    b ⟨2 * i + 1, hi⟩ = J (b ⟨2 * i, by omega⟩) := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  exacts [hb₁, hb₃]

include hQ in
/-- **Chirality is exterior parity on the Fock module.** If the orientation of `V` is induced by
`J`, in the sense that some positively oriented orthonormal basis has the form
`(u₁, J u₁, u₂, J u₂)`, then the chirality element `Γ` acts on `⋀ W` by the grade involution. -/
theorem realFockAction_chirality (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    J.realFockAction hQJ hQnd (chirality Q o) = involute.toLinearMap := by
  rw [realFockAction_chirality_eq_fockAction]
  exact J.fockAction_complexVolume o hQ hQJ hQnd b hb (J.adapted_of_four hb₁ hb₃) (by decide)

include hQ in
/-- **The positive half-spinors of the Fock module are the even forms** `⋀⁰ W ⊕ ⋀² W`, for the
orientation induced by `J`. -/
theorem positiveHalfSpinors_realFockAction (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    positiveHalfSpinors o (J.realFockAction hQJ hQnd) =
      spinPlus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  rw [positiveHalfSpinors_realFockAction_eq_eigenspace]
  exact J.eigenspace_fockAction_complexVolume_one o hQ hQJ hQnd b hb (J.adapted_of_four hb₁ hb₃)
    (by decide)

include hQ in
/-- **The negative half-spinors of the Fock module are the odd forms** `⋀¹ W`, for the
orientation induced by `J`. -/
theorem eigenspace_realFockAction_chirality_neg_one (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    Module.End.eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) (-1) =
      spinMinus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  rw [realFockAction_chirality_eq_fockAction]
  exact J.eigenspace_fockAction_complexVolume_neg_one o hQ hQJ hQnd b hb
    (J.adapted_of_four hb₁ hb₃) (by decide)

include hQ in
/-- The positive half-spinors of the Fock module have complex dimension two. -/
theorem finrank_positiveHalfSpinors_realFockAction (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    finrank ℂ (positiveHalfSpinors o (J.realFockAction hQJ hQnd)) = 2 := by
  rw [positiveHalfSpinors_realFockAction_eq_eigenspace]
  exact J.finrank_eigenspace_fockAction_complexVolume_one o hQ hQJ hQnd b hb
    (J.adapted_of_four hb₁ hb₃) (by decide) (by decide)

include hQ in
/-- The negative half-spinors of the Fock module have complex dimension two. -/
theorem finrank_eigenspace_realFockAction_chirality_neg_one (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    finrank ℂ (Module.End.eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) (-1)) = 2 := by
  rw [realFockAction_chirality_eq_fockAction]
  exact J.finrank_eigenspace_fockAction_complexVolume_neg_one o hQ hQJ hQnd b hb
    (J.adapted_of_four hb₁ hb₃) (by decide) (by decide)

end Four

end TauCeti.AlmostComplexStructure
