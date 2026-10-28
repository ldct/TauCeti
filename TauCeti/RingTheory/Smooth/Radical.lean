/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Smooth.GeometricallyReduced
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Extension of radical ideals along smooth maps

A radical ideal remains radical after extension along a smooth ring map: its quotient
is a smooth algebra over the reduced original quotient. In particular this applies to
étale coordinate charts of reduced divisors.

This uses `TauCeti.isReduced_of_smooth` and Mathlib's quotient–tensor comparison.
-/

public section

open scoped TensorProduct

namespace RingHom.Smooth

variable {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}

/-- Extension along a smooth ring map preserves radical ideals. -/
theorem isRadical_map (hf : f.Smooth) {I : Ideal R} (hI : I.IsRadical) :
    (I.map f).IsRadical := by
  algebraize [f]
  let _ : IsReduced (R ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  let _ : IsReduced ((R ⧸ I) ⊗[R] S) := TauCeti.isReduced_of_smooth (R ⧸ I) _
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).injective

end RingHom.Smooth
