/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Equality

/-!
# Equality in Brunn–Minkowski and volume distributions along a direction

Let `K` and `L` be convex bodies of the same positive volume `V` in a finite-dimensional real
inner product space, and let `0 < θ < 1`. By the Brunn–Minkowski inequality the convex
combination `M = (1 - θ) • K + θ • L` has volume at least `V`. This file shows that if `M` has
volume at most `V`, so that equality holds, then along every unit vector `e` the volume
distributions of `K` and `L` are translates of each other: there is a real number `c` with

`volume {x ∈ L | ⟪e, x⟫ ≤ t + c} = volume {x ∈ K | ⟪e, x⟫ ≤ t}` for every `t : ℝ`.

The quantile transport argument of Kneser and Süss is supplied by
`Convex.exists_quantile_map_inner_cond_eq_add_of_volume_le`. The Galois characterization of
quantiles converts the resulting translation of quantiles into a translation of cumulative
distribution functions, including their endpoint values. Equal total volumes then recover
the unnormalized half-space volumes.

Combined with an identification of centroids, this is the step of the classical proof of
the equality case of the Brunn–Minkowski inequality for convex bodies that compares the bodies
in one direction at a time.

## Main results

* `ConvexBody.exists_forall_volume_sep_inner_le_add_eq`: equality in Brunn–Minkowski for
  convex bodies of equal volume makes their volume distributions along every
  direction translates of each other.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25, for the transport argument and the equality case.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, Section 4, for the one-dimensional transport proof of Brunn–Minkowski.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.1, for the equality case and its history (Kneser and Süss).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Kneser–Süss transport along a direction.** If `K` and `L` are convex bodies of the same
volume and their convex combination `(1 - θ) • K + θ • L` has volume at most that of
`K`, then along every unit vector `e` the volume distributions of `K` and `L` are translates:
the volume of the part of `L` below height `t + c` equals the volume of the part of `K` below
height `t`, for a constant `c` and every `t`. By the Brunn–Minkowski inequality the volume
hypothesis is equivalent to equality. -/
theorem exists_forall_volume_sep_inner_le_add_eq (K L : ConvexBody E)
    (hKL : volume (L : Set E) = volume (K : Set E)) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hM : volume ((1 - θ) • (K : Set E) + θ • (L : Set E)) ≤ volume (K : Set E))
    {e : E} (he : ‖e‖ = 1) :
    ∃ c : ℝ, ∀ t : ℝ,
      volume {x ∈ (L : Set E) | ⟪e, x⟫ ≤ t + c} = volume {x ∈ (K : Set E) | ⟪e, x⟫ ≤ t} := by
  rcases eq_zero_or_pos (volume (K : Set E)) with hK | hK
  · exact ⟨0, fun t ↦ by rw [measure_mono_null (sep_subset _ _) hK,
      measure_mono_null (sep_subset _ _) (hKL.trans hK)]⟩
  have hL : 0 < volume (L : Set E) := hKL ▸ hK
  have hKfin : volume (K : Set E) ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hLfin : volume (L : Set E) ≠ ∞ := L.isCompact.measure_lt_top.ne
  have hvol : volume ((1 - θ) • (K : Set E) + θ • (L : Set E)) ≤
      volume (K : Set E) ^ (1 - θ) * volume (L : Set E) ^ θ := by
    simpa only [hKL, ← ENNReal.rpow_add _ _ hK.ne' hKfin, sub_add_cancel,
      ENNReal.rpow_one] using hM
  obtain ⟨c, hc⟩ := K.convex.exists_quantile_map_inner_cond_eq_add_of_volume_le
    K.isCompact.isBounded K.isCompact.measurableSet hK.ne' L.convex L.isCompact.isBounded
    L.isCompact.measurableSet hL.ne' he hθ₀ hθ₁ hvol
  let μ := (volume[|(K : Set E)]).map fun x ↦ ⟪e, x⟫
  let ν := (volume[|(L : Set E)]).map fun x ↦ ⟪e, x⟫
  refine ⟨c, fun t ↦ ?_⟩
  -- Comparing every interior level also determines the cdf at heights of mass zero or one.
  have hcdf : cdf ν (t + c) = cdf μ t := by
    have hlevels (u : ℝ) (hu₀ : 0 < u) (hu₁ : u < 1) :
        u ≤ cdf ν (t + c) ↔ u ≤ cdf μ t := by
      rw [← ν.quantile_le_iff hu₀ hu₁, ← μ.quantile_le_iff hu₀ hu₁, hc ⟨hu₀, hu₁⟩]
      simp only [μ, add_le_add_iff_right]
    apply le_antisymm
    · by_contra h
      have hlt : cdf μ t < cdf ν (t + c) := lt_of_not_ge h
      obtain ⟨u, hμu, huν⟩ := exists_between hlt
      exact (not_le_of_gt hμu) ((hlevels u ((cdf_nonneg μ t).trans_lt hμu)
        (huν.trans_le (cdf_le_one ν _))).1 huν.le)
    · by_contra h
      have hlt : cdf ν (t + c) < cdf μ t := lt_of_not_ge h
      obtain ⟨u, hνu, huμ⟩ := exists_between hlt
      exact (not_le_of_gt hνu) ((hlevels u ((cdf_nonneg ν _).trans_lt hνu)
        (huμ.trans_le (cdf_le_one μ _))).2 huμ.le)
  have hreal : volume.real {x ∈ (L : Set E) | ⟪e, x⟫ ≤ t + c} =
      volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ t} := by
    rw [TauCeti.cdf_map_inner_cond hL.ne' hLfin,
      TauCeti.cdf_map_inner_cond hK.ne' hKfin] at hcdf
    have hV : volume.real (L : Set E) = volume.real (K : Set E) := by
      simp only [measureReal_def, hKL]
    rw [hV] at hcdf
    exact (div_left_inj' (ENNReal.toReal_pos hK.ne' hKfin).ne').1 hcdf
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top_of_subset (sep_subset _ _) hLfin)
    (measure_ne_top_of_subset (sep_subset _ _) hKfin)).1 hreal

end ConvexBody
