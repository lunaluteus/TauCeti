/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
public import TauCeti.MeasureTheory.Function.Lp.Dilation
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.MeasureTheory.Function.LpSeminorm.Support

/-!
# Iterated derivative seminorms under linear changes of variables

Composing a vector-valued function with a linear automorphism `e` multiplies the `Lᵖ` seminorm
of its `i`-th derivative by at most `‖e‖ ^ i * |det e|^(-1 / p)`. The estimate compares a set
with its preimage under `e`, works against any additive Haar measure on a finite-dimensional
real normed space, and requires no differentiability of the function. Only the derivative of
the composite must be a.e. strongly measurable on the preimage.
-/

public section

namespace ContinuousLinearEquiv

open MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Under a linear change of variables `e`, the `Lᵖ` seminorm of `Dⁱ(f ∘ e)` on `e ⁻¹' s` is at
most `‖e‖ⁱ |det e|^(-1/p)` times the `Lᵖ` seminorm of `Dⁱf` on `s`, against any additive Haar
measure. The set need not be measurable, and no differentiability of `f` is required. -/
theorem eLpNorm_iteratedFDeriv_comp_right_restrict_preimage_le (e : E ≃L[ℝ] E)
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) {s : Set E} (i : ℕ) (p : ℝ≥0∞)
    (hm : AEStronglyMeasurable (iteratedFDeriv ℝ i (f ∘ e)) (μ.restrict (e ⁻¹' s))) :
    eLpNorm (iteratedFDeriv ℝ i (f ∘ e)) p (μ.restrict (e ⁻¹' s)) ≤
      ENNReal.ofReal (‖(e : E →L[ℝ] E)‖ ^ i) *
        (ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
          eLpNorm (iteratedFDeriv ℝ i f) p (μ.restrict s)) := by
  rw [← Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm
    (ae_of_all _ fun y => e.norm_iteratedFDeriv_comp_right_le f y i) p

end ContinuousLinearEquiv

namespace TauCeti

section EuclideanHessian

open MeasureTheory Metric

/-- The `L²` norm of the second derivative of a `C²` function `w` on a Euclidean space is at most
`volume (closedBall 0 R) ^ (1/2) * (card ι) ^ 2 * B`, when the second derivative of `w` is supported
in the closed ball `closedBall x₀ R` and all its second partial derivatives are bounded by `B`.
Only the second derivative needs to be supported there, so `w` itself may be nonzero outside. -/
theorem toReal_eLpNorm_iteratedFDeriv_two_le_of_support_subset_closedBall
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {w : EuclideanSpace ℝ ι → ℝ} (hw : ContDiff ℝ 2 w)
    {x₀ : EuclideanSpace ℝ ι} {R B : ℝ}
    (hsupp : Function.support (iteratedFDeriv ℝ 2 w) ⊆ closedBall x₀ R)
    (hB : ∀ x i j,
      |fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ B) :
    (eLpNorm (iteratedFDeriv ℝ 2 w) 2 volume).toReal ≤
      (volume (closedBall (0 : EuclideanSpace ℝ ι) R)).toReal ^ (2⁻¹ : ℝ) *
        ((Fintype.card ι : ℝ) ^ 2 * B) := by
  have hB₀ : 0 ≤ B :=
    (abs_nonneg _).trans (hB 0 (Classical.arbitrary ι) (Classical.arbitrary ι))
  have hnorm (x : EuclideanSpace ℝ ι) :
      ‖iteratedFDeriv ℝ 2 w x‖ ≤ (Fintype.card ι : ℝ) ^ 2 * B := by
    refine (iteratedFDeriv ℝ 2 w x).opNorm_le_card_sq_mul_of_norm_apply_le
      (EuclideanSpace.basisFun _ ℝ) (B := B) fun i j => ?_
    simpa [iteratedFDeriv_two_apply] using hB x i j
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
    measure_closedBall_lt_top.ne) ENNReal.ofReal_ne_top) (eLpNorm_le_of_ae_bound_of_support_subset
    (hw.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable hsupp (ae_of_all _ hnorm))).trans
    (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity),
    Measure.addHaar_closedBall_center]
  simp only [ENNReal.toReal_ofNat]

end EuclideanHessian

end TauCeti
