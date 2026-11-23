/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.b.Schwartz

/-!
# Double zeroes of `b`

For `r > 2`, `b(r) = -4i sin(π r / 2)² ∫₀^∞ ψ_I(it) e^{-π r t} dt`, where `r` is the squared
radius `‖x‖²`.
-/

@[expose] public section

open Set MeasureTheory Real Complex

namespace MagicFunction.b.AnalyticContinuation

theorem integrableOn_ψI'_mul_cexp {r : ℝ} (hr : 2 < r) :
    IntegrableOn (fun t : ℝ ↦ ψI' (I * t) * cexp (-π * r * t)) (Ioi 0) := by
  sorry

theorem b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral {r : ℝ} (hr : 2 < r) :
    MagicFunction.b.RealIntegrals.b' r = -4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * r * t) := by
  sorry

theorem b_eq_neg_four_mul_I_mul_sin_sq_mul_integral {x : EuclideanSpace ℝ (Fin 8)} (hx : √2 < ‖x‖) :
    MagicFunction.FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * ‖x‖ ^ 2 * t) := by
  rw [MagicFunction.FourierEigenfunctions.b_apply,
    b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral (Real.lt_sq_of_sqrt_lt hx)]
  norm_num

end MagicFunction.b.AnalyticContinuation
