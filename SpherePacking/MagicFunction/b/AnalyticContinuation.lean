/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.b.Schwartz

/-!
# Double zeroes of `b`

Blueprint `prop:b-double-zeros`: for `r > √2`,
`b(r) = -4i sin(π r² / 2)² ∫₀^∞ ψ_I(it) e^{-π r² t} dt`.
In the radial statements `r` is the squared radius `‖x‖²`, as in `MagicFunction.b.RealIntegrals.b'`.
-/

@[expose] public section

open Set MeasureTheory Real Complex

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

namespace MagicFunction.b.AnalyticContinuation

theorem integrableOn_ψI'_mul_cexp {r : ℝ} (hr : 2 < r) :
    IntegrableOn (fun t : ℝ ↦ ψI' (I * t) * cexp (-π * r * t)) (Ioi 0) := by
  sorry

theorem b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral {r : ℝ} (hr : 2 < r) :
    MagicFunction.b.RealIntegrals.b' r = -4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * r * t) := by
  sorry

theorem b_eq_neg_four_mul_I_mul_sin_sq_mul_integral {x : ℝ⁸} (hx : √2 < ‖x‖) :
    MagicFunction.FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * ‖x‖ ^ 2 * t) := by
  change MagicFunction.b.RealIntegrals.b' (‖x‖ ^ 2) = _
  rw [b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral (Real.lt_sq_of_sqrt_lt hx)]
  push_cast
  rfl

end MagicFunction.b.AnalyticContinuation
