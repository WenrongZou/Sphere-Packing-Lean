/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.a.Schwartz

/-!
# Double Zeroes of `a`

This file states the blueprint's Proposition `prop:a-double-zeros`: for `r > √2`,
`a(r) = -4 sin(π r² / 2)² ∫₀^{i∞} φ₀(-1 / z) z² e^{π i r² z} dz`.

Since `sin(π r² / 2)²` vanishes to second order whenever `r² ∈ 2ℤ`, this exhibits the double zeroes
of `a` at all `Λ₈`-vectors of length greater than `√2`.

## Conventions

* As in `MagicFunction.a.RealIntegrals.a'`, the real-variable statement is phrased in terms of the
  *squared* radius `r = ‖x‖²` (the blueprint's `r²`), so the hypothesis `r > √2` of the blueprint
  becomes `2 < r`.
* The contour integral along the imaginary axis from `0` to `i∞` is parametrised by `z = I * t` for
  `t ∈ (0, ∞)`, so that `dz = I * dt`. The integrand `φ₀''(-1 / z) * z ^ 2 * cexp (π * I * r * z)`
  is `MagicFunction.a.ComplexIntegrands.Φ₅' r z`, the same integrand as in the definition of `I₅`.

## Main statements

* `MagicFunction.a.DoubleZeroes.integrableOn_integrand`: the integral converges for `2 < r`.
* `MagicFunction.a.DoubleZeroes.a'_eq_neg_four_mul_sin_sq_mul_integral`: the identity for the
  radial profile `MagicFunction.a.RealIntegrals.a'`.
* `MagicFunction.a.DoubleZeroes.a_eq_neg_four_mul_sin_sq_mul_integral`: the identity for the
  Schwartz function `MagicFunction.FourierEigenfunctions.a` on `ℝ⁸`, in the blueprint's form.
-/

@[expose] public section

open Set Complex Real MeasureTheory

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

namespace MagicFunction.a.DoubleZeroes

/-- For `2 < r` (i.e. radius `> √2`), the contour integral
`∫₀^{i∞} φ₀(-1 / z) z² e^{π i r z} dz`, parametrised by `z = I * t`, converges absolutely. -/
theorem integrableOn_integrand {r : ℝ} (hr : 2 < r) :
    IntegrableOn
      (fun t : ℝ ↦ I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (π * I * r * (I * t)))
      (Ioi 0) := by
  sorry

/-- **Double zeroes of `a`** (blueprint `prop:a-double-zeros`), radial form.

For `2 < r`, where `r` stands for the squared radius `‖x‖²`,
`a'(r) = -4 sin(π r / 2)² ∫₀^{i∞} φ₀(-1 / z) z² e^{π i r z} dz`,
the contour integral being taken along the imaginary axis `z = I * t`, `dz = I * dt`. -/
theorem a'_eq_neg_four_mul_sin_sq_mul_integral {r : ℝ} (hr : 2 < r) :
    MagicFunction.a.RealIntegrals.a' r = -4 * (Real.sin (π * r / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (π * I * r * (I * t)) := by
  sorry

/-- **Double zeroes of `a`** (blueprint `prop:a-double-zeros`).

For `x ∈ ℝ⁸` with `‖x‖ > √2`,
`a(x) = -4 sin(π ‖x‖² / 2)² ∫₀^{i∞} φ₀(-1 / z) z² e^{π i ‖x‖² z} dz`,
the contour integral being taken along the imaginary axis `z = I * t`, `dz = I * dt`. -/
theorem a_eq_neg_four_mul_sin_sq_mul_integral {x : ℝ⁸} (hx : √2 < ‖x‖) :
    MagicFunction.FourierEigenfunctions.a x = -4 * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 *
        cexp (π * I * ‖x‖ ^ 2 * (I * t)) := by
  have hx2 : 2 < ‖x‖ ^ 2 := Real.lt_sq_of_sqrt_lt hx
  change MagicFunction.a.RealIntegrals.a' (‖x‖ ^ 2) = _
  rw [a'_eq_neg_four_mul_sin_sq_mul_integral hx2]
  push_cast
  rfl

end MagicFunction.a.DoubleZeroes
