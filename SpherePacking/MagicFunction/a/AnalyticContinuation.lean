/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.a.DoubleZeroes

/-!
# Another integral representation of `a`

This file states the blueprint's Proposition `prop:a-another-integral`: for `r ≥ 0`,
`a(r) = 4i sin(π r² / 2)² (36 / (π³ (r² - 2)) - 8640 / (π³ r⁴) + 18144 / (π³ r²)
  + ∫₀^∞ (t² φ₀(i / t) - 36 / π² e^{2πt} + 8640 / π t - 18144 / π²) e^{-π r² t} dt)`,
and the integral converges absolutely for all `r ≥ 0`.

The blueprint proves it for `r > √2` from `prop:a-double-zeros`
(`MagicFunction.a.DoubleZeroes.a'_eq_neg_four_mul_sin_sq_mul_integral`) and extends it to
`[0, ∞)` by analytic continuation. It is used to compute the special value `a(0)`.

## Conventions

* As in `MagicFunction.a.RealIntegrals.a'`, the real-variable statements use the *squared*
  radius `r = ‖x‖²` (the blueprint's `r²`).
* The singular terms at `r = 0` and `r = √2` are removable singularities of the right-hand side,
  so the blueprint's identity there is to be read as a limit. In Lean `x / 0 = 0`, so:
  - at `r = 0` the literal right-hand side is `0 ≠ a(0)`; the identity is therefore stated for
    `0 < r`, and the value `a(0)` is `MagicFunction.a.SpecialValues.a_zero`;
  - at `r = 2` (radius `√2`) both sides vanish (`sin π = 0` and `a(√2) = 0`), so the literal
    statement remains true there.

## Main statements

* `MagicFunction.a.AnalyticContinuation.integrableOn_another_integrand`: the integral converges
  absolutely for `0 ≤ r`.
* `MagicFunction.a.AnalyticContinuation.a'_eq_another_integral`: the identity for the radial
  profile `MagicFunction.a.RealIntegrals.a'`.
* `MagicFunction.a.AnalyticContinuation.a_eq_another_integral`: the identity for the Schwartz
  function `MagicFunction.FourierEigenfunctions.a` on `ℝ⁸`, in the blueprint's form.
-/

@[expose] public section

open Set MeasureTheory Real Complex

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

namespace MagicFunction.a.AnalyticContinuation

/-- The integral in blueprint `prop:a-another-integral` converges absolutely for every `r ≥ 0`
(here `r` is the squared radius). -/
theorem integrableOn_another_integrand {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn
      (fun t : ℝ ↦ (t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * cexp (2 * π * t) + 8640 / π * t
        - 18144 / π ^ 2) * cexp (-π * r * t))
      (Ioi 0) := by
  sorry

/-- **Another integral representation of `a`** (blueprint `prop:a-another-integral`), radial
form. For `0 < r`, where `r` stands for the squared radius `‖x‖²`,
`a'(r) = 4i sin(π r / 2)² (36 / (π³ (r - 2)) - 8640 / (π³ r²) + 18144 / (π³ r)
  + ∫₀^∞ (t² φ₀(i / t) - 36 / π² e^{2πt} + 8640 / π t - 18144 / π²) e^{-π r t} dt)`. -/
theorem a'_eq_another_integral {r : ℝ} (hr : 0 < r) :
    MagicFunction.a.RealIntegrals.a' r = 4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
      (36 / (π ^ 3 * (r - 2)) - 8640 / (π ^ 3 * r ^ 2) + 18144 / (π ^ 3 * r) +
        ∫ t in Ioi (0 : ℝ), (t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * cexp (2 * π * t) +
          8640 / π * t - 18144 / π ^ 2) * cexp (-π * r * t)) := by
  sorry

/-- **Another integral representation of `a`** (blueprint `prop:a-another-integral`).
For `x ∈ ℝ⁸` with `x ≠ 0`,
`a(x) = 4i sin(π ‖x‖² / 2)² (36 / (π³ (‖x‖² - 2)) - 8640 / (π³ ‖x‖⁴) + 18144 / (π³ ‖x‖²)
  + ∫₀^∞ (t² φ₀(i / t) - 36 / π² e^{2πt} + 8640 / π t - 18144 / π²) e^{-π ‖x‖² t} dt)`. -/
theorem a_eq_another_integral {x : ℝ⁸} (hx : x ≠ 0) :
    MagicFunction.FourierEigenfunctions.a x = 4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      (36 / (π ^ 3 * (‖x‖ ^ 2 - 2)) - 8640 / (π ^ 3 * ‖x‖ ^ 4) + 18144 / (π ^ 3 * ‖x‖ ^ 2) +
        ∫ t in Ioi (0 : ℝ), (t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * cexp (2 * π * t) +
          8640 / π * t - 18144 / π ^ 2) * cexp (-π * ‖x‖ ^ 2 * t)) := by
  have hx2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  change MagicFunction.a.RealIntegrals.a' (‖x‖ ^ 2) = _
  rw [a'_eq_another_integral hx2]
  push_cast
  ring_nf

end MagicFunction.a.AnalyticContinuation
