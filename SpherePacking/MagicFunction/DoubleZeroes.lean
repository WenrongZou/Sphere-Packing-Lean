/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.IntegralParametrisations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Double zeroes of Laplace transforms

Propositions 2.1 and 2.2 of Feigenbaum–Grabner–Hardin (arXiv:1907.08558), for real `s` and along
the contours of `a'` and `b'`. Here `ψ` is holomorphic on `ℍ`, integrable on `i(0, 1]`, of growth
`O(e^{πσ Im z})` in the strip `|Re z| ≤ 1` (for the contour shift), and on the imaginary axis
`ψ(it) = ∑_{k ≤ n} (a_k + t b_k) e^{2πkt} + O(e^{-Ct})` (as in Viazovska's (39)).
-/

@[expose] public section

open Set Filter MeasureTheory Real Complex MagicFunction.Parametrisations

namespace MagicFunction.DoubleZeroes

/-- `∑_{k ≤ n} (a_k + t b_k) e^{2πkt}`, i.e. `∑_{k ≤ n} (a_k - i z b_k) e^{-2πikz}` at `z = it`. -/
noncomputable def expansion (n : ℕ) (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (a k + t * b k) * cexp (2 * π * k * t)

/-- `∫_{-1}^{i} ψ(z+1) e^{πisz} dz + ∫_{1}^{i} ψ(z-1) e^{πisz} dz - 2 ∫_0^i ψ(z) e^{πisz} dz
  + ∫_i^{i∞} (ψ(z+1) - 2ψ(z) + ψ(z-1)) e^{πisz} dz`. -/
noncomputable def contourSum (ψ : ℂ → ℂ) (s : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..1, I * (ψ (z₁' t + 1) * cexp (π * I * s * z₁' t)))
  + (∫ t in (0 : ℝ)..1, ψ (z₂' t + 1) * cexp (π * I * s * z₂' t))
  + (∫ t in (0 : ℝ)..1, I * (ψ (z₃' t - 1) * cexp (π * I * s * z₃' t)))
  + (∫ t in (0 : ℝ)..1, -1 * (ψ (z₄' t - 1) * cexp (π * I * s * z₄' t)))
  + -2 * (∫ t in (0 : ℝ)..1, I * (ψ (z₅' t) * cexp (π * I * s * z₅' t)))
  + ∫ t in Ici (1 : ℝ),
      I * ((ψ (z₆' t + 1) - 2 * ψ (z₆' t) + ψ (z₆' t - 1)) * cexp (π * I * s * z₆' t))

variable {ψ : ℂ → ℂ} {n : ℕ} {a b : ℕ → ℂ} {σ C s : ℝ}

/-- FGH Proposition 2.1 (Viazovska (40)), for `s > 2n`. -/
theorem integral_eq_sum_add_integral_sub (hψ : DifferentiableOn ℂ ψ {z | 0 < z.im})
    (hint : IntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ioc 0 1)) (hC : 0 < C)
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expansion n a b t) =O[atTop] fun t ↦ rexp (-C * t))
    (hs : 2 * n < s) :
    ∫ t in Ioi (0 : ℝ), I * (ψ (I * t) * cexp (π * I * s * (I * t))) =
      I * ∑ k ∈ Finset.range (n + 1),
          (a k / (π * (s - 2 * k)) + b k / (π ^ 2 * (s - 2 * k) ^ 2)) +
        ∫ t in Ioi (0 : ℝ),
          I * ((ψ (I * t) - expansion n a b t) * cexp (π * I * s * (I * t))) := by
  sorry

/-- FGH Proposition 2.2, for `s > σ`. -/
theorem neg_four_mul_sin_sq_mul_integral_eq (hψ : DifferentiableOn ℂ ψ {z | 0 < z.im})
    (hint : IntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ioc 0 1))
    (hgrowth : ψ =O[comap im atTop ⊓ 𝓟 {z | |z.re| ≤ 1}] fun z ↦ rexp (σ * π * z.im))
    (hs : σ < s) :
    -4 * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), I * (ψ (I * t) * cexp (π * I * s * (I * t))) = contourSum ψ s := by
  sorry

/-- FGH Proposition 2.2, for `s > -C/π`. At `s = 2k` both sides vanish when `b_k = 0`. -/
theorem neg_four_mul_sin_sq_mul_continuation_eq (hψ : DifferentiableOn ℂ ψ {z | 0 < z.im})
    (hint : IntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ioc 0 1))
    (hgrowth : ψ =O[comap im atTop ⊓ 𝓟 {z | |z.re| ≤ 1}] fun z ↦ rexp (σ * π * z.im))
    (hC : 0 < C)
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expansion n a b t) =O[atTop] fun t ↦ rexp (-C * t))
    (hdiff : (fun t : ℝ ↦ ψ (I * t + 1) - 2 * ψ (I * t) + ψ (I * t - 1))
      =O[atTop] fun t ↦ rexp (-C * t))
    (hs : -C / π < s) (hb : ∀ k ∈ Finset.range (n + 1), s = 2 * k → b k = 0) :
    -4 * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      (I * ∑ k ∈ Finset.range (n + 1),
          (a k / (π * (s - 2 * k)) + b k / (π ^ 2 * (s - 2 * k) ^ 2)) +
        ∫ t in Ioi (0 : ℝ),
          I * ((ψ (I * t) - expansion n a b t) * cexp (π * I * s * (I * t)))) =
      contourSum ψ s := by
  sorry

end MagicFunction.DoubleZeroes
