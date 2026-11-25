/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.DoubleZeroes
public import SpherePacking.MagicFunction.b.Schwartz

/-!
# Double zeroes of `b`

For `r > 2`, `b(r) = -4i sin(π r / 2)² ∫₀^∞ ψ_I(it) e^{-π r t} dt`, and for `r ≥ 0`,
`b(r) = -4i sin(π r / 2)² (144 / (π r) + 1 / (π (r - 2))
  + ∫₀^∞ (ψ_I(it) - 144 - e^{2πt}) e^{-π r t} dt)`, where `r` is the squared radius `‖x‖²`.
Both follow from `MagicFunction.DoubleZeroes` with `ψ = ψ_I`.
-/

@[expose] public section

open Set Filter Asymptotics MeasureTheory Real Complex MagicFunction.Parametrisations
  MagicFunction.DoubleZeroes

namespace MagicFunction

lemma ψT'_eq_ψI'_add_one (z : ℂ) : ψT' z = ψI' (z + 1) := by
  sorry

lemma ψT'_eq_ψI'_sub_one (z : ℂ) : ψT' z = ψI' (z - 1) := by
  sorry

lemma ψI'_eq_ψT'_add_ψS' (z : ℂ) : ψI' z = ψT' z + ψS' z := by
  sorry

lemma differentiableOn_ψI' : DifferentiableOn ℂ ψI' {z | 0 < z.im} := by
  sorry

lemma integrableOn_ψI'_Ioc : IntegrableOn (fun t : ℝ ↦ ψI' (I * t)) (Ioc 0 1) := by
  sorry

lemma ψI'_isBigO_exp :
    ψI' =O[comap im atTop ⊓ 𝓟 {z | |z.re| ≤ 1}] fun z ↦ rexp (2 * π * z.im) := by
  sorry

lemma ψI'_I_mul_sub_isBigO :
    (fun t : ℝ ↦ ψI' (I * t) - (144 + cexp (2 * π * t))) =O[atTop] fun t ↦ rexp (-π * t) := by
  sorry

lemma ψS'_I_mul_isBigO : (fun t : ℝ ↦ ψS' (I * t)) =O[atTop] fun t ↦ rexp (-π * t) := by
  sorry

lemma expansion_ψI' (t : ℝ) :
    expansion 1 (fun k ↦ if k = 0 then 144 else 1) 0 t = 144 + cexp (2 * π * t) := by
  simp [expansion, Finset.sum_range_succ]

lemma ψI'_I_mul_sub_expansion_isBigO :
    (fun t : ℝ ↦ ψI' (I * t) - expansion 1 (fun k ↦ if k = 0 then 144 else 1) 0 t)
      =O[atTop] fun t ↦ rexp (-π * t) := by
  simpa only [expansion_ψI'] using ψI'_I_mul_sub_isBigO

lemma ψI'_second_difference_isBigO :
    (fun t : ℝ ↦ ψI' (I * t + 1) - 2 * ψI' (I * t) + ψI' (I * t - 1))
      =O[atTop] fun t ↦ rexp (-π * t) :=
  (ψS'_I_mul_isBigO.const_mul_left (-2)).congr_left fun t ↦ by
    rw [← ψT'_eq_ψI'_add_one, ← ψT'_eq_ψI'_sub_one, ψI'_eq_ψT'_add_ψS' (I * t)]
    ring

lemma b'_eq_contourSum (r : ℝ) : b.RealIntegrals.b' r = contourSum ψI' r := by
  have h6 : b.RealIntegrals.J₆' r = ∫ t in Ici (1 : ℝ),
      I * ((ψI' (z₆' t + 1) - 2 * ψI' (z₆' t) + ψI' (z₆' t - 1)) * cexp (π * I * r * z₆' t)) := by
    rw [b.RealIntegrals.J₆', ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun t _ ↦ ?_
    rw [← ψT'_eq_ψI'_add_one, ← ψT'_eq_ψI'_sub_one, ψI'_eq_ψT'_add_ψS' (z₆' t)]
    simp only [b.RealIntegrands.Ψ₆, b.ComplexIntegrands.Ψ₆']
    ring
  have e1 : b.RealIntegrals.J₁' r =
      ∫ t in (0 : ℝ)..1, I * (ψI' (z₁' t + 1) * cexp (π * I * r * z₁' t)) := by
    simp only [b.RealIntegrals.J₁', b.RealIntegrands.Ψ₁, b.ComplexIntegrands.Ψ₁',
      ψT'_eq_ψI'_add_one]
  have e2 : b.RealIntegrals.J₂' r =
      ∫ t in (0 : ℝ)..1, ψI' (z₂' t + 1) * cexp (π * I * r * z₂' t) := by
    simp only [b.RealIntegrals.J₂', b.RealIntegrands.Ψ₂, b.ComplexIntegrands.Ψ₂',
      ψT'_eq_ψI'_add_one]
  have e3 : b.RealIntegrals.J₃' r =
      ∫ t in (0 : ℝ)..1, I * (ψI' (z₃' t - 1) * cexp (π * I * r * z₃' t)) := by
    simp only [b.RealIntegrals.J₃', b.RealIntegrands.Ψ₃, b.ComplexIntegrands.Ψ₃',
      ψT'_eq_ψI'_sub_one]
  have e4 : b.RealIntegrals.J₄' r =
      ∫ t in (0 : ℝ)..1, -1 * (ψI' (z₄' t - 1) * cexp (π * I * r * z₄' t)) := by
    simp only [b.RealIntegrals.J₄', b.RealIntegrands.Ψ₄, b.ComplexIntegrands.Ψ₄',
      ψT'_eq_ψI'_sub_one]
  change b.RealIntegrals.J₁' r + b.RealIntegrals.J₂' r + b.RealIntegrals.J₃' r +
    b.RealIntegrals.J₄' r + b.RealIntegrals.J₅' r + b.RealIntegrals.J₆' r = _
  rw [e1, e2, e3, e4, h6]
  rfl

theorem integrableOn_ψI'_mul_cexp {r : ℝ} (hr : 2 < r) :
    IntegrableOn (fun t : ℝ ↦ ψI' (I * t) * cexp (-π * r * t)) (Ioi 0) := by
  sorry

theorem b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral {r : ℝ} (hr : 2 < r) :
    b.RealIntegrals.b' r = -4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * r * t) := by
  rw [b'_eq_contourSum, ← neg_four_mul_sin_sq_mul_integral_eq differentiableOn_ψI'
    integrableOn_ψI'_Ioc ψI'_isBigO_exp hr]
  have h (t : ℝ) : I * (ψI' (I * t) * cexp (π * I * r * (I * t))) =
      I * (ψI' (I * t) * cexp (-π * r * t)) := by
    rw [show π * I * r * (I * t) = -π * r * t by linear_combination (π * r * t : ℂ) * I_sq]
  simp_rw [h, integral_const_mul]
  ring

theorem b_eq_neg_four_mul_I_mul_sin_sq_mul_integral {x : EuclideanSpace ℝ (Fin 8)}
    (hx : √2 < ‖x‖) :
    FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * ‖x‖ ^ 2 * t) := by
  rw [FourierEigenfunctions.b_apply,
    b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral (lt_sq_of_sqrt_lt hx)]
  norm_num

theorem integrableOn_ψI'_sub_mul_cexp {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ ↦ (ψI' (I * t) - 144 - cexp (2 * π * t)) * cexp (-π * r * t))
      (Ioi 0) := by
  sorry

theorem b'_eq_another_integral {r : ℝ} (hr : 0 ≤ r) :
    b.RealIntegrals.b' r = -4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
      (144 / (π * r) + 1 / (π * (r - 2)) +
        ∫ t in Ioi (0 : ℝ), (ψI' (I * t) - 144 - cexp (2 * π * t)) * cexp (-π * r * t)) := by
  rw [b'_eq_contourSum, ← neg_four_mul_sin_sq_mul_continuation_eq differentiableOn_ψI'
    integrableOn_ψI'_Ioc ψI'_isBigO_exp pi_pos ψI'_I_mul_sub_expansion_isBigO
    ψI'_second_difference_isBigO ?_ (fun _ _ _ ↦ rfl)]
  · have h (t : ℝ) : I * ((ψI' (I * t) - expansion 1 (fun k ↦ if k = 0 then 144 else 1) 0 t)
        * cexp (π * I * r * (I * t))) =
        I * ((ψI' (I * t) - 144 - cexp (2 * π * t)) * cexp (-π * r * t)) := by
      rw [expansion_ψI',
        show π * I * r * (I * t) = -π * r * t by linear_combination (π * r * t : ℂ) * I_sq]
      ring
    simp_rw [h, integral_const_mul]
    simp [Finset.sum_range_succ]
    ring
  · rw [neg_div, div_self pi_ne_zero]
    linarith

theorem b_eq_another_integral (x : EuclideanSpace ℝ (Fin 8)) :
    FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      (144 / (π * ‖x‖ ^ 2) + 1 / (π * (‖x‖ ^ 2 - 2)) +
        ∫ t in Ioi (0 : ℝ), (ψI' (I * t) - 144 - cexp (2 * π * t)) * cexp (-π * ‖x‖ ^ 2 * t)) := by
  rw [FourierEigenfunctions.b_apply, b'_eq_another_integral (by positivity)]
  push_cast
  ring_nf

end MagicFunction
