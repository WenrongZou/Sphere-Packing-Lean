/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.DoubleZeroes
public import SpherePacking.MagicFunction.a.Schwartz
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

/-!
# Another integral representation of `a`

For `r > 0`, `a(r) = 4i sin(π r / 2)² (36 / (π³ (r - 2)) - 8640 / (π³ r²) + 18144 / (π³ r)
  + ∫₀^∞ (t² φ₀(i / t) - 36 / π² e^{2πt} + 8640 / π t - 18144 / π²) e^{-π r t} dt)`, where `r` is
the squared radius `‖x‖²`. It follows from `DoubleZeroes.neg_four_mul_sin_sq_mul_continuation_eq`
with `ψ(z) = φ₀(-1/z) z²`.
-/

@[expose] public section

open Set MeasureTheory Real Complex MagicFunction.Parametrisations MagicFunction.DoubleZeroes

namespace MagicFunction

lemma φ₀''_second_difference {z : ℂ} (hz : 0 < z.im) :
    φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 - 2 * (φ₀'' (-1 / z) * z ^ 2)
      + φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 = 2 * φ₀'' z := by
  sorry

lemma integrableOn_φ₀''_neg_inv_mul_sq :
    IntegrableOn (fun t : ℝ ↦ φ₀'' (-1 / (I * t)) * (I * t) ^ 2) (Ioc 0 1) := by
  sorry

lemma norm_φ₀''_neg_inv_mul_sq_sub_le : ∃ K, ∀ z : ℂ, 1 ≤ z.im → |z.re| ≤ 1 →
    ‖φ₀'' (-1 / z) * z ^ 2 - (-36 / π ^ 2 * cexp (-2 * π * I * z) - 8640 / π * I * z
      - 18144 / π ^ 2)‖ ≤ K * rexp (-π * z.im) := by
  sorry

lemma expansion_φ₀'' (z : ℂ) :
    expansion 1 (fun k ↦ if k = 0 then -18144 / π ^ 2 else -36 / π ^ 2)
      (fun k ↦ if k = 0 then 8640 / π else 0) z =
      -36 / π ^ 2 * cexp (-2 * π * I * z) - 8640 / π * I * z - 18144 / π ^ 2 := by
  simp [expansion, Finset.sum_range_succ]
  ring

lemma a'_eq_contourSum (r : ℝ) :
    a.RealIntegrals.a' r = contourSum (fun z ↦ φ₀'' (-1 / z) * z ^ 2) r := by
  have h6 : a.RealIntegrals.I₆' r = ∫ t in Ici (1 : ℝ),
      I * ((φ₀'' (-1 / (z₆' t + 1)) * (z₆' t + 1) ^ 2 - 2 * (φ₀'' (-1 / z₆' t) * z₆' t ^ 2)
        + φ₀'' (-1 / (z₆' t - 1)) * (z₆' t - 1) ^ 2) * cexp (π * I * r * z₆' t)) := by
    rw [a.RealIntegrals.I₆', ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun t ht ↦ ?_
    simp only [a.RealIntegrands.Φ₆, a.ComplexIntegrands.Φ₆',
      φ₀''_second_difference (im_z₆'_pos ht)]
    ring
  simp only [contourSum]
  rw [← h6]
  rfl

theorem integrableOn_φ₀''_sub_mul_cexp {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ ↦ (t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * cexp (2 * π * t)
      + 8640 / π * t - 18144 / π ^ 2) * cexp (-π * r * t)) (Ioi 0) := by
  sorry

theorem a'_eq_another_integral {r : ℝ} (hr : 0 < r) :
    a.RealIntegrals.a' r = 4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
      (36 / (π ^ 3 * (r - 2)) - 8640 / (π ^ 3 * r ^ 2) + 18144 / (π ^ 3 * r) +
        ∫ t in Ioi (0 : ℝ), (t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * cexp (2 * π * t) +
          8640 / π * t - 18144 / π ^ 2) * cexp (-π * r * t)) := by
  have hψ : DifferentiableOn ℂ (fun z ↦ φ₀'' (-1 / z) * z ^ 2) {z | 0 < z.im} := by
    simpa only [Pi.mul_def, add_zero] using
      (a.ComplexIntegrands.φ₀''_neg_inv_add_holo (c := 0) (by simp)).mul (differentiableOn_pow 2)
  have hexp := norm_φ₀''_neg_inv_mul_sq_sub_le
  simp_rw [← expansion_φ₀''] at hexp
  rw [a'_eq_contourSum, ← neg_four_mul_sin_sq_mul_continuation_eq hψ
    integrableOn_φ₀''_neg_inv_mul_sq pi_pos hexp ?_ ?_]
  · have h (t : ℝ) : I * ((φ₀'' (-1 / (I * t)) * (I * t) ^ 2 - expansion 1
        (fun k ↦ if k = 0 then -18144 / π ^ 2 else -36 / π ^ 2)
        (fun k ↦ if k = 0 then 8640 / π else 0) (I * t)) * cexp (π * I * r * (I * t))) =
        -I * ((t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * cexp (2 * π * t) + 8640 / π * t
          - 18144 / π ^ 2) * cexp (-π * r * t)) := by
      rw [expansion_φ₀'', show -1 / (I * t) = I / t by rw [mul_comm I, ← div_div, div_I]; ring,
        show -2 * π * I * (I * t) = 2 * π * t by linear_combination (-2 * π * t : ℂ) * I_sq,
        show π * I * r * (I * t) = -π * r * t by linear_combination (π * r * t : ℂ) * I_sq]
      linear_combination I * cexp (-π * r * t) * (φ₀'' (I / t) * t ^ 2 + 8640 / π * t) * I_sq
    simp_rw [h, integral_const_mul]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, div_eq_mul_inv, mul_inv]
    norm_num
    ring
  · rw [neg_div, div_self pi_ne_zero]
    linarith
  · intro k hk hrk
    rcases k with _ | _ | k
    · simp at hrk
      linarith
    · simp
    · simp at hk

theorem a_eq_another_integral {x : EuclideanSpace ℝ (Fin 8)} (hx : x ≠ 0) :
    FourierEigenfunctions.a x = 4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      (36 / (π ^ 3 * (‖x‖ ^ 2 - 2)) - 8640 / (π ^ 3 * ‖x‖ ^ 4) + 18144 / (π ^ 3 * ‖x‖ ^ 2) +
        ∫ t in Ioi (0 : ℝ), (t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * cexp (2 * π * t) +
          8640 / π * t - 18144 / π ^ 2) * cexp (-π * ‖x‖ ^ 2 * t)) := by
  rw [FourierEigenfunctions.a_apply, a'_eq_another_integral (by positivity)]
  push_cast
  ring_nf

end MagicFunction
