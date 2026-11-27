/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.b.Schwartz

import SpherePacking.ModularForms.Delta

/-!
# Double zeroes of `b`

For `s > 2`, `b(s) = -4i sin(π s / 2)² ∫₀^∞ ψ_I(it) e^{-π s t} dt`, where `s` is the squared
radius `‖x‖²`. We also state the behaviour of `ψ_I(it)` as `t → 0` and `t → ∞`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Real Complex MagicFunction.DoubleZeroes Finset

namespace MagicFunction

/-- `ψ_I(it) = O(t² e^{-π/t})` as `t → 0`. -/
theorem ψI'_I_mul_isBigO_nhdsGT_zero :
    (fun t : ℝ ↦ ψI' (I * t)) =O[𝓝[>] 0] fun t ↦ t ^ 2 * rexp (-π / t) := by
  sorry

/-- `ψ_I(it) = O(e^{2πt})` as `t → ∞`. -/
theorem ψI'_I_mul_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t)) =O[atTop] fun t ↦ rexp (2 * π * t) := by
  sorry

/-- `ψ_S = -G / (2Δ)` is holomorphic on the upper half-plane. -/
theorem ψS'_holo : DifferentiableOn ℂ ψS' {z : ℂ | 0 < z.im} := by
  have hG := UpperHalfPlane.mdifferentiable_iff.mp G_holo
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp CuspForm.discriminant.holo'
  refine DifferentiableOn.congr ((hG.const_mul (-1 / 2 : ℂ)).div hΔ fun z hz ↦ ?_)
    fun z hz ↦ ?_
  · simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz,
      ModularForm.discriminant_ne_zero]
  · simp [ψS'_def hz, ψS_eq_neg_one_half_smul_G_div_disc,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- `t ↦ ψ_I(it) = ψ_S(i/t) (it)²` is continuous on `(0, ∞)`. -/
theorem continuousOn_ψI'_I_mul : ContinuousOn (fun t : ℝ ↦ ψI' (I * t)) (Ioi 0) := by
  have hmaps : MapsTo (fun t : ℝ ↦ -1 / (I * t)) (Ioi 0) {z : ℂ | 0 < z.im} := fun t ht ↦ by
    simpa [div_mul_eq_div_div] using mem_Ioi.mp ht
  have hcont : ContinuousOn (fun t : ℝ ↦ -1 / (I * t)) (Ioi 0) := by
    fun_prop (disch := intro t ht; exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht)))
  refine ((ψS'_holo.continuousOn.comp hcont hmaps).mul
    (by fun_prop : Continuous fun t : ℝ ↦ (I * t) ^ 2).continuousOn).congr fun t ht ↦ ?_
  exact ψS_slash_S_explicit (z := I * t) (by simpa using ht)

/-- `t ↦ ψ_I(it)` is locally integrable on `[0, ∞)`. -/
theorem locallyIntegrableOn_ψI'_I_mul :
    LocallyIntegrableOn (fun t : ℝ ↦ ψI' (I * t)) (Ici 0) := by
  refine locallyIntegrableOn_Ici_of_continuousOn_of_isBigO continuousOn_ψI'_I_mul
    (ψI'_I_mul_isBigO_nhdsGT_zero.trans (Asymptotics.IsBigO.of_bound 1 ?_))
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ⟨ht0, ht1⟩
  have h1 : t ^ 2 ≤ 1 := pow_le_one₀ ht0.le ht1.le
  have h2 : rexp (-π / t) ≤ 1 :=
    exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith [pi_pos]) ht0.le)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, abs_of_pos ht0,
    norm_one, mul_one]
  nlinarith [exp_pos (-π / t)]

theorem integrableOn_ψI'_mul_cexp {s : ℝ} (hr : 2 < s) :
    IntegrableOn (fun t : ℝ ↦ ψI' (I * t) * cexp (-π * s * t)) (Ioi 0) := by
  sorry

theorem b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral {s : ℝ} (hr : 2 < s) :
    b.RealIntegrals.b' s = -4 * I * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t) := by
  sorry

theorem b_eq_neg_four_mul_I_mul_sin_sq_mul_integral {x : EuclideanSpace ℝ (Fin 8)} (hx : √2 < ‖x‖) :
    FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * ‖x‖ ^ 2 * t) := by
  rw [FourierEigenfunctions.b_apply,
    b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral (lt_sq_of_sqrt_lt hx)]
  norm_num

/-- `ψ_I(it) = e^{2πt} + 144 + O(e^{-πt})` as `t → ∞`. -/
theorem ψI'_I_mul_sub_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t) - (cexp (2 * π * t) + 144)) =O[atTop] fun t ↦ rexp (-π * t) := by
  sorry

theorem expPoly_ψI' (t : ℝ) :
    expPoly 1 (fun k ↦ if k = 0 then 144 else 1) 0 t = cexp (2 * π * t) + 144 := by
  simp [sum_range_succ, add_comm]

theorem ψI'_I_mul_sub_expPoly_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t) - expPoly 1 (fun k ↦ if k = 0 then 144 else 1) 0 t) =O[atTop]
      fun t ↦ rexp (-π * t) :=
  ψI'_I_mul_sub_isBigO_atTop.congr_left fun t ↦ by rw [expPoly_ψI']

end MagicFunction
