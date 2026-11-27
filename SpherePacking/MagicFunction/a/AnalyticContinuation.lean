/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.a.Schwartz

import SpherePacking.MagicFunction.a.CuspExpansion
import SpherePacking.MagicFunction.a.Integrability.CuspPath
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.ModularForms.PhiTransform

/-!
# Analytic continuation of `a`

The asymptotic expansion of `φ₀(i/t) t²` as `t → ∞`, and the identity `ψ(it) = t² φ₀(i/t)` for
`ψ(z) = -z² φ₀(-1/z)`, the function to which the analytic continuation of Laplace transforms is
applied.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Real Complex MagicFunction.DoubleZeroes Finset

namespace MagicFunction

/-- `φ₀(i/t) = O(e^{-2π/t})` as `t → 0`. -/
theorem φ₀''_I_div_isBigO_nhdsGT_zero :
    (fun t : ℝ ↦ φ₀'' (I / t)) =O[𝓝[>] 0] fun t ↦ rexp (-2 * π / t) := by
  obtain ⟨C₀, -, hC₀⟩ := PolyFourierCoeffBound.norm_φ₀_le
  refine Asymptotics.IsBigO.of_bound C₀ ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with t ⟨ht0, ht2⟩
  have him : (I / (t : ℂ)).im = t⁻¹ := by simp
  have hpos : 0 < (I / (t : ℂ)).im := by rw [him]; positivity
  have hlt : 1 / 2 < (I / (t : ℂ)).im := by
    rw [him, lt_inv_comm₀ (by norm_num) ht0]; norm_num [ht2]
  have h := hC₀ ⟨I / t, hpos⟩ hlt
  rw [show (⟨I / t, hpos⟩ : UpperHalfPlane).im = t⁻¹ from him] at h
  rw [φ₀''_def hpos, Real.norm_of_nonneg (exp_pos _).le, div_eq_mul_inv (-2 * π) t]
  exact h

/-- `φ₀(it) = O(e^{-2πt})` as `t → ∞`. -/
theorem φ₀''_I_mul_isBigO_atTop :
    (fun t : ℝ ↦ φ₀'' (I * t)) =O[atTop] fun t ↦ rexp (-2 * π * t) := by
  obtain ⟨C₀, -, h₀⟩ := PolyFourierCoeffBound.norm_φ₀_le
  refine Asymptotics.IsBigO.of_bound C₀ ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have him : (I * (t : ℂ)).im = t := by simp
  have hpos : 0 < (I * (t : ℂ)).im := by rw [him]; linarith
  have hlt : 1 / 2 < (I * (t : ℂ)).im := by rw [him]; linarith
  have h := h₀ ⟨I * t, hpos⟩ hlt
  rw [show (⟨I * t, hpos⟩ : UpperHalfPlane).im = t from him] at h
  rw [φ₀''_def hpos, Real.norm_of_nonneg (exp_pos _).le]
  exact h

/-- `φ₋₂(it) = 720 + O(e^{-2πt})` as `t → ∞`. -/
theorem φ₂''_I_mul_sub_isBigO_atTop :
    (fun t : ℝ ↦ φ₂'' (I * t) - 720) =O[atTop] fun t ↦ rexp (-2 * π * t) := by
  refine (a.CuspExpansion.φ₂'_sub_isBigO.comp_tendsto
    a.CuspExpansion.tendsto_ofComplex_I_mul).congr' ?_ ?_ <;>
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hpos : 0 < (I * (t : ℂ)).im := by simpa using ht
    simp [φ₂''_def hpos, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]

/-- `φ₋₄(it) = e^{2πt} + 504 + O(e^{-2πt})` as `t → ∞`. -/
theorem φ₄''_I_mul_sub_isBigO_atTop :
    (fun t : ℝ ↦ φ₄'' (I * t) - (cexp (2 * π * t) + 504)) =O[atTop]
      fun t ↦ rexp (-2 * π * t) := by
  refine (a.CuspExpansion.φ₄'_sub_isBigO.comp_tendsto
    a.CuspExpansion.tendsto_ofComplex_I_mul).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hpos : 0 < (I * (t : ℂ)).im := by simpa using ht
    -- `q⁻¹ = e^{2πt}` at `z = it`
    have h : -(2 * π * I * (I * t)) = 2 * π * (t : ℂ) := by
      linear_combination (-2 * π * t) * I_sq
    simp only [Function.comp_apply, φ₄''_def hpos, UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
      UpperHalfPlane.coe_mk, ← Complex.exp_neg, h]
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hpos : 0 < (I * (t : ℂ)).im := by simpa using ht
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]

/-- The S-transformation of `φ₀` at `z = it`, multiplied by `t²`. -/
theorem φ₀''_I_div_mul_sq {t : ℝ} (ht : 0 < t) :
    φ₀'' (I / t) * t ^ 2 =
      t ^ 2 * φ₀'' (I * t) - 12 / π * t * φ₂'' (I * t) + 36 / π ^ 2 * φ₄'' (I * t) := by
  have hpos : 0 < (I * (t : ℂ)).im := by simpa using ht
  let z : UpperHalfPlane := ⟨I * t, hpos⟩
  have hSz : ((ModularGroup.S • z : UpperHalfPlane) : ℂ) = I / t := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [z, div_eq_mul_inv, Complex.inv_I, mul_comm]
  rw [← hSz, φ₀''_coe_upperHalfPlane, φ₀_S_transform, φ₀''_def hpos, φ₂''_def hpos,
    φ₄''_def hpos]
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  simp only [z]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- `φ₀(i/t) t² = 36/π² e^{2πt} - 8640/π t + 18144/π² + O(t² e^{-2πt})` as `t → ∞`. -/
theorem φ₀''_I_div_mul_sq_sub_isBigO_atTop :
    (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2 -
      (36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2)) =O[atTop]
        fun t ↦ t ^ 2 * rexp (-2 * π * t) := by
  -- `t²`, `t` and `1` are all `O(t²)`
  have hsq : (fun t : ℝ ↦ (t : ℂ) ^ 2) =O[atTop] fun t ↦ t ^ 2 :=
    Asymptotics.isBigO_of_le _ fun t ↦ by simp
  have hid : (fun t : ℝ ↦ (t : ℂ)) =O[atTop] fun t ↦ t ^ 2 := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith),
      abs_of_pos (by positivity), one_mul]
    nlinarith
  have hone : (fun _ : ℝ ↦ (1 : ℂ)) =O[atTop] fun t ↦ t ^ 2 := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  -- `t² φ₀(i/t) = t² φ₀(it) - 12t/π φ₋₂(it) + 36/π² φ₋₄(it)`
  have h0 := hsq.mul φ₀''_I_mul_isBigO_atTop
  have h2 := (hid.mul φ₂''_I_mul_sub_isBigO_atTop).const_mul_left (12 / π : ℂ)
  have h4 := (hone.mul φ₄''_I_mul_sub_isBigO_atTop).const_mul_left (36 / π ^ 2 : ℂ)
  refine ((h0.sub h2).add h4).congr' ?_ (Eventually.of_forall fun t ↦ rfl)
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [φ₀''_I_div_mul_sq ht]
  ring

/-- `φ₀(i/t) = O(t⁻² e^{2πt})` as `t → ∞`. -/
theorem φ₀''_I_div_isBigO_atTop :
    (fun t : ℝ ↦ φ₀'' (I / t)) =O[atTop] fun t ↦ rexp (2 * π * t) / t ^ 2 := by
  have hexp : (1 : ℝ → ℝ) =O[atTop] fun t ↦ rexp (2 * π * t) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Pi.one_apply, norm_one, norm_eq_abs, abs_exp, one_mul, one_le_exp_iff]
    positivity
  have hcexp : (fun t : ℝ ↦ cexp (2 * π * t)) =O[atTop] fun t ↦ rexp (2 * π * t) :=
    Asymptotics.isBigO_of_le _ fun t ↦ by simp [Complex.norm_exp]
  have hid : (fun t : ℝ ↦ (t : ℂ)) =O[atTop] fun t ↦ rexp (2 * π * t) :=
    (Asymptotics.isBigO_of_le (g := fun t : ℝ ↦ t ^ 1) _ fun t ↦ by simp).trans
      (isLittleO_pow_exp_pos_mul_atTop 1 (by positivity)).isBigO
  -- the main term and the error term are both `O(e^{2πt})`
  have hmain : (fun t : ℝ ↦ (36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2 : ℂ))
      =O[atTop] fun t ↦ rexp (2 * π * t) :=
    ((hcexp.const_mul_left _).sub (hid.const_mul_left _)).add
      ((Asymptotics.isBigO_const_one ℝ _ atTop).trans hexp)
  have herr : (fun t : ℝ ↦ t ^ 2 * rexp (-2 * π * t)) =O[atTop] fun t ↦ rexp (2 * π * t) := by
    refine (Asymptotics.IsBigO.of_bound 1 ?_).trans
      (isLittleO_pow_exp_pos_mul_atTop 2 (by positivity)).isBigO
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [one_mul, norm_mul, Real.norm_of_nonneg (exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (exp_le_one_iff.2 (by nlinarith [pi_pos]))
  have h : (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2) =O[atTop] fun t ↦ rexp (2 * π * t) :=
    ((φ₀''_I_div_mul_sq_sub_isBigO_atTop.trans herr).add hmain).congr_left fun t ↦ by ring
  have hinv : (fun t : ℝ ↦ ((t : ℂ) ^ 2)⁻¹) =O[atTop] fun t ↦ (t ^ 2)⁻¹ :=
    Asymptotics.isBigO_of_le _ fun t ↦ by simp
  refine (h.mul hinv).congr' ?_ (Eventually.of_forall fun t ↦ (div_eq_mul_inv _ _).symm)
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact mul_inv_cancel_right₀ (pow_ne_zero 2 (ofReal_ne_zero.2 ht.ne')) _

/-- `ψ(it) = t² φ₀(i/t)` for `ψ(z) = -z² φ₀(-1/z)`. -/
theorem neg_sq_mul_φ₀''_neg_inv_I_mul (t : ℝ) :
    -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) = φ₀'' (I / t) * t ^ 2 := by
  /- This is used to rewrite `φ₀(i/t) t²` as `ψ(it)`, in order to apply the analytic continuation
    of Laplace transforms (FGH Proposition 2.1, see `MagicFunction.DoubleZeroes`) to `a`. -/
  have h : -1 / (I * t) = I / t := by simp [div_eq_mul_inv, Complex.inv_I, mul_comm]
  rw [h, mul_pow, I_sq]
  ring

/-- `t ↦ ψ(it)` is locally integrable on `[0, ∞)`, for `ψ(z) = -z² φ₀(-1/z)`. -/
theorem locallyIntegrableOn_φ₀'' :
    LocallyIntegrableOn (fun t : ℝ ↦ -(I * t) ^ 2 * φ₀'' (-1 / (I * t))) (Ici 0) := by
  refine locallyIntegrableOn_Ici_of_continuousOn_of_isBigO
    ((by fun_prop : Continuous fun t : ℝ ↦ -(I * t) ^ 2).continuousOn.mul
      continuousOn_φ₀''_cusp_path) ?_
  simp only [neg_sq_mul_φ₀''_neg_inv_I_mul]
  have h1 : (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2) =O[𝓝[>] 0] fun t ↦ φ₀'' (I / t) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ⟨ht0, ht1⟩
    rw [norm_mul, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ht0.le ht1.le)
  have h2 : (fun t : ℝ ↦ rexp (-2 * π / t)) =O[𝓝[>] 0] fun _ ↦ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (exp_pos _).le, norm_one, mul_one]
    exact exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith [pi_pos]) ht.le)
  exact h1.trans (φ₀''_I_div_isBigO_nhdsGT_zero.trans h2)

theorem expPoly_φ₀'' (t : ℝ) :
    expPoly 1 (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
      (fun k ↦ if k = 0 then -8640 / π else 0) t =
        36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2 := by
  simp [sum_range_succ]
  ring

theorem φ₀''_sub_expPoly_isBigO_atTop :
    (fun t : ℝ ↦ -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) -
      expPoly 1 (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
        (fun k ↦ if k = 0 then -8640 / π else 0) t) =O[atTop] fun t ↦ rexp (-π * t) := by
  have h : (fun t : ℝ ↦ t ^ 2 * rexp (-2 * π * t)) =O[atTop] fun t ↦ rexp (-π * t) :=
    ((isLittleO_pow_exp_pos_mul_atTop 2 pi_pos).isBigO.mul
      (Asymptotics.isBigO_refl _ _)).congr_right fun t ↦ by rw [← Real.exp_add]; ring_nf
  refine (φ₀''_I_div_mul_sq_sub_isBigO_atTop.trans h).congr_left fun t ↦ ?_
  rw [neg_sq_mul_φ₀''_neg_inv_I_mul, expPoly_φ₀'']

end MagicFunction
