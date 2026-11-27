/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.a.Phi
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.E2
public import SpherePacking.ModularForms.Eisenstein

import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import SpherePacking.ForMathlib.AtImInfty
import SpherePacking.ForMathlib.QSeriesBounds
import SpherePacking.ModularForms.EisensteinAsymptotics

/-!
# Expansions of `φ₋₂` and `φ₋₄` at the cusp

With `q = e^{2πiz}`, we show `φ₋₂ = 720 + O(‖q‖)` and `φ₋₄ = q⁻¹ + 504 + O(‖q‖)` as `z → i∞`.
These are the expansions used in the proof of the asymptotic expansion of `φ₀(i/t) t²`. We use the
`q`-expansions `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`, `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`, `E₆ = 1 - 504 ∑ σ₅(n) qⁿ` and
`Δ = (E₄³ - E₆²) / 1728`.
-/

@[expose] public section

open Filter Topology Real Complex
open scoped UpperHalfPlane ArithmeticFunction.sigma
open UpperHalfPlane (atImInfty)

namespace MagicFunction.a.CuspExpansion

/-- `E₆ = 1 - 504 ∑' n : ℕ+, σ₅ n qⁿ`. -/
lemma E₆_sigma_qexp (z : ℍ) :
    E₆ z = 1 - 504 * ∑' (n : ℕ+), (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
  refine (EisensteinSeries.q_expansion_bernoulli (by norm_num : 3 ≤ 6) (by decide) z).trans ?_
  norm_num [bernoulli, bernoulli'_six, ← Complex.exp_natCast_mul, mul_comm, mul_assoc,
    mul_left_comm]

/-- The shifted coefficients `σ_k(m + 3)` are summable against `e^{-2πm}`. -/
lemma summable_sigma_shift (k : ℕ) :
    Summable fun m : ℕ ↦ ‖(σ k (m + 3) : ℂ)‖ * rexp (-(2 * π * 1) * m) := by
  have hr : ‖rexp (-(2 * π))‖ < 1 := by
    rw [Real.norm_of_nonneg (exp_pos _).le, Real.exp_lt_one_iff]; linarith [pi_pos]
  have hg := (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (k + 1) * rexp (-(2 * π)) ^ n)
    3).2 (summable_pow_mul_geometric_of_norm_lt_one (k + 1) hr)
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun m ↦ ?_)
    (hg.mul_left (rexp (2 * π) ^ 3))
  have h1 : (σ k (m + 3) : ℝ) ≤ ((m + 3 : ℕ) : ℝ) ^ (k + 1) := by
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k (m + 3)
  have h2 : rexp (-(2 * π * 1) * m) = rexp (2 * π) ^ 3 * rexp (-(2 * π)) ^ (m + 3) := by
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul, ← Real.exp_add]; push_cast; ring_nf
  rw [Complex.norm_natCast, h2]
  calc (σ k (m + 3) : ℝ) * (rexp (2 * π) ^ 3 * rexp (-(2 * π)) ^ (m + 3))
      ≤ ((m + 3 : ℕ) : ℝ) ^ (k + 1) * (rexp (2 * π) ^ 3 * rexp (-(2 * π)) ^ (m + 3)) := by
        gcongr
    _ = _ := by ring

/-- `∑ σ_k(n) qⁿ = q + σ_k(2) q² + O(‖q‖³)` at `i∞`. -/
lemma sigma_qseries_sub_isBigO (k : ℕ) :
    (fun z : ℍ ↦ ∑' n : ℕ+, (σ k n : ℂ) * cexp (2 * π * I * n * z) -
      (cexp (2 * π * I * z) + σ k 2 * cexp (2 * π * I * z) ^ 2))
      =O[UpperHalfPlane.atImInfty] fun z ↦ rexp (-2 * π * z.im) ^ 3 := by
  refine Asymptotics.IsBigO.of_bound (∑' m : ℕ, ‖(σ k (m + 3) : ℂ)‖ * rexp (-(2 * π * 1) * m)) ?_
  filter_upwards [Filter.eventually_atImInfty.2 ⟨1, fun z hz ↦ hz⟩] with z hz
  let f : ℕ → ℂ := fun m ↦ (σ k m : ℂ) * cexp (2 * π * I * m * z)
  have hfs : Summable f := (summable_pnat_iff_summable_nat (f := f)).1
    (by simpa [f] using sigma_qexp_summable_generic 0 k z)
  have hsplit : ∑' n : ℕ+, (σ k n : ℂ) * cexp (2 * π * I * n * z) =
      f 0 + f 1 + f 2 + ∑' m : ℕ, f (m + 3) := by
    rw [tsum_pnat_eq_tsum_of_eq_zero (f := f) (by simp [f]), ← hfs.sum_add_tsum_nat_add 3]
    simp [Finset.sum_range_succ]
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = cexp (2 * π * I * z) := by simp [f, ArithmeticFunction.sigma_apply]
  have hf2 : f 2 = σ k 2 * cexp (2 * π * I * z) ^ 2 := by
    simp only [f]
    rw [← Complex.exp_natCast_mul]; push_cast; ring_nf
  rw [hsplit, hf0, hf1, hf2, show ∀ a b c : ℂ, 0 + a + b + c - (a + b) = c by intros; ring]
  refine (Complex.norm_qseries_shift_le 3 (summable_sigma_shift k) (by simpa using hz)).trans_eq ?_
  rw [Real.norm_of_nonneg (by positivity), ← Real.exp_natCast_mul]
  congr 2
  simp only [UpperHalfPlane.coe_im]
  push_cast
  ring

lemma norm_cexp_two_pi_I_mul (z : ℍ) : ‖cexp (2 * π * I * z)‖ = rexp (-2 * π * z.im) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma cexp_pow_isBigO (n : ℕ) : (fun z : ℍ ↦ cexp (2 * π * I * z) ^ n) =O[atImInfty]
    fun z ↦ rexp (-2 * π * z.im) ^ n :=
  Asymptotics.isBigO_of_le _ fun z ↦ by
    rw [norm_pow, norm_cexp_two_pi_I_mul, norm_pow, Real.norm_of_nonneg (exp_pos _).le]

lemma exp_pow_succ_isBigO (n : ℕ) : (fun z : ℍ ↦ rexp (-2 * π * z.im) ^ (n + 1)) =O[atImInfty]
    fun z ↦ rexp (-2 * π * z.im) ^ n :=
  Asymptotics.isBigO_of_le _ fun z ↦ by
    rw [norm_pow, norm_pow, Real.norm_of_nonneg (exp_pos _).le]
    exact pow_le_pow_of_le_one (exp_pos _).le
      (exp_le_one_iff.2 (by nlinarith [pi_pos, z.im_pos])) (Nat.le_succ n)

lemma tendsto_exp_neg_two_pi_im :
    Tendsto (fun z : ℍ ↦ rexp (-2 * π * z.im)) atImInfty (𝓝 0) :=
  tendsto_exp_atBot.comp (tendsto_im_atImInfty.const_mul_atTop_of_neg (by linarith [pi_pos]))

lemma tendsto_cexp_two_pi_I_mul :
    Tendsto (fun z : ℍ ↦ cexp (2 * π * I * z)) atImInfty (𝓝 0) := by
  have h₀ : Tendsto (fun z : ℍ ↦ -2 * π * z.im) atImInfty atBot :=
    tendsto_im_atImInfty.const_mul_atTop_of_neg (by linarith [pi_pos])
  have h : Tendsto (fun z : ℍ ↦ rexp (-2 * π * z.im)) atImInfty (𝓝 0) :=
    tendsto_exp_atBot.comp h₀
  simpa only [pow_one] using (cexp_pow_isBigO 1).trans_tendsto (by simpa only [pow_one] using h)

/-- `E₄ = 1 + 240 q + 2160 q² + O(‖q‖³)`. -/
lemma E₄_sub_isBigO : (fun z : ℍ ↦ E₄ z - (1 + 240 * cexp (2 * π * I * z) +
    2160 * cexp (2 * π * I * z) ^ 2)) =O[atImInfty] fun z ↦ rexp (-2 * π * z.im) ^ 3 :=
  ((sigma_qseries_sub_isBigO 3).const_mul_left 240).congr_left fun z ↦ by
    rw [E₄_sigma_qexp, show (σ 3 2 : ℂ) = 9 by
      norm_num [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]]
    ring

/-- `E₆ = 1 - 504 q - 16632 q² + O(‖q‖³)`. -/
lemma E₆_sub_isBigO : (fun z : ℍ ↦ E₆ z - (1 - 504 * cexp (2 * π * I * z) -
    16632 * cexp (2 * π * I * z) ^ 2)) =O[atImInfty] fun z ↦ rexp (-2 * π * z.im) ^ 3 :=
  ((sigma_qseries_sub_isBigO 5).const_mul_left (-504)).congr_left fun z ↦ by
    rw [E₆_sigma_qexp, show (σ 5 2 : ℂ) = 33 by
      norm_num [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]]
    ring

/-- `E₂ = 1 - 24 q + O(‖q‖²)`. -/
lemma E₂_sub_isBigO : (fun z : ℍ ↦ E₂ z - (1 - 24 * cexp (2 * π * I * z))) =O[atImInfty]
    fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
  ((((sigma_qseries_sub_isBigO 1).trans (exp_pow_succ_isBigO 2)).const_mul_left (-24)).add
    ((cexp_pow_isBigO 2).const_mul_left (-72))).congr_left fun z ↦ by
    rw [E₂_sigma_qexp, show (σ 1 2 : ℂ) = 3 by
      norm_num [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]]
    ring

/-- `Δ = q - 24 q² + O(‖q‖³)`, from `Δ = (E₄³ - E₆²) / 1728`. -/
lemma Δ_sub_isBigO : (fun z : ℍ ↦ Δ z - (cexp (2 * π * I * z) - 24 * cexp (2 * π * I * z) ^ 2))
    =O[atImInfty] fun z ↦ rexp (-2 * π * z.im) ^ 3 := by
  have hq := tendsto_cexp_two_pi_I_mul
  have hE₄ : Tendsto (fun z : ℍ ↦ E₄ z) atImInfty (𝓝 1) := E₄_tendsto_one_atImInfty
  have hE₆ : Tendsto (fun z : ℍ ↦ E₆ z) atImInfty (𝓝 1) := E₆_tendsto_one_atImInfty
  have hp₄ : Tendsto (fun z : ℍ ↦ 1 + 240 * cexp (2 * π * I * z) +
      2160 * cexp (2 * π * I * z) ^ 2) atImInfty (𝓝 1) := by
    simpa using ((hq.const_mul 240).const_add 1).add ((hq.pow 2).const_mul 2160)
  have hp₆ : Tendsto (fun z : ℍ ↦ 1 - 504 * cexp (2 * π * I * z) -
      16632 * cexp (2 * π * I * z) ^ 2) atImInfty (𝓝 1) := by
    simpa using ((hq.const_mul 504).const_sub 1).sub ((hq.pow 2).const_mul 16632)
  have hP : (fun z : ℍ ↦ 169344 + 110621376 * cexp (2 * π * I * z) +
      3359232000 * cexp (2 * π * I * z) ^ 2 + 10077696000 * cexp (2 * π * I * z) ^ 3)
      =O[atImInfty] (fun _ ↦ (1 : ℝ)) :=
    ((((hq.const_mul _).const_add _).add ((hq.pow 2).const_mul _)).add
      ((hq.pow 3).const_mul _)).isBigO_one ℝ
  have hX := (((hE₄.pow 2).add (hE₄.mul hp₄)).add (hp₄.pow 2)).isBigO_one ℝ
  have hY := (hE₆.add hp₆).isBigO_one ℝ
  refine ((((cexp_pow_isBigO 3).mul hP).add (E₄_sub_isBigO.mul hX)).sub
    (E₆_sub_isBigO.mul hY) |>.const_mul_left (1 / 1728)).congr' ?_ ?_
  · refine Eventually.of_forall fun z ↦ ?_
    have hΔ : Δ z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
    simp only
    rw [hΔ]
    ring
  · exact Eventually.of_forall fun z ↦ by simp

lemma exp_inv_isBigO_discriminant : (fun z : ℍ ↦ (Δ z)⁻¹) =O[atImInfty]
    fun z ↦ (rexp (-2 * π * z.im))⁻¹ :=
  ModularForm.exp_isBigO_discriminant.inv_rev
    (Eventually.of_forall fun _ h ↦ absurd h (exp_pos _).ne')

/-- `φ₋₂ = 720 + O(‖q‖)` at `i∞`. -/
lemma φ₂'_sub_isBigO : (fun z : ℍ ↦ φ₂' z - 720) =O[atImInfty]
    fun z ↦ rexp (-2 * π * z.im) := by
  have hq := tendsto_cexp_two_pi_I_mul
  have hE₄ : (fun z : ℍ ↦ E₄ z) =O[atImInfty] (fun _ ↦ (1 : ℝ)) :=
    (E₄_tendsto_one_atImInfty).isBigO_one ℝ
  have h₁ : (fun z : ℍ ↦ 1 - 24 * cexp (2 * π * I * z)) =O[atImInfty] (fun _ ↦ (1 : ℝ)) :=
    ((hq.const_mul 24).const_sub 1).isBigO_one ℝ
  -- second order remainders
  have hb : (fun z : ℍ ↦ E₄ z - (1 + 240 * cexp (2 * π * I * z))) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
    ((E₄_sub_isBigO.trans (exp_pow_succ_isBigO 2)).add
      ((cexp_pow_isBigO 2).const_mul_left 2160)).congr_left fun z ↦ by ring
  have hc : (fun z : ℍ ↦ E₆ z - (1 - 504 * cexp (2 * π * I * z))) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
    ((E₆_sub_isBigO.trans (exp_pow_succ_isBigO 2)).sub
      ((cexp_pow_isBigO 2).const_mul_left 16632)).congr_left fun z ↦ by ring
  have hd : (fun z : ℍ ↦ Δ z - cexp (2 * π * I * z)) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
    ((Δ_sub_isBigO.trans (exp_pow_succ_isBigO 2)).sub
      ((cexp_pow_isBigO 2).const_mul_left 24)).congr_left fun z ↦ by ring
  -- `E₂E₄ - E₆ = 720 q + O(‖q‖²)`
  have hA : (fun z : ℍ ↦ E₂ z * E₄ z - E₆ z - 720 * cexp (2 * π * I * z)) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
    (((((cexp_pow_isBigO 2).const_mul_left (-5760)).add
      ((h₁.mul hb).congr_right fun _ ↦ one_mul _)).add
      ((E₂_sub_isBigO.mul hE₄).congr_right fun _ ↦ mul_one _)).sub hc).congr_left
      fun z ↦ by ring
  have hE₄' : (fun z : ℍ ↦ E₄ z - 1) =O[atImInfty] fun z ↦ rexp (-2 * π * z.im) ^ 1 :=
    (((cexp_pow_isBigO 1).const_mul_left 240).add (hb.trans (exp_pow_succ_isBigO 1))).congr_left
      fun z ↦ by ring
  -- `E₄(E₂E₄ - E₆) - 720 Δ = O(‖q‖²)`
  have hN : (fun z : ℍ ↦ E₄ z * (E₂ z * E₄ z - E₆ z) - 720 * Δ z) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
    (((((cexp_pow_isBigO 1).mul hE₄').const_mul_left 720).congr_right fun _ ↦ by ring).add
      ((hE₄.mul hA).congr_right fun _ ↦ one_mul _) |>.sub (hd.const_mul_left 720)).congr_left
      fun z ↦ by ring
  refine ((hN.mul exp_inv_isBigO_discriminant).congr_right fun z ↦ ?_).congr_left fun z ↦ ?_
  · rw [pow_two, mul_assoc, mul_inv_cancel₀ (exp_pos _).ne', mul_one]
  · have hΔ := ModularForm.discriminant_ne_zero z
    simp only [φ₂']
    field_simp

/-- `φ₋₄ = q⁻¹ + 504 + O(‖q‖)` at `i∞`. -/
lemma φ₄'_sub_isBigO : (fun z : ℍ ↦ φ₄' z - ((cexp (2 * π * I * z))⁻¹ + 504)) =O[atImInfty]
    fun z ↦ rexp (-2 * π * z.im) := by
  have hq := tendsto_cexp_two_pi_I_mul
  have h₁ : (fun z : ℍ ↦ 1 + 240 * cexp (2 * π * I * z)) =O[atImInfty] (fun _ ↦ (1 : ℝ)) :=
    ((hq.const_mul 240).const_add 1).isBigO_one ℝ
  have hb : (fun z : ℍ ↦ E₄ z - (1 + 240 * cexp (2 * π * I * z))) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
    ((E₄_sub_isBigO.trans (exp_pow_succ_isBigO 2)).add
      ((cexp_pow_isBigO 2).const_mul_left 2160)).congr_left fun z ↦ by ring
  have hb₀ : (fun z : ℍ ↦ E₄ z - (1 + 240 * cexp (2 * π * I * z))) =O[atImInfty]
      (fun _ ↦ (1 : ℝ)) :=
    hb.trans (((tendsto_exp_neg_two_pi_im).pow 2).isBigO_one ℝ)
  have hqinv : (fun z : ℍ ↦ (cexp (2 * π * I * z))⁻¹) =O[atImInfty]
      fun z ↦ (rexp (-2 * π * z.im))⁻¹ :=
    Asymptotics.isBigO_of_le _ fun z ↦ by
      rw [norm_inv, norm_cexp_two_pi_I_mul, norm_inv, Real.norm_of_nonneg (exp_pos _).le]
  -- `E₄² - (q⁻¹ + 504) Δ = O(‖q‖²)`
  have h₂ := ((h₁.mul hb).congr_right fun _ ↦ one_mul _).const_mul_left (2 : ℂ)
  have h₃ := (hb.mul hb₀).congr_right fun _ ↦ mul_one _
  have h₄ : (fun z : ℍ ↦ (cexp (2 * π * I * z))⁻¹ *
      (Δ z - (cexp (2 * π * I * z) - 24 * cexp (2 * π * I * z) ^ 2))) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 :=
    (hqinv.mul Δ_sub_isBigO).congr_right fun _ ↦ by
      rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ (exp_pos _).ne', one_mul]
  have h₅ := (Δ_sub_isBigO.trans (exp_pow_succ_isBigO 2)).const_mul_left (504 : ℂ)
  have hN : (fun z : ℍ ↦ E₄ z ^ 2 - ((cexp (2 * π * I * z))⁻¹ + 504) * Δ z) =O[atImInfty]
      fun z ↦ rexp (-2 * π * z.im) ^ 2 := by
    refine (((((cexp_pow_isBigO 2).const_mul_left (69696 : ℂ)).add h₂).add h₃).sub h₄
      |>.sub h₅).congr_left fun z ↦ ?_
    have := Complex.exp_ne_zero (2 * π * I * z)
    field_simp
    ring
  refine ((hN.mul exp_inv_isBigO_discriminant).congr_right fun z ↦ ?_).congr_left fun z ↦ ?_
  · rw [pow_two, mul_assoc, mul_inv_cancel₀ (exp_pos _).ne', mul_one]
  · have hΔ := ModularForm.discriminant_ne_zero z
    simp only [φ₄']
    field_simp

lemma tendsto_ofComplex_I_mul :
    Tendsto (fun t : ℝ ↦ UpperHalfPlane.ofComplex (I * t)) atTop atImInfty :=
  UpperHalfPlane.tendsto_comap_im_ofComplex.comp
    (tendsto_comap_iff.2 (tendsto_id.congr fun t ↦ by simp))

end MagicFunction.a.CuspExpansion
