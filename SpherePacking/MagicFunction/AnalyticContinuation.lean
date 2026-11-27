/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.IntegralParametrisations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Analytic continuation of Laplace transforms

Let `t ↦ ψ(it)` be locally integrable on `[0, ∞)` with
`ψ(it) = ∑_{k=0}^n (a_k + t b_k) e^{2πkt} + O(e^{-Ct})` as `t → ∞`. Then for `Re s > 2n`,
`W(s) = ∫₀^∞ ψ(it) e^{-πst} dt` equals
`∑_{k=0}^n (a_k / (π(s - 2k)) + b_k / (π²(s - 2k)²)) + ∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt`,
where `P = expPoly n a b`, and the last integral is holomorphic on `Re s > -C/π`.
This is used for the analytic continuation of `a` and `b`.

## References

* [A. S. Feigenbaum, P. J. Grabner and D. P. Hardin, *Eigenfunctions of the Fourier transform
  with specified zeros*][feigenbaumgrabnerhardin2021]
-/

@[expose] public section

open Set Filter Topology MeasureTheory Real Complex MagicFunction.Parametrisations Finset

namespace MagicFunction.DoubleZeroes

/-- The main term `P(t) = ∑_{k=0}^n (a_k + t b_k) e^{2πkt}` of `ψ(it)` as `t → ∞`. -/
noncomputable def expPoly (n : ℕ) (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (a k + t * b k) * cexp (2 * π * k * t)

@[simp] lemma expPoly_apply (n : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    expPoly n a b t = ∑ k ∈ range (n + 1), (a k + t * b k) * cexp (2 * π * k * t) :=
  rfl

/-- A function continuous on `(0, ∞)` and bounded near `0` is locally integrable on `[0, ∞)`.
This is used to verify the hypothesis `hloc` below. -/
theorem locallyIntegrableOn_Ici_of_continuousOn_of_isBigO {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioi 0)) (h0 : f =O[𝓝[>] 0] fun _ ↦ (1 : ℝ)) :
    LocallyIntegrableOn f (Ici 0) := by
  intro x hx
  rcases (mem_Ici.1 hx).eq_or_lt with rfl | hx
  · have h : f =O[𝓝[≥] 0] fun _ ↦ (1 : ℝ) := by
      rw [← Set.insert_Ioi, nhdsWithin_insert]
      exact (show f =O[pure 0] fun _ ↦ (1 : ℝ) from Asymptotics.isBigO_pure.2 (by simp)).sup h0
    refine h.integrableAtFilter ⟨Ici 0, self_mem_nhdsWithin, ?_⟩
      ((continuous_const.integrableAt_nhds 0).filter_mono nhdsWithin_le_nhds)
    rw [← restrict_Ioi_eq_restrict_Ici]
    exact hf.aestronglyMeasurable measurableSet_Ioi
  · exact (hf.locallyIntegrableOn measurableSet_Ioi x hx).filter_mono
      (nhdsWithin_le_nhds.trans (nhdsWithin_eq_nhds.2 (Ioi_mem_nhds hx)).ge)

variable {ψ : ℂ → ℂ} {n : ℕ} {a b : ℕ → ℂ} {C : ℝ} {s : ℂ}

/-- `W(s) = ∫₀^∞ ψ(it) e^{-πst} dt` converges absolutely for `Re s > 2n`. -/
theorem integrableOn_mul_cexp (hC : 0 < C) (hs : 2 * n < s.re)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    IntegrableOn (fun t : ℝ ↦ ψ (I * t) * cexp (-π * s * t)) (Ioi 0) := by
  sorry

/-- `∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt` converges absolutely for `Re s > -C/π`. -/
theorem integrableOn_sub_expPoly_mul_cexp (hs : -C / π < s.re)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    IntegrableOn (fun t : ℝ ↦ (ψ (I * t) - expPoly n a b t) * cexp (-π * s * t))
      (Ioi 0) := by
  /- Here we don't need `C` to be positive, since if `C ≤ 0`, `- C / π ≥ 0`,
    which is a weaker result. -/
  sorry

/-- FGH Proposition 2.1: for `Re s > 2n`, `W(s)` is the sum of its principal parts at `s = 2k`
and `∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt`. -/
theorem integral_eq_sum_add_integral_sub (hC : 0 < C) (hs : 2 * n < s.re)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    ∫ t in Ioi (0 : ℝ), ψ (I * t) * cexp (-π * s * t) =
      ∑ k ∈ range (n + 1), (a k / (π * (s - 2 * k)) + b k / (π ^ 2 * (s - 2 * k) ^ 2)) +
        ∫ t in Ioi (0 : ℝ), (ψ (I * t) - expPoly n a b t) * cexp (-π * s * t) := by
  sorry

/-- `∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt` is holomorphic on `Re s > -C/π`, so the right hand side of
`integral_eq_sum_add_integral_sub` is a meromorphic continuation of `W` to this half-plane, with at
most double poles at `s = 2k`. -/
theorem analyticOnNhd_integral_sub_expPoly (hC : 0 < C)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ t in Ioi (0 : ℝ),
      (ψ (I * t) - expPoly n a b t) * cexp (-π * s * t)) {s | -C / π < s.re} := by
  sorry

/-- `sin(πs/2)^2 * ∫₀^∞ ψ(it) e^{-πst} dt` is holomorphic on `Re s > -C/π`. -/
theorem analyticOnNhd_sin_sq_mul_integral (hC : 0 < C)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
      AnalyticOnNhd ℂ (fun s : ℂ ↦ (sin (π * s / 2)) ^ 2 * ∫ t in Ioi (0 : ℝ),
        ψ (I * t) * cexp (-π * s * t)) {s | -C / π < s.re} := by
  sorry

end MagicFunction.DoubleZeroes
