/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.a.Schwartz

/-!
# Analytic continuation of `a`

The asymptotic expansion of `φ₀(i/t) t²` as `t → ∞`.
-/

@[expose] public section

open Filter Real Complex

namespace MagicFunction

/-- `φ₀(i/t) t² = 36/π² e^{2πt} - 8640/π t + 18144/π² + O(t² e^{-2πt})` as `t → ∞`. -/
theorem φ₀''_I_div_mul_sq_sub_isBigO_atTop :
    (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2 -
      (36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2))
      =O[atTop] fun t ↦ t ^ 2 * rexp (-2 * π * t) := by
  sorry

end MagicFunction
