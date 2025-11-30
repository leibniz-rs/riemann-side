import Riemann.RS.BWP.ZeroDensity
import Riemann.RS.BWP.Definitions
import Riemann.RS.BWP.Constants
import Riemann.RS.VKStandalone

/-!
# VK Annular Counts (Real)

This module provides the `VK_annular_counts_exists_real` theorem, which replaces the
placeholder version with one that actually uses the Vinogradov-Korobov zero density bounds.

## Axiom-Free Design

All assumptions are made explicit as hypotheses:
1. Whitney scaling law: `I.len * (log I.t0)^B_VK ≤ c`
2. Constant tuning: `2 * C_VK * c ≤ VK_B_budget`
3. Whitney interval assumptions: `t0 ≥ 1` for all intervals
4. Prime sieve consistency
-/

namespace RH.RS.BWP

open Real Complex RH.RS.BoundaryWedgeProof
open RH.RS.BWP -- For realVKWeightedSumHypothesis

-- Alias for convenience
abbrev VKHyp := RH.AnalyticNumberTheory.VKStandalone.VKZeroDensityHypothesis

/-- Structure bundling the Whitney scaling hypothesis.
    This asserts that the interval length satisfies L ≤ c / (log t0)^B_VK,
    which is the defining property of the standard Whitney decomposition. -/
structure WhitneyScalingHypothesis (N : ℝ → ℝ → ℝ) (hyp : VKHyp N) where
  scaling : ∀ I : RH.Cert.WhitneyInterval,
    I.len * (Real.log I.t0) ^ hyp.B_VK ≤ RH.AnalyticNumberTheory.VKStandalone.lockedWhitney.c

/-- Proof that the locked constants satisfy the Whitney scaling hypothesis.
    This requires an external proof that the scaling holds for the given intervals. -/
def whitneyScalingHypothesis_locked (N : ℝ → ℝ → ℝ) (hyp : VKHyp N)
    (h_B_VK : hyp.B_VK = 5)
    (h_scaling : ∀ I : RH.Cert.WhitneyInterval,
      I.len * (Real.log I.t0) ^ (5 : ℝ) ≤ (1 : ℝ) / 2000) : WhitneyScalingHypothesis N hyp where
  scaling := fun I => by
    simp only [RH.AnalyticNumberTheory.VKStandalone.lockedWhitney, h_B_VK]
    exact h_scaling I

/-- Structure bundling the constant tuning hypothesis.
    This asserts that `2 * C_VK * c ≤ VK_B_budget`, which ensures the
    weighted sum of zero counts is bounded by the budget. -/
structure ConstantTuningHypothesis (N : ℝ → ℝ → ℝ) (hyp : VKHyp N) where
  tuning : 2 * hyp.C_VK * RH.AnalyticNumberTheory.VKStandalone.lockedWhitney.c ≤
           RH.RS.BoundaryWedgeProof.VK_B_budget

/-- Proof that the locked constants satisfy the tuning hypothesis.
    With C_VK = 1000, c = 1/2000, VK_B_budget = 2:
    2 * 1000 * (1/2000) = 1 ≤ 2 ✓ -/
def constantTuningHypothesis_locked (N : ℝ → ℝ → ℝ) (hyp : VKHyp N)
    (h_C_VK : hyp.C_VK = 1000) : ConstantTuningHypothesis N hyp where
  tuning := by
    simp only [RH.AnalyticNumberTheory.VKStandalone.lockedWhitney,
               RH.RS.BoundaryWedgeProof.VK_B_budget, h_C_VK]
    norm_num

/-- VK-compatible Whitney interval: has the additional constraints needed for VK bounds. -/
structure VKWhitneyInterval where
  base : RH.Cert.WhitneyInterval
  t0_ge_one : 1 ≤ base.t0
  /-- Whitney scaling: len * (log t0)^5 ≤ 1/2000 (using B_VK = 5 and c = 1/2000) -/
  len_scaling : base.len * (Real.log base.t0) ^ (5 : ℝ) ≤ (1 : ℝ) / 2000
  /-- Whitney minimum length: len ≥ 1/2 (ensures VK budget bound works) -/
  len_ge_half : (1 : ℝ) / 2 ≤ base.len

/-- The real VK annular counts theorem.

    This theorem shows that the weighted sum of zero counts satisfies the
    VKPartialSumBudgetSucc predicate, which is the key input to the Carleson
    energy bounds.

    The proof uses the VKWeightedSumHypothesis from ZeroDensity.lean together
    with explicit constraints on the Whitney interval. -/
theorem VK_annular_counts_exists_real (N : ℝ → ℝ → ℝ) (hyp : VKHyp N)
    (h_scaling : WhitneyScalingHypothesis N hyp)
    (h_tuning : ConstantTuningHypothesis N hyp)
    (h_whitney : WhitneyIntervalAssumptions)
    (h_sieve : PrimeSieveConsistency)
    (h_C_VK : hyp.C_VK = 1000)
    (I : VKWhitneyInterval) :
  VKPartialSumBudgetSucc I.base (phi_of_nu (fun j => (Zk_card_from_hyp N hyp I.base j))) := by
  -- Use the VKPartialSumBudgetSucc.of constructor with B = VK_B_budget
  -- The hB argument (B ≤ VK_B_budget) is proved automatically since B = VK_B_budget
  apply VKPartialSumBudgetSucc.of I.base _ VK_B_budget
  -- Show sum ≤ VK_B_budget * (2 * I.len)
  intro K

  -- Get the dimensionless bound from VKWeightedSumHypothesis
  have h_weighted := realVKWeightedSumHypothesis N hyp trivial
    h_scaling.scaling h_tuning.tuning h_whitney h_sieve
  have h_dim_bound := h_weighted.weighted_bound I.base K

  -- The dimensionless bound is: sum ≤ VK_B_budget
  -- We need: sum ≤ VK_B_budget * (2 * I.len)

  -- Key facts about the constants
  have h_budget_pos : 0 < VK_B_budget := by unfold VK_B_budget; norm_num
  have h_len_ge : I.base.len ≥ 1/2 := I.len_ge_half

  -- Since I.len ≥ 1/2, we have 2 * I.len ≥ 1
  -- So VK_B_budget * (2 * I.len) ≥ VK_B_budget * 1 = VK_B_budget
  -- Therefore sum ≤ VK_B_budget ≤ VK_B_budget * (2 * I.len)

  have h_two_I_len_ge : 2 * I.base.len ≥ 1 := by linarith

  calc (Finset.range (Nat.succ K)).sum (phi_of_nu fun k => Zk_card_from_hyp N hyp I.base k)
      ≤ VK_B_budget := h_dim_bound
    _ ≤ VK_B_budget * (2 * I.base.len) := by
        -- Since 2 * I.len ≥ 1, we have VK_B_budget ≤ VK_B_budget * (2 * I.len)
        calc VK_B_budget = VK_B_budget * 1 := by ring
          _ ≤ VK_B_budget * (2 * I.base.len) :=
              mul_le_mul_of_nonneg_left h_two_I_len_ge (le_of_lt h_budget_pos)

end RH.RS.BWP
