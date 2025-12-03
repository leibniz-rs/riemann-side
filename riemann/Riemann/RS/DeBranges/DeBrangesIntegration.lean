import Riemann.RS.DeBranges.HBContradiction
import Riemann.Cert.KxiPPlus
import Riemann.academic_framework.CompletedXiSymmetry

/-!
# De Branges Integration Layer

This module connects the de Branges contradiction (off-line zeros impossible)
to the standard RH predicate used in the rest of the library.
-/

namespace RH.RS.DeBranges

open Complex

/-- The main De Branges theorem: If we can construct the space, RH holds. -/
theorem rh_from_de_branges_construction
  (hHB : HermiteBiehlerClass XiGenerator) :
  RiemannHypothesis := by
  -- Definition of RH: ∀ s, ξ(s) = 0 → s.re = 1/2
  intro s hs_zero
  by_contra h_not_half

  -- If re s ≠ 1/2, then by functional equation symmetry, we can find a zero with re s > 1/2
  -- (or handle the re s < 1/2 case via s -> 1-s)
  have h_off_line : ∃ ρ, riemannXi_ext ρ = 0 ∧ 1/2 < ρ.re := by
    -- Use the functional equation: ξ(s) = ξ(1-s)
    by_cases h_gt : (1 : ℝ) / 2 < s.re
    · -- Case: s.re > 1/2, so s itself is the witness
      exact ⟨s, hs_zero, h_gt⟩
    · -- Case: s.re ≤ 1/2, but s.re ≠ 1/2, so s.re < 1/2
      have h_lt : s.re < (1 : ℝ) / 2 := by
        push_neg at h_gt
        cases' (h_gt.lt_or_eq) with h h
        · exact h
        · exact absurd h.symm h_not_half
      -- Use 1 - s as the witness
      use 1 - s
      constructor
      · -- ξ(1 - s) = 0 by the functional equation
        exact RH.AcademicFramework.CompletedXi.xi_ext_zero_symmetry s hs_zero
      · -- (1 - s).re > 1/2
        simp only [sub_re, one_re]
        linarith

  rcases h_off_line with ⟨ρ, hρ_zero, hρ_pos⟩

  -- Apply the HB contradiction
  have h_ne_zero := xi_rh_from_hb hHB ρ hρ_pos

  exact h_ne_zero hρ_zero

end RH.RS.DeBranges
