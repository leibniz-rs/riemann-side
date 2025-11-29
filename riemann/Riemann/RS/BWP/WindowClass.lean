import Riemann.RS.BWP.Constants
import Riemann.RS.BWP.Definitions

/-!
# Admissible Window Classes

This module defines the structure for admissible windows used in the CR-Green pairing.
These windows must handle atom dodging (avoiding zeros on the line) while maintaining
uniform energy bounds.
-/

namespace RH.RS.BWP

open Real Complex

/-- Structure defining an admissible window family for CR-Green pairing. -/
structure AdmissibleWindow (I : RH.Cert.WhitneyInterval) where
  φ : ℝ → ℝ
  /-- Supported strictly inside the interval -/
  support_subset : Function.support φ ⊆ I.interval
  /-- Smoothness (C1 is sufficient for Green's identity, but C2 is better for extensions) -/
  smoothness : ContDiff ℝ 2 φ
  nonneg : ∀ t, 0 ≤ φ t
  integral_one : ∫ t, φ t = 1
  energy_bound : ℝ
  h_energy : ∫ t, (deriv φ t)^2 ≤ energy_bound

/-- The specific window class constants used in the proof. -/
def WindowConstants (Kxi : ℝ) : Prop :=
  Kxi ≤ RH.RS.BoundaryWedgeProof.Kxi_paper

end RH.RS.BWP
