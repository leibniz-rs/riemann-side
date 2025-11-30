import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import StrongPNT.PNT3_RiemannZeta
import Riemann.AnalyticNumberTheory.VinogradovKorobov

open Complex Real

theorem hadamard_zeta_inequality (σ t : ℝ) (hσ : 1 < σ) :
    3 * Real.log ‖riemannZeta σ‖ +
    4 * Real.log ‖riemannZeta (σ + t * I)‖ +
    Real.log ‖riemannZeta (σ + 2 * t * I)‖ ≥ 0 := by
  sorry



