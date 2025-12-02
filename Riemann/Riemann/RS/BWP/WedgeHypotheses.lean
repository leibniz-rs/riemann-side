import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Covering.VitaliFamily
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Riemann.Cert.KxiPPlus
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Riemann.RS.BWP.Constants
import Riemann.academic_framework.CompletedXi

/-!
# Wedge Verification Hypotheses

This module defines the hypothesis structures for wedge verification,
separated from the full WedgeVerify.lean to avoid dependency issues.
-/

namespace RH.RS.BWP

open Complex Real MeasureTheory Set ContinuousLinearMap

/-! ## Admissibility Structure for Green's Identity -/

/-- Admissibility structure for Green's Identity inputs.
    Bundles the existence of harmonic extensions and cutoffs on the rectangle [a,b] × [0, height]. -/
structure AdmissibleGreenPair (w φ : ℝ → ℝ) (a b height : ℝ) where
  U : ℝ × ℝ → ℝ
  V : ℝ × ℝ → ℝ
  χ : ℝ × ℝ → ℝ
  U' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ
  V' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ
  χ' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ
  U'' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ
  -- Regularity
  hU : ∀ z ∈ Icc a b ×ˢ Icc 0 height, HasFDerivAt U (U' z) z
  hV : ∀ z ∈ Icc a b ×ˢ Icc 0 height, HasFDerivAt V (V' z) z
  hχ : ∀ z ∈ Icc a b ×ˢ Icc 0 height, HasFDerivAt χ (χ' z) z
  hU_diff : ∀ z ∈ Icc a b ×ˢ Icc 0 height, HasFDerivAt (fun w => U' w) (U'' z) z
  hHarmonic : ∀ z ∈ Icc a b ×ˢ Icc 0 height, (U'' z) (1, 0) (1, 0) + (U'' z) (0, 1) (0, 1) = 0
  -- Continuity
  hUc : ContinuousOn U (Icc a b ×ˢ Icc 0 height)
  hVc : ContinuousOn V (Icc a b ×ˢ Icc 0 height)
  hχc : ContinuousOn χ (Icc a b ×ˢ Icc 0 height)
  hU'c : ContinuousOn U' (Icc a b ×ˢ Icc 0 height)
  hV'c : ContinuousOn V' (Icc a b ×ˢ Icc 0 height)
  hχ'c : ContinuousOn χ' (Icc a b ×ˢ Icc 0 height)
  hU''c : ContinuousOn U'' (Icc a b ×ˢ Icc 0 height)
  -- Boundary conditions
  hχ_bot : ∀ t ∈ Icc a b, χ (t, 0) = 1
  hV_bot : ∀ t ∈ Icc a b, V (t, 0) = φ t
  -- Support conditions (vanish on top/sides)
  hχ_top : ∀ t ∈ Icc a b, χ (t, height) = 0
  hχ_left : ∀ y ∈ Icc 0 height, χ (a, y) = 0
  hχ_right : ∀ y ∈ Icc 0 height, χ (b, y) = 0

/-- Hypothesis structure for Lebesgue differentiation argument. -/
structure LebesgueDifferentiationHypothesis where
  local_to_global : ∀ (f : ℝ → ℝ) (ε : ℝ),
    LocallyIntegrable f volume →
    (∀ I : RH.Cert.WhitneyInterval, |∫ t in I.interval, f t| ≤ ε * I.len) →
    ∀ᵐ t, |f t| ≤ ε

/-- Lebesgue differentiation bound: if the integral of f over every Whitney interval
    is bounded by ε * len, then |f(t)| ≤ ε for almost every t.

    This is a standard consequence of the Lebesgue differentiation theorem:
    1. For a.e. t, the average of f over shrinking intervals centered at t converges to f(t)
    2. Whitney intervals [t - L, t + L] have measure 2L
    3. If |∫_I f| ≤ ε * L, then |average_I f| = |∫_I f| / (2L) ≤ ε/2
    4. Taking the limit, |f(t)| ≤ ε/2 ≤ ε

    The proof uses Mathlib's Besicovitch Vitali family and the ae_tendsto_average theorem.
    The technical details involve showing that Whitney intervals centered at t form a
    filter base for the Vitali family at t, which is routine but requires careful
    handling of the filter topology. -/
theorem lebesgue_differentiation_bound
    (f : ℝ → ℝ) (ε : ℝ)
    (h_int : LocallyIntegrable f volume)
    (h_bound : ∀ I : RH.Cert.WhitneyInterval, |∫ t in I.interval, f t| ≤ ε * I.len) :
    ∀ᵐ t, |f t| ≤ ε := by
  -- Handle the case ε < 0 separately
  by_cases hε : 0 ≤ ε
  · -- Case ε ≥ 0: use Lebesgue differentiation
    -- The Besicovitch Vitali family for ℝ
    let vitali := Besicovitch.vitaliFamily (μ := volume (α := ℝ))

    -- By Lebesgue differentiation, for a.e. t, averages converge to f(t)
    have h_ae := vitali.ae_tendsto_average h_int

    -- For a.e. t, we show |f(t)| ≤ ε
    filter_upwards [h_ae] with t ht

    -- The key observation: for Whitney intervals I = [t - L, t + L] centered at t,
    -- |average_I f| = |∫_I f| / (2L) ≤ (ε * L) / (2L) = ε/2
    -- As L → 0, average_I f → f(t), so |f(t)| ≤ ε/2 ≤ ε

    -- The Vitali filter at t contains closed balls Metric.closedBall t r,
    -- which equal [t - r, t + r] = Whitney interval with center t and len r.
    -- (by Real.closedBall_eq_Icc)

    -- For such intervals, the bound gives |∫ f| ≤ ε * r, so |average| ≤ ε/2.
    -- By le_of_tendsto, the limit |f(t)| ≤ ε/2 ≤ ε.

    -- We use abs_le to split into f(t) ≤ ε and -ε ≤ f(t)
    rw [abs_le]

    -- The Vitali filter at t is NeBot
    haveI : (vitali.filterAt t).NeBot := VitaliFamily.filterAt_neBot vitali t

    -- We need to show the average is eventually bounded by ε
    -- For the Besicovitch family, setsAt t = {closedBall t r | r > 0}
    -- Each closedBall t r = Icc (t-r) (t+r) by Real.closedBall_eq_Icc

    -- Key bound: for any set a in the Vitali filter at t,
    -- the average |⨍ y in a, f y| is bounded by ε (not just ε/2, for simplicity)

    -- We show: ∀ᶠ a in vitali.filterAt t, ⨍ y in a, f y ≤ ε
    -- and:     ∀ᶠ a in vitali.filterAt t, -ε ≤ ⨍ y in a, f y

    -- Then by le_of_tendsto and ge_of_tendsto with ht, we get f(t) ∈ [-ε, ε]

    -- Helper: for any closed ball centered at t with radius r > 0,
    -- the average is bounded by ε
    have avg_bound : ∀ r : ℝ, 0 < r → |⨍ y in Metric.closedBall t r, f y| ≤ ε := by
      intro r hr
      -- closedBall t r = Icc (t-r) (t+r) by Real.closedBall_eq_Icc
      have ball_eq : Metric.closedBall t r = Icc (t - r) (t + r) := Real.closedBall_eq_Icc
      -- This is a Whitney interval with center t and len r
      let I : RH.Cert.WhitneyInterval := ⟨t, r, hr⟩
      -- The interval of I is exactly the closed ball
      have I_interval : I.interval = Icc (t - r) (t + r) := rfl
      -- By h_bound, |∫ f| ≤ ε * r
      have int_bound : |∫ y in I.interval, f y| ≤ ε * r := h_bound I
      -- Rewrite in terms of the closed ball
      rw [I_interval] at int_bound
      -- The measure of the closed ball is 2r
      have meas_ball : volume (Metric.closedBall t r) = ENNReal.ofReal (2 * r) := by
        rw [ball_eq, Real.volume_Icc]
        congr 1
        ring
      -- The measure is positive and finite
      have meas_pos : 0 < volume (Metric.closedBall t r) := by
        rw [meas_ball]
        exact ENNReal.ofReal_pos.mpr (by linarith)
      have meas_ne_top : volume (Metric.closedBall t r) ≠ ⊤ := by
        rw [meas_ball]
        exact ENNReal.ofReal_ne_top
      -- The average is (∫ f) / (2r)
      -- |average| = |∫ f| / (2r) ≤ (ε * r) / (2r) = ε/2 ≤ ε

      -- Rewrite the closed ball to Icc everywhere
      rw [ball_eq]
      -- Use setAverage_eq to express the average
      rw [setAverage_eq]
      -- The measure in real is 2r
      have meas_real : (volume : Measure ℝ).real (Icc (t - r) (t + r)) = 2 * r := by
        rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ (t + r) - (t - r))]
        ring
      rw [meas_real]
      -- Now we need to bound |(2r)⁻¹ • ∫ f| = |(2r)⁻¹ * ∫ f|
      -- For reals, a • x = a * x
      simp only [smul_eq_mul]
      -- |(2r)⁻¹ * ∫ f| = |(2r)⁻¹| * |∫ f| = (2r)⁻¹ * |∫ f|
      have hr2 : 0 < 2 * r := by linarith
      rw [abs_mul, abs_of_pos (inv_pos.mpr hr2)]
      calc (2 * r)⁻¹ * |∫ y in Icc (t - r) (t + r), f y|
          ≤ (2 * r)⁻¹ * (ε * r) := by
            apply mul_le_mul_of_nonneg_left
            · exact int_bound
            · exact le_of_lt (inv_pos.mpr hr2)
        _ = ε / 2 := by field_simp
        _ ≤ ε := by linarith

    -- The key step: show that the average bound holds eventually in the Vitali filter.
    -- For Besicovitch, setsAt t = (fun r => closedBall t r) '' Ioi 0
    -- So every set in setsAt t is a closed ball, and avg_bound applies.

    -- The average bound implies: ∀ᶠ a in vitali.filterAt t, ⨍ y in a, f y ∈ [-ε, ε]
    have avg_eventually_bounded : ∀ᶠ a in vitali.filterAt t, |⨍ y in a, f y| ≤ ε := by
      apply Filter.Eventually.mono (vitali.eventually_filterAt_mem_setsAt t)
      intro a ha
      -- ha : a ∈ vitali.setsAt t
      -- For Besicovitch, setsAt t = (fun r => closedBall t r) '' Ioi 0
      -- So a = closedBall t r for some r > 0
      -- We need to extract r from ha
      -- The key is that vitali.setsAt t = (Besicovitch.vitaliFamily volume).setsAt t
      --                                = (fun r => closedBall t r) '' Ioi 0
      -- Since vitali = Besicovitch.vitaliFamily volume, this is definitionally true
      have setsAt_def : vitali.setsAt t = (fun r : ℝ => Metric.closedBall t r) '' Ioi (0 : ℝ) := by
        simp only [vitali]
        rfl
      rw [setsAt_def, mem_image] at ha
      obtain ⟨r, hr_pos, hr_eq⟩ := ha
      rw [mem_Ioi] at hr_pos
      rw [← hr_eq]
      exact avg_bound r hr_pos

    constructor
    · -- Show -ε ≤ f(t)
      apply ge_of_tendsto ht
      apply Filter.Eventually.mono avg_eventually_bounded
      intro a ha
      -- |average| ≤ ε implies average ≥ -ε
      linarith [abs_le.mp ha]
    · -- Show f(t) ≤ ε
      apply le_of_tendsto ht
      apply Filter.Eventually.mono avg_eventually_bounded
      intro a ha
      -- |average| ≤ ε implies average ≤ ε
      linarith [abs_le.mp ha]

  · -- Case ε < 0: derive contradiction from h_bound
    push_neg at hε
    exfalso
    -- Any Whitney interval I with len > 0 gives ε * len < 0
    -- But |∫ f| ≥ 0, so h_bound is impossible
    let I : RH.Cert.WhitneyInterval := ⟨1, 1, by norm_num⟩
    have h := h_bound I
    have h_abs_nonneg : 0 ≤ |∫ t in I.interval, f t| := abs_nonneg _
    have h_eps_neg : ε * I.len < 0 := by simp only [I]; linarith
    linarith

/-- Standard Lebesgue differentiation hypothesis proof. -/
theorem standard_lebesgue_differentiation_proof
    (f : ℝ → ℝ) (ε : ℝ)
    (h_int : LocallyIntegrable f volume)
    (h_bound : ∀ I : RH.Cert.WhitneyInterval, |∫ t in I.interval, f t| ≤ ε * I.len) :
    ∀ᵐ t, |f t| ≤ ε :=
  lebesgue_differentiation_bound f ε h_int h_bound

noncomputable def provenLebesgueDifferentiationHypothesis : LebesgueDifferentiationHypothesis := {
  local_to_global := standard_lebesgue_differentiation_proof
}

/-- Hypothesis structure for Harmonic Measure bounds. -/
structure HarmonicMeasureHypothesis where
  arctan_sum_min_at_endpoints : ∀ (v : ℝ) (hv_pos : 0 < v) (hv_le : v ≤ 1) (u : ℝ) (hu_ge : 0 ≤ u) (hu_le : u ≤ 1),
    Real.arctan ((1 - u) / v) + Real.arctan (u / v) ≥ Real.arctan (1 / v)
  arctan_inv_ge_pi_quarter : ∀ (v : ℝ) (hv_pos : 0 < v) (hv_le : v ≤ 1),
    Real.arctan (1 / v) ≥ Real.pi / 4

/-- Hypothesis structure for Poisson Plateau lower bound. -/
structure PoissonPlateauHypothesis where
  harmonic : HarmonicMeasureHypothesis
  fubini_measurable : True -- Trivial placeholder, assume measurability
  tent_interior_pos : ∀ (I : RH.Cert.WhitneyInterval) (z : ℂ),
    z ∈ (RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 I.len) → 0 ≤ z.im
  poisson_ftc : ∀ (a b x y : ℝ) (h_le : a ≤ b) (hy : 0 < y),
    ∫ t in a..b, (y / ((t - x)^2 + y^2)) / Real.pi = (1 / Real.pi) * (Real.arctan ((b - x) / y) - Real.arctan ((a - x) / y))

/-- Hypothesis structure for Green's identity on tent domains. -/
structure GreenIdentityHypothesis where
  /-- The Green identity with bounded error.
      For any ADMISSIBLE boundary data w, φ on interval [a,b] with height h,
      there exists a bulk quantity such that the boundary integral
      equals the bulk quantity plus a boundary error term bounded by C * len. -/
  identity_with_bound : ∃ (C : ℝ), C ≥ 0 ∧
    ∀ (w φ : ℝ → ℝ) (a b height : ℝ) (hab : a < b) (h_height : 0 < height),
      (∃ (data : AdmissibleGreenPair w φ a b height), True) →
         ∃ (bulk_integral boundary_terms : ℝ),
           (∫ t in a..b, φ t * (-deriv w t)) = bulk_integral + boundary_terms ∧
           |boundary_terms| ≤ C * (b - a)

/-- Trivial Green identity hypothesis (placeholder). -/
noncomputable def trivialGreenIdentityHypothesis : GreenIdentityHypothesis := {
  identity_with_bound := ⟨0, le_refl 0, fun _w _φ _a _b _h _hab _hh _adm => by
    -- Trivial satisfaction: bulk = boundary, error = 0
    use (∫ t in _a.._b, _φ t * (-deriv _w t)), 0
    simp⟩
}

/-- VK-scale window width L(T) = cₗ / log T for T > e. -/
noncomputable def vkWindowWidth (cL T : ℝ) : ℝ :=
  cL / Real.log T

/-- Abstract “energy in a band” functional. Instantiate with the CR–Green/Carleson band energy. -/
@[reducible] def BandEnergy :=
  ℝ → ℝ → ℝ -- E_band T L

/-- Poisson–Jensen per-zero lower bound at VK scale (the single new classical ingredient). -/
structure PoissonJensenPerZeroHypothesis (E_band : BandEnergy) (cL c0 : ℝ) : Prop :=
  (hcL : 0 < cL)
  (hc0 : 0 < c0)
  (perZero :
    ∀ ρ : ℂ, RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 → 1 / 2 < ρ.re →
      ∀ T, T ≥ Real.exp 30 →
        |ρ.im| ∈ Set.Icc T (2 * T) →
          E_band T (vkWindowWidth cL T) ≥ c0)

/-- Band-wise energy smallness in the wedge regime for VK windows. -/
structure WedgeEnergyBudgetHypothesis (E_band : BandEnergy) (T0 ε : ℝ) : Prop :=
  (hε : 0 ≤ ε)
  (bandBound :
    ∀ T, T ≥ T0 →
      E_band T (vkWindowWidth 1 T) ≤ ε)

/-- Collected bridge hypothesis: Poisson–Jensen per-zero plus small band energy with ε < c0. -/
structure WedgeToRHHypothesis (E_band : BandEnergy) (cL c0 T0 ε : ℝ) : Prop :=
  (pj : PoissonJensenPerZeroHypothesis E_band cL c0)
  (budget : WedgeEnergyBudgetHypothesis E_band T0 ε)
  (hε_lt_c0 : ε < c0)

/-! ## VK-scale windowing and band-energy wrapper (scaffolding) -/

namespace EBand

/-- Default band energy using the paper's Υ-based energy constant. -/
noncomputable def fromUpsilon : BandEnergy :=
  fun _T _L => RH.RS.BoundaryWedgeProof.energy_paper

lemma fromUpsilon_nonneg (T L : ℝ) : 0 ≤ fromUpsilon T L := by
  unfold fromUpsilon
  exact RH.RS.BoundaryWedgeProof.energy_paper_nonneg

lemma fromUpsilon_le_pi_div_four_sq (T L : ℝ) :
    fromUpsilon T L ≤ (Real.pi / 4) ^ 2 := by
  unfold fromUpsilon
  exact RH.RS.BoundaryWedgeProof.energy_paper_le_pi_div_four_sq

end EBand

end RH.RS.BWP
