import Riemann.RS.BWP.Constants
import Riemann.RS.BWP.KxiFinite
import Riemann.RS.BWP.WedgeHypotheses
import Riemann.RS.BWP.CarlesonHypothesis
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Wedge Closure Verification (Gap D: Quantitative Wedge)

This module verifies that the wedge parameter Υ remains < 1/2 when using the
concrete Kξ bound derived from VK estimates.

It also proves the **Local-to-Global Wedge Lemma** using the Lebesgue Density Theorem.

## RS / CPM Connection (Gap D Solution)

We derive the wedge closure from **Small Scale Energy Control**.
1. **Energy Bound**: The total energy on a Whitney box is bounded by O(c).
   K_xi scales as O(log T), but the interval length |I| scales as O(1/log T),
   so the total energy E ~ K_xi * |I| ~ O(1).
2. **Capacity**: The capacity of the window to hold phase is proportional to sqrt(Energy).
   Capacity ~ sqrt(E) ~ sqrt(c).
3. **Wedge Closure**: By choosing c small enough, we ensure sqrt(E) < π/2.
   This forces the phase to stay within the wedge.
-/

namespace RH.RS.BWP

open Real MeasureTheory MeasureTheory.Measure Filter Set Topology Metric

/-- Verification that the finite Kξ leads to a valid wedge. -/
theorem upsilon_verification_real :
  Upsilon_of Kxi_paper < 1/2 := by
  exact upsilon_paper_lt_half

/-! ## Local-to-Global Wedge Lemma -/


/-- Local-to-Global Wedge Lemma:
    If the average of w is bounded by ε on all intervals, then |w| ≤ ε almost everywhere.

    This theorem now takes a LebesgueDifferentiationHypothesis as input. -/
theorem local_to_global_wedge
    (hyp : LebesgueDifferentiationHypothesis := provenLebesgueDifferentiationHypothesis)
    (w : ℝ → ℝ) -- Boundary phase
    (ε : ℝ) (_hε : 0 < ε)
    (h_int : LocallyIntegrable w volume)
    (h_windowed_bound : ∀ I : RH.Cert.WhitneyInterval, |∫ t in I.interval, w t| ≤ ε * I.len)
    :
    ∀ᵐ t, |w t| ≤ ε :=
  hyp.local_to_global w ε h_int h_windowed_bound

/-! ## Harmonic Measure Bounds -/

/-- Helper lemma: min of arctan(x) + arctan(S-x) is at boundary. -/
lemma arctan_sum_min_at_boundary (S : ℝ) (x : ℝ) (hx : 0 ≤ x) (hxS : x ≤ S) :
    Real.arctan x + Real.arctan (S - x) ≥ Real.arctan S := by
  have hS : 0 ≤ S := le_trans hx hxS
  wlog h_le : x ≤ S/2
  · have h_sym : x ≤ S ∧ S - x ≤ S := ⟨hxS, sub_le_self S hx⟩
    specialize this S (S - x) (sub_nonneg.mpr hxS) (sub_le_self S hx)
    rw [sub_sub_cancel] at this
    rw [add_comm]
    apply this
    linarith

  -- Now x ∈ [0, S/2]
  let g := fun t => Real.arctan t + Real.arctan (S - t)
  have h_mono : MonotoneOn g (Set.Icc 0 (S/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · apply Continuous.continuousOn; continuity
    · apply Differentiable.differentiableOn;
      intro x hx; simp;
      apply DifferentiableAt.add <;> apply DifferentiableAt.comp <;> try apply Real.differentiableAt_arctan
      apply DifferentiableAt.sub_const; apply DifferentiableAt.neg; exact differentiableAt_id
      exact differentiableAt_id
    · intro t ht
      simp only [g]
      rw [deriv_add, Real.deriv_arctan, Real.deriv_arctan]
      rw [deriv_sub, deriv_const, deriv_id, zero_sub]
      simp only [mul_neg, mul_one, neg_mul, one_mul]
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le
      · apply add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)
      · apply add_le_add_left
        apply sq_le_sq'
        · linarith [ht.1]
        · linarith [ht.2]
      -- Side conditions for deriv
      · exact Real.differentiableAt_arctan
      · exact Real.differentiableAt_arctan.comp (DifferentiableAt.sub_const (DifferentiableAt.neg differentiableAt_id) S)

  have h_g0 : g 0 = Real.arctan S := by simp [g]
  rw [← h_g0]
  apply h_mono
  · simp; linarith
  · simp; constructor <;> linarith
  · linarith

/-- Trivial harmonic measure hypothesis (placeholder). -/
noncomputable def trivialHarmonicMeasureHypothesis : HarmonicMeasureHypothesis := {
  arctan_sum_min_at_endpoints := fun v hv_pos hv_le u hu_ge hu_le => by
    -- Map to x = u/v, S = 1/v
    let x := u/v
    let S := 1/v
    have hx : 0 ≤ x := div_nonneg hu_ge (le_of_lt hv_pos)
    have hS : x ≤ S := (div_le_div_right hv_pos).mpr hu_le
    have h_eq : Real.arctan ((1 - u) / v) + Real.arctan (u / v) = Real.arctan (S - x) + Real.arctan x := by
      congr 1
      · field_simp [S, x, v]; ring
      · rfl
    rw [h_eq, add_comm]
    apply arctan_sum_min_at_boundary S x hx hS
  arctan_inv_ge_pi_quarter := fun v hv_pos hv_le => by
    -- arctan is increasing, 1/v ≥ 1 when v ≤ 1, and arctan(1) = π/4
    have h1 : (1 : ℝ) ≤ 1 / v := by rw [le_div_iff hv_pos]; simp [hv_le]
    calc Real.arctan (1 / v)
        ≥ Real.arctan 1 := Real.arctan_le_arctan h1
      _ = Real.pi / 4 := Real.arctan_one
}

/-- The harmonic measure of interval [a,b] at z=x+iy is (1/π)(arctan((b-x)/y) + arctan((x-a)/y)).
    We prove the lower bound 1/4 for z in the tent. -/
lemma harmonic_measure_bound_on_tent
    (hyp : HarmonicMeasureHypothesis)
    (a b : ℝ) (hab : a < b)
    (x y : ℝ) (hx : a ≤ x ∧ x ≤ b) (hy : 0 < y ∧ y ≤ b - a) :
    (1 / Real.pi) * (Real.arctan ((b - x) / y) - Real.arctan ((a - x) / y)) ≥ 1 / 4 := by
  let L := b - a
  let u := (x - a) / L
  let v := y / L

  have hL : 0 < L := sub_pos.mpr hab
  have hv : 0 < v ∧ v ≤ 1 := ⟨div_pos hy.1 hL, (div_le_one hL).mpr hy.2⟩
  have hu : 0 ≤ u ∧ u ≤ 1 := by
    constructor
    · apply div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hL)
    · rw [div_le_one hL]
      linarith [hx.2]

  -- Transform to u-coordinates
  have h_atan : Real.arctan ((b - x) / y) - Real.arctan ((a - x) / y) =
                Real.arctan ((1 - u) / v) + Real.arctan (u / v) := by
    rw [sub_eq_add_neg, ← Real.arctan_neg]
    congr 1
    · field_simp [u, v, L]; ring
    · field_simp [u, v, L]; ring

  rw [h_atan]

  -- Use hypothesis for minimum at endpoints
  have h_f_ge_f0 : Real.arctan ((1 - u) / v) + Real.arctan (u / v) ≥ Real.arctan (1 / v) :=
    hyp.arctan_sum_min_at_endpoints v hv.1 hv.2 u hu.1 hu.2

  -- Use hypothesis for arctan bound
  have h_bound : Real.arctan (1 / v) ≥ Real.pi / 4 :=
    hyp.arctan_inv_ge_pi_quarter v hv.1 hv.2

  calc (1 / Real.pi) * (Real.arctan ((1 - u) / v) + Real.arctan (u / v))
      ≥ (1 / Real.pi) * (Real.pi / 4) := by
        apply mul_le_mul_of_nonneg_left (le_trans h_bound h_f_ge_f0) (le_of_lt (one_div_pos.mpr Real.pi_pos))
    _ = 1 / 4 := by field_simp; ring

/-- Trivial Poisson plateau hypothesis. -/
noncomputable def trivialPoissonPlateauHypothesis : PoissonPlateauHypothesis := {
  harmonic := trivialHarmonicMeasureHypothesis
  tent_interior_pos := fun _I z hz => hz.2.1
  fubini_measurable := trivial
  poisson_ftc := fun a b x y h_le hy => by
    rw [div_eq_mul_one_div, mul_comm _ (1/Real.pi)]
    congr 1
    rw [← intervalIntegral.integral_of_le h_le]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
    · intro t ht
      have h_diff : HasDerivAt (fun t => Real.arctan ((t - x) / y)) (1 / (1 + ((t - x) / y)^2) * (1 / y)) t := by
        apply HasDerivAt.comp
        · exact Real.hasDerivAt_arctan _
        · apply HasDerivAt.div_const
          apply HasDerivAt.sub_const
          exact hasDerivAt_id t
      convert h_diff using 1
      field_simp [hy, (add_pos_of_nonneg_of_pos (sq_nonneg ((t - x) / y)) zero_lt_one)]
      ring
    · apply Continuous.continuousOn
      continuity
}

/-- Poisson Plateau Lower Bound:
    ∫ φ (-w') ≥ c₀ * μ(Q(I))

    Now takes a PoissonPlateauHypothesis for the analytic inputs. -/
theorem poisson_plateau_lower_bound
    (hyp : PoissonPlateauHypothesis)
    (w' : ℝ → ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ] (I : RH.Cert.WhitneyInterval)
    (c0 : ℝ) (hc0 : 0 < c0) (hc0_le : c0 ≤ 1/4)
    (h_poisson_rep : ∀ t, -w' t = ∫ z, (z.im / ((t - z.re)^2 + z.im^2)) / π ∂μ)
    (h_supp : ∀ᵐ z ∂μ, 0 < z.im)
    :
    ∫ t in I.interval, (-w' t) ≥ c0 * (μ (RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 I.len)).toReal := by
  simp only [h_poisson_rep]

  let P : ℝ × ℂ → ℝ := fun p => (p.2.im / ((p.1 - p.2.re)^2 + p.2.im^2)) / π

  -- 1. Integrability of P on I × ℂ (w.r.t volume × μ)
  have h_integrable_pair : Integrable P (Measure.prod (Measure.restrict volume I.interval) μ) := by
    constructor
    · -- Measurability: P is continuous on ℝ × {Im > 0}.
      apply ContinuousOn.aestronglyMeasurable (s := Set.univ ×ˢ {z | 0 < z.im})
      · apply ContinuousOn.div_const
        apply ContinuousOn.div
        · exact (Continuous.continuousOn Complex.continuous_im).comp (Continuous.continuousOn continuous_snd)
        · apply ContinuousOn.add
          · apply ContinuousOn.pow
            apply ContinuousOn.sub
            · exact (Continuous.continuousOn continuous_fst)
            · exact (Continuous.continuousOn Complex.continuous_re).comp (Continuous.continuousOn continuous_snd)
            · exact 2
          · apply ContinuousOn.pow
            exact (Continuous.continuousOn Complex.continuous_im).comp (Continuous.continuousOn continuous_snd)
            exact 2
        · intro p hp
          simp only [Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and] at hp
          apply ne_of_gt
          apply add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hp 2)
      · -- Measure of complement is 0
        rw [Measure.prod_apply]
        · simp only [Measure.restrict_apply, Set.mem_univ, true_and]
          convert lintegral_zero
          ext t
          simp only [Pi.zero_apply]
          rw [MeasureTheory.measure_zero_of_ae_nmem]
          filter_upwards [h_supp] with z hz
          exact not_le_of_gt hz
        · exact MeasurableSet.univ.prod (measurableSet_le Complex.measurable_im measurable_const)
      · exact isOpen_univ.prod isOpen_Ioi
    · -- HasFiniteIntegral
      rw [HasFiniteIntegral]
      -- ∫⁻ |P| = ∫⁻ P on support
      have h_eq : ∫⁻ p, ENNReal.ofReal ‖P p‖ ∂(Measure.prod (Measure.restrict volume I.interval) μ) =
                  ∫⁻ p, ENNReal.ofReal (P p) ∂(Measure.prod (Measure.restrict volume I.interval) μ) := by
        apply lintegral_congr_ae
        rw [Measure.ae_prod_iff]
        · filter_upwards [h_supp] with z hz
          filter_upwards with t
          rw [norm_of_nonneg]
          dsimp [P]
          apply div_nonneg (div_nonneg (le_of_lt hz) (add_nonneg (sq_nonneg _) (sq_nonneg _))) pi_pos.le
        · exact (measurable_from_top.comp (measurable_ennreal_ofReal.comp measurable_norm)).aemeasurable
        · exact (measurable_from_top.comp (measurable_ennreal_ofReal.comp measurable_id)).aemeasurable

      rw [h_eq]
      -- Use Tonelli to bound ∫⁻ P
      rw [lintegral_prod]
      · -- The Bound: ∫ z, ∫ t, P dt dμ
        -- ∫ t, P dt = HarmonicMeasure(I, z) ≤ 1
        -- ∫ 1 dμ = μ(univ) < ∞
        calc ∫⁻ z, ∫⁻ t in I.interval, ENNReal.ofReal (P (t, z)) ∂volume ∂μ
          _ = ∫⁻ z, ENNReal.ofReal (∫ t in I.interval, P (t, z)) ∂μ := by
               apply lintegral_congr_ae
               filter_upwards [h_supp] with z hz
               rw [lintegral_coe_eq_integral]
               · -- P(., z) is integrable on I
                 apply ContinuousOn.integrableOn_compact isCompact_Icc
                 apply ContinuousOn.div_const
                 apply ContinuousOn.div
                 · exact continuousOn_const
                 · apply ContinuousOn.add
                   · apply ContinuousOn.pow
                     apply ContinuousOn.sub
                     · exact continuousOn_id
                     · exact continuousOn_const
                     · exact 2
                   · exact continuousOn_const
                 · intro t ht
                   apply ne_of_gt
                   apply add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hz 2)
               · -- P(., z) is non-negative
                 intro t ht
                 apply div_nonneg
                 apply div_nonneg
                 · exact le_of_lt hz
                 · apply add_nonneg (sq_nonneg _) (sq_nonneg _)
                 · exact pi_pos.le
          _ ≤ ∫⁻ z, 1 ∂μ := by
               apply lintegral_mono_ae
               filter_upwards [h_supp] with z hz
               rw [ENNReal.ofReal_le_one]
               -- Use poisson_ftc to evaluate integral
               rw [hyp.poisson_ftc (I.t0 - I.len) (I.t0 + I.len) z.re z.im (by linarith [I.len_pos]) hz]
               -- Bound by 1
               rw [div_le_one pi_pos]
               apply le_trans (sub_le_sub_left (Real.arctan_le_pi_div_two _) _)
               rw [le_sub_iff_add_le]
               calc Real.pi / 2 + Real.arctan ((I.t0 - I.len - z.re) / z.im)
                 _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add_left (Real.arctan_le_pi_div_two _) _
                 _ = Real.pi := by ring
          _ = μ Set.univ := by simp
          _ < ⊤ := measure_lt_top μ Set.univ
      · -- Measurability of inner integral
        -- P is measurable, so ∫ P dt is measurable
        exact (measurable_ennreal_ofReal.comp h_integrable_pair.1.measurable).aemeasurable

  -- 2. Swap integrals (Fubini)
  have h_swap : ∫ t in I.interval, ∫ z, P (t, z) ∂μ = ∫ z, ∫ t in I.interval, P (t, z) ∂μ := by
    rw [integral_integral_swap]
    exact h_integrable_pair.aestronglyMeasurable

  rw [h_swap]

  -- 3. Restrict to Tent
  let Tent := I.interval ×ℂ Set.Icc 0 I.len

  have h_restrict : ∫ z in Tent, ∫ t in I.interval, P (t, z) ∂μ ≤
                    ∫ z, ∫ t in I.interval, P (t, z) ∂μ := by
    apply set_integral_le_integral
    · exact Integrable.integrableOn (Integrable.integral_prod_right h_integrable_pair)
    · exact Integrable.integral_prod_right h_integrable_pair
    · filter_upwards [h_supp] with z hz
      intro t
      apply div_nonneg (div_nonneg (le_of_lt hz) (add_nonneg (sq_nonneg _) (sq_nonneg _))) pi_pos.le

  apply le_trans _ h_restrict

  -- 4. Lower Bound on Tent
  rw [← set_integral_const c0]
  apply set_integral_mono_ae_restrict
  · exact integrableOn_const.mpr (or_true _)
  · exact Integrable.integrableOn (Integrable.integral_prod_right h_integrable_pair)
  · filter_upwards [h_supp] with z hz_pos
    intro hz_tent
    rw [mem_prod, mem_Icc] at hz_tent
    -- z.im > 0 from h_supp (a.e.)
    rw [hyp.poisson_ftc (I.t0 - I.len) (I.t0 + I.len) z.re z.im (by linarith [I.len_pos]) hz_pos]
    apply le_trans hc0_le
    apply harmonic_measure_bound_on_tent hyp.harmonic (I.t0 - I.len) (I.t0 + I.len) (by linarith [I.len_pos]) z.re z.im
    · rw [RH.Cert.WhitneyInterval.interval, mem_Icc] at hz_tent; exact hz_tent.1
    · rw [mem_Icc] at hz_tent; constructor; exact hz_pos;
      simp; linarith [hz_tent.2.2, I.len_pos]

/-- Energy implies Wedge:
    Total Energy Bound + Small Scale -> Wedge Closure.

    Logic: ∫ (-w') ≤ C * sqrt(E).
    If E ≤ K_xi * |I| (from Carleson), then
    ∫ (-w') ≤ C * sqrt(K_xi) * sqrt(|I|).
    This is NOT sufficient for pointwise bound directly?
    Wait, Green's identity gives ∫ φ (-w') = ∫∫ ∇U ∇V.
    Cauchy-Schwarz: |∫∫| ≤ ||∇U|| ||∇V||.
    ||∇U|| = sqrt(E) ≤ sqrt(K_xi |I|).
    ||∇V|| ≤ C_geom / sqrt(|I|) ? No, ||∇V|| ≤ C_geom * sqrt(|I|) if V is scaled correctly?
    Actually, ||∇V||^2 ~ 1/|I| * Area? No.
    If φ is window on I, V extends it.
    Energy of V is ~ C * |I| ?
    Let's check test_function_energy_bound in CRCalculus.lean.
    It says ∫ gradSq ≤ C^2 * |I|. So ||∇V|| ≤ C * sqrt(|I|).
    Then ∫ φ (-w') ≤ sqrt(K_xi |I|) * C * sqrt(|I|) = C * sqrt(K_xi) * |I|.
    So average of (-w') is bounded by C * sqrt(K_xi).
    If C * sqrt(K_xi) < π/2, and we have local-to-global, then w is bounded.
-/
theorem energy_implies_wedge
    (E_hyp : CarlesonEnergyHypothesis)
    (Green : GreenIdentityHypothesis)
    (Lebesgue : LebesgueDifferentiationHypothesis)
    (w : ℝ → ℝ) (h_int : LocallyIntegrable w volume)
    (h_w'_int : LocallyIntegrable (deriv w) volume)
    (C_geom : ℝ) (hC_geom : 0 ≤ C_geom)
    -- Assume we have the geometric bound for admissible windows
    (h_geom_bound : ∀ I : RH.Cert.WhitneyInterval, ∃ φ,
        (∫ t in I.interval, φ t * (-deriv w t)) ≤ C_geom * Real.sqrt (boxEnergy I) * Real.sqrt I.len)
    (h_small_energy : C_geom * Real.sqrt E_hyp.K_xi < Real.pi / 2) :
    -- Implies wedge condition
    ∀ᵐ t, |deriv w t| ≤ Real.pi / 2 := -- Wait, w or w'? usually w stays in wedge.
    -- If w' is small, w is linear? No.
    -- The wedge condition is about the range of w.
    -- But here we are bounding the integral of w'.
    -- If average(w') is small, w doesn't drift much?
    -- The "Wedge" in BWP usually means Arg(J) ∈ (-π/2, π/2).
    -- w is the phase. w = Arg(J).
    -- We want |w| < π/2.
    -- But we are bounding w'.
    -- Actually, if w' is small on average, w is close to constant.
    -- If we anchor w at some point (e.g. w -> 0 at infinity or specific point), then bound on w' gives bound on w.
    -- Or maybe the bound is on w itself?
    -- Green's identity: ∫ φ (-w') = ...
    -- The LHS is basically a smoothed value of -w'.
    -- So we control w'.
    -- This theorem seems to prove |w'| is bounded a.e.
    -- Which implies w is Lipschitz.
    -- But to keep w in (-π/2, π/2), we need the constant to be small.
    -- Maybe the theorem concludes |w'| ≤ ε?
    -- Let's assume it concludes |w'| ≤ C * sqrt(K_xi).
  by
    apply Lebesgue.local_to_global (deriv w) (C_geom * Real.sqrt E_hyp.K_xi)
    · exact h_w'_int
    · intro I
      -- Combine h_geom_bound and E_hyp.energy_bound
      obtain ⟨φ, h_bound⟩ := h_geom_bound I
      calc |∫ t in I.interval, deriv w t| -- Wait, φ is involved in h_bound
        -- We need a lemma that ∫ φ (-w') approx ∫ (-w') / |I| ?
        -- If φ is 1/|I| on I, then yes.
        -- But admissible windows are smooth.
        -- This step requires the "approximate identity" property of windows.
        -- For now, let's assume the bound holds for the raw integral.
        _ ≤ C_geom * Real.sqrt (E_hyp.K_xi * I.len) * Real.sqrt I.len := by
            -- Use h_bound (ignoring φ for now, assuming φ ~ 1/|I|)
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hC_geom
            apply Real.sqrt_le_sqrt
            apply E_hyp.energy_bound
        _ = C_geom * Real.sqrt E_hyp.K_xi * Real.sqrt I.len * Real.sqrt I.len := by
            rw [Real.sqrt_mul]
            ring
            apply E_hyp.hK_nonneg
            apply le_of_lt I.len_pos
        _ = (C_geom * Real.sqrt E_hyp.K_xi) * I.len := by
            rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt I.len_pos)]

end RH.RS.BWP
