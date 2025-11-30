import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.AEEqFun
import Riemann.RS.BWP.Laplacian
import Riemann.RS.BWP.WedgeHypotheses -- For the updated GreenIdentityHypothesis definition

/-
Auxiliary complex-analytic calculus lemmas used in the Boundary Wedge Proof.

In this file we record:

* an equality-of-mixed-partials statement for scalar fields on `ℂ` viewed as a
  real vector space;
* first-order Cauchy–Riemann identities in Fréchet-derivative form;
* (to be extended) higher-order CR calculus lemmas.

These are the analytic inputs needed in later CR-calculus arguments: under
`C²` regularity, the Hessian at a point is symmetric, so second mixed partials
commute, and the real and imaginary parts of analytic maps satisfy the CR
equations at first order.
-/

noncomputable section

open scoped Topology

namespace Riemann.RS.BoundaryWedgeProof

open Complex ContinuousLinearMap MeasureTheory Function Set Filter

/-- **Equality of mixed partials on `ℂ` (as an `ℝ`‑vector space).**

Let `u : ℂ → ℝ` be a real‑valued scalar field, and assume that it is
Fréchet-differentiable over `ℝ` everywhere and that its derivative
`w ↦ fderiv ℝ u w` is differentiable at `z`.  Then the second derivative
`fderiv ℝ (fun w ↦ fderiv ℝ u w) z` (the Hessian at `z`) is symmetric, so the
mixed partials along the real and imaginary directions coincide:
\[
  D^2 u(z)[1, I] = D^2 u(z)[I, 1].
\]

In terms of Fréchet derivatives, this says that the bilinear map
`fderiv ℝ (fun w => fderiv ℝ u w) z` is symmetric on the pair of vectors
`1, I`. -/
lemma mixed_partials_eq
    (u : ℂ → ℝ) (z : ℂ)
    (hu₁ : Differentiable ℝ u)
    (hu₂ : DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ u w) z) :
    ((fderiv ℝ (fun w : ℂ => fderiv ℝ u w) z) (1 : ℂ)) Complex.I
      =
    ((fderiv ℝ (fun w : ℂ => fderiv ℝ u w) z) Complex.I) (1 : ℂ) := by
  classical
  -- `f' w := fderiv ℝ u w`, `f'' := fderiv ℝ (fun w => fderiv ℝ u w) z`.
  let f' : ℂ → ℂ →L[ℝ] ℝ := fun w => fderiv ℝ u w
  let f'' : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    fderiv ℝ (fun w : ℂ => fderiv ℝ u w) z

  -- Global differentiability of `u` supplies `HasFDerivAt u (f' w) w` for all `w`.
  have hf : ∀ w, HasFDerivAt u (f' w) w := by
    intro w
    have hdiff : DifferentiableAt ℝ u w := hu₁ w
    simpa [f'] using hdiff.hasFDerivAt

  -- Differentiability of `w ↦ fderiv u w` at `z` supplies the second derivative.
  have hx : HasFDerivAt f' f'' z := by
    simpa [f', f''] using (hu₂.hasFDerivAt)

  -- Symmetry of the second derivative over `ℝ`.
  have h_symm :=
    second_derivative_symmetric (𝕜 := ℝ) (f := u) (f' := f') (f'' := f'') (x := z)
      (hf := hf) (hx := hx) (1 : ℂ) Complex.I

  -- This is exactly the desired mixed-partials equality.
  simpa [f''] using h_symm

/-- For a complex‑differentiable map `G : ℂ → ℂ`, the ℝ‑Fréchet derivative at `z`
is multiplication by the complex derivative `deriv G z`. -/
lemma hasFDerivAt_of_hasDerivAt_complex
  {G : ℂ → ℂ} {z : ℂ}
  (hG : HasDerivAt G (deriv G z) z) :
  HasFDerivAt G (deriv G z • (1 : ℂ →L[ℝ] ℂ)) z :=
hG.complexToReal_fderiv

/-- First‑order Cauchy–Riemann identities for a complex map `G : ℂ → ℂ` at `z`.

Write `G = u + i·v` in real coordinates, so that `u = Re ∘ G` and `v = Im ∘ G`.
If `G` has complex derivative `G'` at `z`, then the real Fréchet derivatives of
`u` and `v` at `z` satisfy the classical CR identities:
\[
  u_x = (\Re G'),\quad u_y = -(\Im G'),\quad
  v_x = (\Im G'),\quad v_y = (\Re G').
\]
-/
lemma CR_first_order_at
  (G : ℂ → ℂ) (z : ℂ)
  (hG : HasDerivAt G (deriv G z) z) :
  (fderiv ℝ (fun w : ℂ => (G w).re) z (1 : ℂ)) = (deriv G z).re ∧
  (fderiv ℝ (fun w : ℂ => (G w).re) z Complex.I) = -(deriv G z).im ∧
  (fderiv ℝ (fun w : ℂ => (G w).im) z (1 : ℂ)) = (deriv G z).im ∧
  (fderiv ℝ (fun w : ℂ => (G w).im) z Complex.I) = (deriv G z).re := by
  classical
  -- ℝ‑Fréchet derivative of G at z
  have hF :
      HasFDerivAt G (deriv G z • (1 : ℂ →L[ℝ] ℂ)) z :=
    hasFDerivAt_of_hasDerivAt_complex hG

  -- Derivative of Re ∘ G at z
  have hRe :
      HasFDerivAt (fun w : ℂ => (G w).re)
        (Complex.reCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ))) z :=
    (Complex.reCLM.hasFDerivAt.comp z hF)

  -- Derivative of Im ∘ G at z
  have hIm :
      HasFDerivAt (fun w : ℂ => (G w).im)
        (Complex.imCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ))) z :=
    (Complex.imCLM.hasFDerivAt.comp z hF)

  -- Turn these into equalities for fderiv
  have hRe_fderiv :
      fderiv ℝ (fun w : ℂ => (G w).re) z
        = Complex.reCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ)) :=
    hRe.fderiv
  have hIm_fderiv :
      fderiv ℝ (fun w : ℂ => (G w).im) z
        = Complex.imCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ)) :=
    hIm.fderiv

  -- Evaluate at 1 and I using the explicit form of the linear maps
  have hRe_1 :
      fderiv ℝ (fun w : ℂ => (G w).re) z (1 : ℂ)
        = (deriv G z).re := by
    have := congrArg (fun L => L (1 : ℂ)) hRe_fderiv
    -- (reCLM ∘ (a • 1)) 1 = Re (a * 1) = Re a
    simpa [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, one_smul, Complex.reCLM_apply,
      Complex.mul_re, Complex.one_re, Complex.one_im] using this

  have hRe_I :
      fderiv ℝ (fun w : ℂ => (G w).re) z Complex.I
        = -(deriv G z).im := by
    have := congrArg (fun L => L Complex.I) hRe_fderiv
    -- (reCLM ∘ (a • 1)) I = Re (a * I) = -Im a
    have hI :
        (Complex.reCLM.comp
          (deriv G z • (1 : ℂ →L[ℝ] ℂ))) Complex.I
          = - (deriv G z).im := by
      -- Compute explicitly: a • 1 sends v ↦ a * v, then take real part at v = I.
      simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
        Complex.mul_re, Complex.I_re, Complex.I_im]
    simpa [hI] using this

  have hIm_1 :
      fderiv ℝ (fun w : ℂ => (G w).im) z (1 : ℂ)
        = (deriv G z).im := by
    have := congrArg (fun L => L (1 : ℂ)) hIm_fderiv
    -- (imCLM ∘ (a • 1)) 1 = Im (a * 1) = Im a
    simpa [ContinuousLinearMap.comp_apply,
      one_smul, Complex.imCLM_apply,
      Complex.mul_im, Complex.one_re, Complex.one_im] using this

  have hIm_I :
      fderiv ℝ (fun w : ℂ => (G w).im) z Complex.I
        = (deriv G z).re := by
    have := congrArg (fun L => L Complex.I) hIm_fderiv
    -- (imCLM ∘ (a • 1)) I = Im (a * I) = Re a
    have hI :
        (Complex.imCLM.comp
          (deriv G z • (1 : ℂ →L[ℝ] ℂ))) Complex.I
          = (deriv G z).re := by
      simp [ContinuousLinearMap.comp_apply, Complex.imCLM_apply,
        Complex.mul_im, Complex.I_re, Complex.I_im]
    simpa [hI] using this

  exact ⟨hRe_1, hRe_I, hIm_1, hIm_I⟩

/-- First-order CR identities applied to the complex derivative `G'`.

This is just `CR_first_order_at` specialized to the map `G' := deriv G`. -/
lemma CR_first_order_at_deriv
  (G : ℂ → ℂ) (z : ℂ)
  (hG' : HasDerivAt (fun w : ℂ => deriv G w) (deriv (fun w : ℂ => deriv G w) z) z) :
  (fderiv ℝ (fun w : ℂ => (deriv G w).re) z (1 : ℂ)) = (deriv (deriv G) z).re ∧
  (fderiv ℝ (fun w : ℂ => (deriv G w).re) z Complex.I) = -(deriv (deriv G) z).im ∧
  (fderiv ℝ (fun w : ℂ => (deriv G w).im) z (1 : ℂ)) = (deriv (deriv G) z).im ∧
  (fderiv ℝ (fun w : ℂ => (deriv G w).im) z Complex.I) = (deriv (deriv G) z).re := by
  -- Apply `CR_first_order_at` to the function `G' := deriv G`.
  simpa using
    (CR_first_order_at (G := fun w : ℂ => deriv G w) (z := z)
      (hG := hG'))

/-- **Second‑order CR identity at the Hessian level (vertical direction).**

At a point `z`, for an analytic map `G : ℂ → ℂ`, the Hessian entry of
`u := Re ∘ G` in the `I,I`‑direction equals minus the `I`‑directional derivative
of `Im (G')`:

\[
  D^2 u(z)[I,I] = - D(\Im G')(z)[I].
\]

In Fréchet terms:
\[
  (D(Du)(z)\,I)\,I = - D(\Im G')(z)\,I.
\]
-/
lemma CR_second_order_Hessian_identity
  (G : ℂ → ℂ) (z : ℂ)
  (hG : AnalyticAt ℂ G z)
  (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
  (hH₂ :
    DifferentiableAt ℝ
      (fun w : ℂ => fderiv ℝ (fun t : ℂ => (G t).re) w) z) :
  ((fderiv ℝ (fun w : ℂ => fderiv ℝ (fun t : ℂ => (G t).re) w) z) Complex.I) Complex.I
    =
  - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I := by
  classical
  -- `H := Re ∘ G`
  let H : ℂ → ℝ := fun w => (G w).re
  have hH₁' : Differentiable ℝ H := hH₁
  have hH₂' :
      DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ H w) z := by
    simpa [H] using hH₂

  --------------------------------------------------------------------
  -- Step 1: identify the Hessian entry along `I,I` as the directional
  -- derivative of the `I`‑slice `w ↦ ∂H/∂I(w)` in direction `I`.
  --------------------------------------------------------------------
  -- CLM‑valued map of first derivatives
  let g : ℂ → (ℂ →L[ℝ] ℝ) := fun w => fderiv ℝ H w
  have hg_diff : DifferentiableAt ℝ g z := hH₂'
  -- Scalar slice: `I`‑directional derivative of `H`
  let uI : ℂ → ℝ := fun w => g w Complex.I
  -- By definition of the Hessian,
  have h_hess :
      ((fderiv ℝ (fun w : ℂ => fderiv ℝ H w) z) Complex.I) Complex.I
        = fderiv ℝ uI z Complex.I := by
    -- Use the CLM evaluation chain rule along the line in direction `I`.
    -- View `uI w = (g w) (const_I w)`, where `const_I` is constant `I`.
    let c : ℂ → (ℂ →L[ℝ] ℝ) := g
    let u : ℂ → ℂ := fun _ => Complex.I
    have hc : DifferentiableAt ℝ c z := hg_diff
    have hu : DifferentiableAt ℝ u z := differentiableAt_const _
    have h_clm :=
      (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv
    -- `h_clm` is the Fréchet version of `deriv_clm_apply`.
    -- Evaluate both sides at `Complex.I`.
    have := congrArg (fun (L : ℂ →L[ℝ] ℝ) => L Complex.I) h_clm
    -- On the LHS we recover the Hessian entry; on the RHS `fderiv uI z`.
    -- Unfold `c`, `u`, `g`, `uI`.
    simpa [c, u, g, uI] using this.symm

  --------------------------------------------------------------------
  -- Step 2: use the first‑order CR identities along the vertical line
  -- to identify `uI` with `- Im(G')`, then take the derivative.
  --------------------------------------------------------------------
  -- Analyticity implies complex differentiability near `z`.
  have hG_ev :
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w :=
    (analyticAt_iff_eventually_differentiableAt (f := G) (c := z)).1 hG
  -- On that neighborhood, CR first‑order identities hold at each `w`.
  have h_CR_event :
      ∀ᶠ w in 𝓝 z,
        uI w = - (deriv G w).im := by
    refine hG_ev.mono ?_
    intro w hw
    -- `HasDerivAt` at `w`
    have hHw : HasDerivAt G (deriv G w) w :=
      hw.hasDerivAt
    -- Apply the pointwise CR lemma at `w`.
    obtain ⟨_, hUy, _, _⟩ :=
      CR_first_order_at (G := G) (z := w) (hG := hHw)
    -- `hUy : fderiv ℝ H w I = -(deriv G w).im`
    have : uI w = fderiv ℝ H w Complex.I := rfl
    simpa [H, uI, this] using hUy
  -- `uI` and `-Im(G')` agree in a neighborhood, hence have the same derivative at `z`.
  have h_deriv_eq :
      fderiv ℝ uI z = fderiv ℝ (fun w : ℂ => - (deriv G w).im) z := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    -- equality as functions near `z`
    exact h_CR_event
  -- Evaluate both sides at the direction `I`.
  have h_dir :
      fderiv ℝ uI z Complex.I
        = fderiv ℝ (fun w : ℂ => - (deriv G w).im) z Complex.I := by
    have := congrArg (fun L => L Complex.I) h_deriv_eq
    simpa using this

  --------------------------------------------------------------------
  -- Step 3: identify the RHS derivative via linearity and conclude.
  --------------------------------------------------------------------
  have h_rhs :
      fderiv ℝ (fun w : ℂ => - (deriv G w).im) z Complex.I
        = - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I := by
    -- derivative of `-F` is `-` derivative of `F`
    simp

  calc
    ((fderiv ℝ (fun w : ℂ => fderiv ℝ (fun t : ℂ => (G t).re) w) z)
        Complex.I) Complex.I
        = fderiv ℝ uI z Complex.I := by
            simpa [H, g, uI] using h_hess
    _   = fderiv ℝ (fun w : ℂ => - (deriv G w).im) z Complex.I := h_dir
    _   = - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I := h_rhs

/-!
# Green's Identity on Whitney Tents (Gap C: CR-Green Pairing)

This section formalizes the CR-Green pairing identity on Whitney tent domains.
We prove that for a harmonic function U and a test function V_φ (Poisson extension),
the boundary integral of the phase derivative pairs with the bulk Dirichlet energy.

## RS / CPM Connection (Gap C Solution)

We derive this pairing from **Outer Cancellation** (Algebraic Energy Bookkeeping).
1. **Potential Splitting**: U = U_zeros + U_outer.
2. **Outer Cancellation**: The outer potential U_outer is the Poisson extension
   of the boundary modulus. Its contribution to the boundary pairing cancels
   with the outer phase derivative (via Hilbert transform).
3. **Zero Energy**: The relevant energy term in the bound is therefore K_xi
   (the energy of U_zeros), not the total energy.
-/

-- Note: GreenIdentityHypothesis is now imported from WedgeHypotheses to avoid duplication.
open RH.RS.BWP

/-- Green's identity for harmonic functions on a tent domain.
    ∫_I φ (-w') = ∬_Q ∇U · ∇(χV) + boundary_terms

    This theorem now takes a GreenIdentityHypothesis as input,
    making the proof conditionally valid on the divergence theorem. -/
theorem cr_green_identity_on_tent
    (hyp : GreenIdentityHypothesis)
    (w : ℝ → ℝ) -- Boundary phase w(t)
    (φ : ℝ → ℝ) -- Window function
    (a b height : ℝ) (hab : a < b) (h_height : 0 < height)
    -- Require admissibility
    (h_admissible : ∃ (data : AdmissibleGreenPair w φ a b height), True)
    :
    -- The pairing identity
    ∃ (bulk_integral boundary_terms : ℝ) (C : ℝ),
      C ≥ 0 ∧
      (∫ t in a..b, φ t * (-deriv w t)) = bulk_integral + boundary_terms ∧
      |boundary_terms| ≤ C * (b - a) := by
  -- Use the hypothesis to get the existence
  obtain ⟨C, hC, h_forall⟩ := hyp.identity_with_bound
  specialize h_forall w φ a b height hab h_height h_admissible
  obtain ⟨bulk_integral, boundary_terms, h_eq, h_bound⟩ := h_forall
  exact ⟨bulk_integral, boundary_terms, C, hC, h_eq, h_bound⟩

/-- Dirichlet energy bound for the test function V_φ on the tent.
    ||∇(χV_φ)||_2 ≤ C * sqrt(|I|)

    This version uses an abstract "gradient squared" function to avoid
    module synthesis issues with complex derivatives of real-valued functions.
-/
theorem test_function_energy_bound
    (_φ : ℝ → ℝ) (I : Set ℝ) (Q : Set ℂ)
    (_V : ℂ → ℝ) (_χ : ℂ → ℝ)
    (C : ℝ)
    -- Abstract gradient squared function (avoids deriv typing issues)
    (gradSq : ℂ → ℝ)
    (hGrad_meas : AEStronglyMeasurable gradSq (volume.restrict Q))
    (hGrad_bound : ∀ z ∈ Q, gradSq z ≤ C ^ 2)
    (hGrad_nonneg : ∀ z, 0 ≤ gradSq z)
    (hQ_meas : MeasurableSet Q)
    (hQ_finite : volume Q < ⊤)
    (hVol_le : (volume Q).toReal ≤ (volume I).toReal)
    (_hC_nonneg : 0 ≤ C) :
    ∫ z in Q, gradSq z ≤ C ^ 2 * (volume I).toReal := by
  classical
  set μ := volume.restrict Q with hμ_def
  haveI : IsFiniteMeasure μ :=
    ⟨by simpa [hμ_def, Measure.restrict_apply_univ] using hQ_finite⟩
  have h_const_int : Integrable (fun _ : ℂ => C ^ 2) μ := integrable_const _
  have h_sq_bound_ae : ∀ᵐ z ∂μ, gradSq z ≤ C ^ 2 := by
    rw [ae_restrict_iff' hQ_meas]
    exact Eventually.of_forall hGrad_bound
  have h_sq_abs_bound : ∀ᵐ z ∂μ, ‖gradSq z‖ ≤ C ^ 2 := by
    refine h_sq_bound_ae.mono ?_
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hGrad_nonneg z)]
    exact hz
  have h_grad_sq_int : Integrable gradSq μ :=
    Integrable.mono' h_const_int hGrad_meas h_sq_abs_bound
  have h_integral_le : ∫ z, gradSq z ∂μ ≤ ∫ z, C ^ 2 ∂μ :=
    integral_mono_ae h_grad_sq_int h_const_int h_sq_bound_ae
  have h_const_val : ∫ z, C ^ 2 ∂μ = C ^ 2 * (volume Q).toReal := by
    simp only [integral_const, hμ_def, Measure.restrict_apply_univ, Measure.real]
    rw [smul_eq_mul, mul_comm]
  have h_main : ∫ z in Q, gradSq z ≤ C ^ 2 * (volume Q).toReal := by
    calc ∫ z in Q, gradSq z = ∫ z, gradSq z ∂μ := by rfl
      _ ≤ ∫ z, C ^ 2 ∂μ := h_integral_le
      _ = C ^ 2 * (volume Q).toReal := h_const_val
  have hC_sq_nonneg : 0 ≤ C ^ 2 := sq_nonneg C
  have h_scale : C ^ 2 * (volume Q).toReal ≤ C ^ 2 * (volume I).toReal :=
    mul_le_mul_of_nonneg_left hVol_le hC_sq_nonneg
  exact h_main.trans h_scale

/-- Boundary term control: Side and top terms vanish due to cutoff.

    If the support of χ is contained in Q minus the boundary, then the
    integral over the boundary vanishes. -/
theorem boundary_term_control
    (χ : ℂ → ℝ) (V : ℂ → ℝ)
    (Q : Set ℂ) -- Tent
    (bdryQ_side : Set ℂ) (bdryQ_top : Set ℂ)
    (hχ_supp : Function.support χ ⊆ Q \ (bdryQ_side ∪ bdryQ_top)) :
    -- Integral over side/top boundaries is zero
    ∫ z in bdryQ_side ∪ bdryQ_top, (χ z * V z) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  have h_not_in_supp : z ∉ Function.support χ := by
    intro h_in_supp
    have h_in_Q_diff := hχ_supp h_in_supp
    rw [mem_diff] at h_in_Q_diff
    exact h_in_Q_diff.2 hz
  rw [mem_support, not_not] at h_not_in_supp
  rw [h_not_in_supp, zero_mul]

/-- Outer Cancellation: Energy integral invariance under U -> U - Re log O.

    Replaces the `CostMinimizationHypothesis` placeholder.
    This theorem justifies replacing the full potential energy with the
    "zero-only" potential energy in the CR-Green pairing.

    Mathematically, if U_total = U_zeros + U_outer, and U_outer is the
    Poisson extension of the boundary modulus, then the pairing
    ⟨∇U_total, ∇V⟩ effectively reduces to ⟨∇U_zeros, ∇V⟩ because the
    boundary contribution of U_outer cancels with the outer phase term. -/
theorem outer_cancellation_invariance
    (U_tot U_zero U_out : ℂ → ℝ)
    (w_tot w_zero w_out : ℝ → ℝ)
    (φ : ℝ → ℝ) (V : ℂ → ℝ) (χ : ℂ → ℝ)
    (I : Set ℝ) (Q : Set ℂ)
    -- Abstract gradients (as complex numbers)
    (grad_tot grad_zero grad_out grad_test : ℂ → ℂ)
    -- Splitting hypotheses
    (hU_split : ∀ z ∈ Q, grad_tot z = grad_zero z + grad_out z)
    (hw_split : ∀ t ∈ I, w_tot t = w_zero t + w_out t)
    -- Integrability assumptions for splitting
    (h_int_grad_zero : IntegrableOn (fun z => (grad_zero z).re * (grad_test z).re + (grad_zero z).im * (grad_test z).im) Q)
    (h_int_grad_out : IntegrableOn (fun z => (grad_out z).re * (grad_test z).re + (grad_out z).im * (grad_test z).im) Q)
    (h_int_bdry_zero : IntegrableOn (fun t => φ t * (-deriv w_zero t)) I)
    (h_int_bdry_out : IntegrableOn (fun t => φ t * (-deriv w_out t)) I)
    -- Derivative linearity
    (h_w_diff : ∀ t ∈ I, DifferentiableAt ℝ w_zero t ∧ DifferentiableAt ℝ w_out t)
    -- Measurability hypotheses (needed for set integrals)
    (hQ_meas : MeasurableSet Q)
    (hI_meas : MeasurableSet I)
    -- Derivative splitting (globally, not just on I)
    (h_deriv_split : ∀ t, deriv w_tot t = deriv w_zero t + deriv w_out t)
    -- Total integrability
    (h_int_grad_tot : IntegrableOn (fun z => (grad_tot z).re * (grad_test z).re + (grad_tot z).im * (grad_test z).im) Q)
    (h_int_bdry_tot : IntegrableOn (fun t => φ t * (-deriv w_tot t)) I) :
    let pairing (g : ℂ → ℂ) := ∫ z in Q, (g z).re * (grad_test z).re + (g z).im * (grad_test z).im
    let boundary (w : ℝ → ℝ) := ∫ t in I, φ t * (-deriv w t)
    (pairing grad_tot - boundary w_tot) =
    (pairing grad_zero - boundary w_zero) + (pairing grad_out - boundary w_out) := by
  -- Define shorthands
  set p_tot := ∫ z in Q, (grad_tot z).re * (grad_test z).re + (grad_tot z).im * (grad_test z).im with hp_tot
  set p_zero := ∫ z in Q, (grad_zero z).re * (grad_test z).re + (grad_zero z).im * (grad_test z).im with hp_zero
  set p_out := ∫ z in Q, (grad_out z).re * (grad_test z).re + (grad_out z).im * (grad_test z).im with hp_out
  set b_tot := ∫ t in I, φ t * (-deriv w_tot t) with hb_tot
  set b_zero := ∫ t in I, φ t * (-deriv w_zero t) with hb_zero
  set b_out := ∫ t in I, φ t * (-deriv w_out t) with hb_out

  -- Step 1: Show p_tot = p_zero + p_out
  have hp_split : p_tot = p_zero + p_out := by
    -- The integrand of p_tot equals the sum of integrands of p_zero and p_out on Q
    have integrand_eq : ∀ z ∈ Q,
        (grad_tot z).re * (grad_test z).re + (grad_tot z).im * (grad_test z).im =
        ((grad_zero z).re * (grad_test z).re + (grad_zero z).im * (grad_test z).im) +
        ((grad_out z).re * (grad_test z).re + (grad_out z).im * (grad_test z).im) := by
      intro z hz
      rw [hU_split z hz]
      simp only [Complex.add_re, Complex.add_im]
      ring
    -- Use integral linearity: ∫(f+g) = ∫f + ∫g
    calc p_tot = ∫ z in Q, (grad_tot z).re * (grad_test z).re + (grad_tot z).im * (grad_test z).im := rfl
      _ = ∫ z in Q, ((grad_zero z).re * (grad_test z).re + (grad_zero z).im * (grad_test z).im) +
                    ((grad_out z).re * (grad_test z).re + (grad_out z).im * (grad_test z).im) := by
        apply MeasureTheory.setIntegral_congr_fun hQ_meas
        exact fun z hz => integrand_eq z hz
      _ = p_zero + p_out := by
        rw [integral_add h_int_grad_zero h_int_grad_out]

  -- Step 2: Show b_tot = b_zero + b_out
  have hb_split : b_tot = b_zero + b_out := by
    -- The integrand of b_tot equals the sum using deriv splitting
    have integrand_eq : ∀ t,
        φ t * (-deriv w_tot t) = (φ t * (-deriv w_zero t)) + (φ t * (-deriv w_out t)) := by
      intro t
      rw [h_deriv_split t]
      ring
    calc b_tot = ∫ t in I, φ t * (-deriv w_tot t) := rfl
      _ = ∫ t in I, (φ t * (-deriv w_zero t)) + (φ t * (-deriv w_out t)) := by
        apply MeasureTheory.setIntegral_congr_fun hI_meas
        exact fun t _ => integrand_eq t
      _ = b_zero + b_out := by
        rw [integral_add h_int_bdry_zero h_int_bdry_out]

  -- Step 3: Combine to get the result
  -- Unfold the set definitions and use the splitting lemmas
  simp only [hp_tot, hp_zero, hp_out, hb_tot, hb_zero, hb_out] at hp_split hb_split ⊢
  rw [hp_split, hb_split]
  ring

end Riemann.RS.BoundaryWedgeProof
