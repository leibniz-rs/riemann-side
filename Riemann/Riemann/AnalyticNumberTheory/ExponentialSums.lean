import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Ford-Vinogradov-Korobov Exponential Sum Bounds

This file formalizes the exponential sum bounds that underlie the Vinogradov-Korobov
zero-density estimates. These bounds control sums of the form ∑_{n≤X} n^{-it}.

## Main Definitions

* `FordExponentialSumHypothesis`: Hypothesis structure for exponential sum bounds
* `DirichletPolynomialBoundHypothesis`: Derived bounds for Dirichlet polynomials

## References

* Ford, K. (2002). "Vinogradov's integral and bounds for the Riemann zeta function"
* Korobov, N.M. (1958). "Estimates of trigonometric sums and their applications"
-/

open Real BigOperators Finset MeasureTheory
open scoped Interval

namespace RH.AnalyticNumberTheory.ExponentialSums

noncomputable section

/-! ## 0. Calculus Helper Lemmas -/

/-- Simple wrapper for `Real.rpow_le_one_of_one_le_of_nonpos`. -/
lemma rpow_le_one_of_nonpos_exponent {x γ : ℝ} (hx : 1 ≤ x) (hγ : γ ≤ 0) :
    x ^ γ ≤ (1 : ℝ) :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hγ

/-- For `X ≥ 2`, the discrete cutoff `⌊X⌋₊` is at least `X/2`. -/
lemma floor_nat_ge_half {X : ℝ} (hX : 2 ≤ X) :
    (X / 2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
  have h_le : X ≤ (⌊X⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one X).le
  have h_sub : X - 1 ≤ (⌊X⌋₊ : ℝ) := by linarith
  have h_div_le_sub : X / 2 ≤ X - 1 := by linarith
  exact le_trans h_div_le_sub h_sub

/-- A uniform comparison between real powers of `⌊X⌋₊` and `X`, with ratio at most `2`. -/
lemma floor_pow_le_two_mul_pow {X p : ℝ} (hX : 2 ≤ X) (hp_lower : -1 ≤ p) :
    (⌊X⌋₊ : ℝ) ^ p ≤ (2 : ℝ) * X ^ p := by
  have hX_pos : 0 < X := by linarith
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hm_nonneg : 0 ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast Nat.zero_le ⌊X⌋₊
  have hm_le_X : (⌊X⌋₊ : ℝ) ≤ X := by exact_mod_cast Nat.floor_le hX_nonneg
  have hm_ge_half : X / 2 ≤ (⌊X⌋₊ : ℝ) := floor_nat_ge_half hX
  by_cases hp_nonneg : 0 ≤ p
  · have h₁ := Real.rpow_le_rpow hm_nonneg hm_le_X hp_nonneg
    have hxpow_nonneg : 0 ≤ X ^ p := Real.rpow_nonneg hX_nonneg p
    calc (⌊X⌋₊ : ℝ) ^ p ≤ X ^ p := h₁
      _ ≤ 2 * X ^ p := by linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 1) hxpow_nonneg]
  · have hp_neg : p < 0 := lt_of_not_ge hp_nonneg
    have hxhalf_pos : 0 < X / 2 := by linarith
    have hpow_le := Real.rpow_le_rpow_of_nonpos hxhalf_pos hm_ge_half (le_of_lt hp_neg)
    have hxhalf_eq : (X / 2 : ℝ) ^ p = X ^ p * (2⁻¹ : ℝ) ^ p := by
      simp [div_eq_mul_inv, Real.mul_rpow hX_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
    have hhalf_le_two : (2⁻¹ : ℝ) ^ p ≤ 2 := by
      have hxpow : (2⁻¹ : ℝ) ^ p = (2 : ℝ) ^ (-p) := by
        simp [Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      have h_exp_le : -p ≤ 1 := by linarith
      simpa [hxpow] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h_exp_le
    have hxpow_nonneg : 0 ≤ X ^ p := Real.rpow_nonneg hX_nonneg p
    calc (⌊X⌋₊ : ℝ) ^ p ≤ (X / 2) ^ p := hpow_le
      _ = X ^ p * (2⁻¹ : ℝ) ^ p := hxhalf_eq
      _ ≤ X ^ p * 2 := by exact mul_le_mul_of_nonneg_left hhalf_le_two hxpow_nonneg
      _ = 2 * X ^ p := by ring

/-- A uniform control of the Abel boundary term: the gap between the discrete cutoff
    and the real parameter introduces at most a factor of `2`. -/
lemma boundary_term_power_bound_with_ratio
    {θ σ X : ℝ} (hX : 2 ≤ X) (hθ_le_one : θ ≤ 1) (hσ_hi : σ ≤ 1) :
    let m : ℝ := (⌊X⌋₊ : ℝ)
    (m ^ (1 - θ - σ) ≤ (2 : ℝ) * X ^ (1 - θ - σ)) ∧
    (m ^ (1 / 2 - σ) ≤ (2 : ℝ) * X ^ (1 / 2 - σ)) := by
  have hp₁_lower : -1 ≤ 1 - θ - σ := by linarith
  have hp₂_lower : -1 ≤ 1 / 2 - σ := by linarith
  exact ⟨floor_pow_le_two_mul_pow hX hp₁_lower, floor_pow_le_two_mul_pow hX hp₂_lower⟩

/-! ## 0.1 Discrete Partial Summation (Abel's Identity) -/

/-- Discrete partial summation identity (Abel's summation formula).
    For sequences `a : ℕ → ℂ` and `f : ℕ → ℂ`:
    ∑_{n ∈ range N} a(n) * f(n) = S(N) * f(N-1) - ∑_{k ∈ range (N-1)} S(k+1) * (f(k+1) - f(k))
    where S(k) = ∑_{n ∈ range k} a(n). -/
lemma partial_summation_identity (N : ℕ) (hN : 1 ≤ N)
    (a f : ℕ → ℂ) :
    ∑ n ∈ range N, a n * f n =
      (∑ n ∈ range N, a n) * f (N - 1) -
      ∑ k ∈ range (N - 1), (∑ n ∈ range (k + 1), a n) * (f (k + 1) - f k) := by
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN)
  subst hM
  induction M with
  | zero =>
    simp [range_one, range_zero]
  | succ M ih =>
    have hM_pos : 1 ≤ M + 1 := by omega
    rw [sum_range_succ]
    conv_lhs => rw [ih hM_pos]
    simp only [Nat.add_one_sub_one, sum_range_succ]
    ring

/-- Norm bound for partial summation: if `‖S(k)‖ ≤ B(k)` for all `k`, and the weights
    `|f(k) - f(k+1)|` are controlled, we get a bound on the full sum. -/
lemma partial_summation_norm_bound (N : ℕ) (hN : 1 ≤ N)
    (a f : ℕ → ℂ) (B : ℕ → ℝ)
    (hS_bound : ∀ k ≤ N, ‖∑ n ∈ range k, a n‖ ≤ B k) :
    ‖∑ n ∈ range N, a n * f n‖ ≤
      B N * ‖f (N - 1)‖ +
      ∑ k ∈ range (N - 1), B (k + 1) * ‖f (k + 1) - f k‖ := by
  rw [partial_summation_identity N hN]
  calc ‖(∑ n ∈ range N, a n) * f (N - 1) -
        ∑ k ∈ range (N - 1), (∑ n ∈ range (k + 1), a n) * (f (k + 1) - f k)‖
    ≤ ‖(∑ n ∈ range N, a n) * f (N - 1)‖ +
      ‖∑ k ∈ range (N - 1), (∑ n ∈ range (k + 1), a n) * (f (k + 1) - f k)‖ := norm_sub_le _ _
    _ ≤ ‖∑ n ∈ range N, a n‖ * ‖f (N - 1)‖ +
        ∑ k ∈ range (N - 1), ‖(∑ n ∈ range (k + 1), a n) * (f (k + 1) - f k)‖ := by
      gcongr
      · exact norm_mul_le _ _
      · exact norm_sum_le _ _
    _ ≤ B N * ‖f (N - 1)‖ +
        ∑ k ∈ range (N - 1), B (k + 1) * ‖f (k + 1) - f k‖ := by
      gcongr with k hk
      · exact hS_bound N (le_refl N)
      · calc ‖(∑ n ∈ range (k + 1), a n) * (f (k + 1) - f k)‖
          ≤ ‖∑ n ∈ range (k + 1), a n‖ * ‖f (k + 1) - f k‖ := norm_mul_le _ _
          _ ≤ B (k + 1) * ‖f (k + 1) - f k‖ := by
            gcongr
            exact hS_bound (k + 1) (by simp only [mem_range] at hk; omega)

/-- Shift a sum over `range (n + 1)` so every term is evaluated at a positive index.
    Useful when `f 0` is ill-behaved (e.g. negative powers). -/
lemma sum_range_succ_shift {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    ∀ n, ∑ k ∈ range (n + 1), f k =
        f 0 + ∑ k ∈ range n, f (k + 1)
  | 0 => by simp
  | Nat.succ n =>
      have hsum :
          ∑ k ∈ range (Nat.succ (Nat.succ n)), f k =
            ∑ k ∈ range (Nat.succ n), f k + f (Nat.succ n) := by
        simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using
          (Finset.sum_range_succ (fun k => f k) (Nat.succ n))
      have hshift :
          ∑ k ∈ range (Nat.succ n), f (k + 1) =
            ∑ k ∈ range n, f (k + 1) + f (Nat.succ n) := by
        simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using
          (Finset.sum_range_succ (fun k => f (k + 1)) n)
      calc
        ∑ k ∈ range (Nat.succ (Nat.succ n)), f k
            = ∑ k ∈ range (Nat.succ n), f k + f (Nat.succ n) := hsum
        _ = (f 0 + ∑ k ∈ range n, f (k + 1)) + f (Nat.succ n) := by
              simpa [Nat.succ_eq_add_one] using sum_range_succ_shift f n
        _ = f 0 + (∑ k ∈ range n, f (k + 1) + f (Nat.succ n)) := by
              simp [add_comm, add_left_comm, add_assoc]
        _ = f 0 + ∑ k ∈ range (Nat.succ n), f (k + 1) := by
              simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using hshift.symm

/-! ## 0.2 Power Difference Bounds -/

/-- Mean value theorem bound: for n ≥ 1 and σ > 0, the difference of consecutive
    negative powers is bounded by σ times the derivative at the left endpoint. -/
lemma power_diff_bound {n : ℕ} (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 < σ) :
    |(n : ℝ)^(-σ) - ((n : ℝ) + 1)^(-σ)| ≤ σ * (n : ℝ)^(-(1 + σ)) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1_pos : 0 < (n : ℝ) + 1 := by linarith
  -- The function x ↦ x^{-σ} is decreasing for x > 0, so n^{-σ} ≥ (n+1)^{-σ}
  have hdecr : (n : ℝ)^(-σ) ≥ ((n : ℝ) + 1)^(-σ) := by
    have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hneg : -σ ≤ 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos hn_pos hle hneg
  rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ)^(-σ) - ((n : ℝ) + 1)^(-σ))]
  -- Use mean value theorem
  have hcont : ContinuousOn (fun x => x^(-σ)) (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    apply ContinuousOn.rpow continuousOn_id continuousOn_const
    intro x hx
    left
    exact ne_of_gt (lt_of_lt_of_le hn_pos hx.1)
  have hderiv : ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun y => y^(-σ)) ((-σ) * x^(-σ - 1)) x := by
    intro x hx
    have hx_pos : 0 < x := lt_trans hn_pos hx.1
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx_pos))
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope (fun x => x^(-σ))
    (fun x => (-σ) * x^(-σ - 1)) (by linarith : (n : ℝ) < (n : ℝ) + 1) hcont
    (fun x hx => hderiv x hx)
  -- hξ_eq : (-σ) * ξ^(-σ - 1) = ((n+1)^{-σ} - n^{-σ}) / ((n+1) - n) = (n+1)^{-σ} - n^{-σ}
  have hslope_simp : ((n : ℝ) + 1)^(-σ) - (n : ℝ)^(-σ) = (-σ) * ξ^(-σ - 1) := by
    have h1 : ((n : ℝ) + 1) - (n : ℝ) = 1 := by ring
    calc ((n : ℝ) + 1)^(-σ) - (n : ℝ)^(-σ)
        = (((n : ℝ) + 1)^(-σ) - (n : ℝ)^(-σ)) / 1 := by ring
      _ = (((n : ℝ) + 1)^(-σ) - (n : ℝ)^(-σ)) / (((n : ℝ) + 1) - (n : ℝ)) := by rw [h1]
      _ = (-σ) * ξ^(-σ - 1) := hξ_eq.symm
  -- So n^{-σ} - (n+1)^{-σ} = σ * ξ^{-(σ+1)}
  have hdiff_eq : (n : ℝ)^(-σ) - ((n : ℝ) + 1)^(-σ) = σ * ξ^(-(σ + 1)) := by
    have h := hslope_simp
    calc (n : ℝ)^(-σ) - ((n : ℝ) + 1)^(-σ)
        = -(((n : ℝ) + 1)^(-σ) - (n : ℝ)^(-σ)) := by ring
      _ = -((-σ) * ξ^(-σ - 1)) := by rw [h]
      _ = σ * ξ^(-σ - 1) := by ring
      _ = σ * ξ^(-(σ + 1)) := by ring_nf
  rw [hdiff_eq]
  -- Since ξ ≥ n and -(σ+1) < 0, we have ξ^{-(σ+1)} ≤ n^{-(σ+1)}
  have hξ_ge_n : (n : ℝ) ≤ ξ := le_of_lt hξ_mem.1
  have hneg_exp : -(σ + 1) ≤ 0 := by linarith
  have hpow_le : ξ^(-(σ + 1)) ≤ (n : ℝ)^(-(σ + 1)) :=
    Real.rpow_le_rpow_of_nonpos hn_pos hξ_ge_n hneg_exp
  have hexp_eq : -(1 + σ) = -(σ + 1) := by ring
  have hmul_le : σ * ξ^(-(σ + 1)) ≤ σ * (n : ℝ)^(-(σ + 1)) :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hσ)
  calc σ * ξ^(-(σ + 1)) ≤ σ * (n : ℝ)^(-(σ + 1)) := hmul_le
    _ = σ * (n : ℝ)^(-(1 + σ)) := by rw [hexp_eq]

/-- For `n ≥ 1`, the norm of the complex power `(n : ℂ)^{-σ}` coincides with the real
power `(n : ℝ)^{-σ}`. This lets us transfer real bounds to the complex Dirichlet weights. -/
lemma norm_coe_nat_neg_rpow {n : ℕ} (hn : 1 ≤ n) (σ : ℝ) :
    ‖(n : ℂ) ^ (-σ)‖ = (n : ℝ) ^ (-σ) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hpow :
      ((n : ℂ) ^ (-σ)) = (((n : ℝ) ^ (-σ)) : ℂ) := by
    simpa using
      (Complex.ofReal_cpow (x := (n : ℝ)) (hx := hn_nonneg) (y := -σ)).symm
  have hnonneg : 0 ≤ (n : ℝ) ^ (-σ) :=
    Real.rpow_nonneg hn_nonneg _
  calc
    ‖(n : ℂ) ^ (-σ)‖ = ‖(((n : ℝ) ^ (-σ)) : ℂ)‖ := by simpa [hpow]
    _ = |(n : ℝ) ^ (-σ)| := by simp
    _ = (n : ℝ) ^ (-σ) := abs_of_nonneg hnonneg

/-- The `power_diff_bound` inequality transfers directly to the complex powers: the norm of
the difference between consecutive complex weights is controlled by the same real estimate. -/
lemma norm_coe_nat_neg_rpow_sub_succ_le {n : ℕ} (hn : 1 ≤ n)
    (σ : ℝ) (hσ : 0 < σ) :
    ‖(n : ℂ) ^ (-σ) - ((n + 1 : ℕ) : ℂ) ^ (-σ)‖ ≤
      σ * (n : ℝ) ^ (-(1 + σ)) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hpow_n :
      ((n : ℂ) ^ (-σ)) = (((n : ℝ) ^ (-σ)) : ℂ) := by
    simpa using
      (Complex.ofReal_cpow (x := (n : ℝ)) (hx := hn_nonneg) (y := -σ)).symm
  have hpow_succ :
      ((n + 1 : ℕ) : ℂ) ^ (-σ) =
        ((((n + 1 : ℝ) ) ^ (-σ)) : ℂ) := by
    have hsucc_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le (n + 1)
    simpa [Nat.cast_add, Nat.cast_one] using
      (Complex.ofReal_cpow (x := ((n + 1 : ℕ) : ℝ)) (hx := hsucc_nonneg) (y := -σ)).symm
  have hbound :=
    (power_diff_bound (n := n) hn σ hσ)
  have hbound' :
      |(n : ℝ) ^ (-σ) - ((n + 1 : ℝ) ^ (-σ))|
        ≤ σ * (n : ℝ) ^ (-(1 + σ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hbound
  calc
    ‖(n : ℂ) ^ (-σ) - ((n + 1 : ℕ) : ℂ) ^ (-σ)‖
        = |(n : ℝ) ^ (-σ) - ((n + 1 : ℝ) ^ (-σ))| := by
          simp [hpow_n, hpow_succ, Nat.cast_add, Nat.cast_one]
    _ ≤ σ * (n : ℝ) ^ (-(1 + σ)) := hbound'

/-- Reindex the Dirichlet polynomial so every term has a positive base. -/
lemma dirichlet_sum_drop_zero
    {σ t : ℝ} {m : ℕ} (hm : 1 ≤ m) (hσ_pos : 0 < σ) :
    ∑ n ∈ range m, (n : ℂ) ^ (-(σ + Complex.I * t)) =
      ∑ n ∈ range (m - 1), ((n + 1 : ℕ) : ℂ) ^ (-(σ + Complex.I * t)) := by
  have hm_pos : 0 < m := Nat.succ_le_iff.mp hm
  have hshift :=
    sum_range_succ_shift
      (fun n : ℕ => (n : ℂ) ^ (-(σ + Complex.I * t))) (m - 1)
  have hsum_ne : (σ + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have hσ_zero : σ = 0 := by
      simpa [Complex.add_re, Complex.ofReal_re, Complex.mul_re] using
        congrArg Complex.re h
    exact (ne_of_gt hσ_pos) hσ_zero
  have hexp_ne : (-(σ + Complex.I * t) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr hsum_ne
  have hzero_term :
      ((0 : ℂ) ^ (-(σ + Complex.I * t))) = 0 := by
    simpa using Complex.zero_cpow hexp_ne
  have hpred : Nat.succ (m - 1) = m := Nat.succ_pred_eq_of_pos hm_pos
  have hrewrite :
      ∑ n ∈ range m, (n : ℂ) ^ (-(σ + Complex.I * t)) =
        ((0 : ℂ) ^ (-(σ + Complex.I * t))) +
          ∑ n ∈ range (m - 1), ((n + 1 : ℕ) : ℂ) ^ (-(σ + Complex.I * t)) := by
    simpa [hpred, Nat.add_comm] using hshift
  simpa [hzero_term] using hrewrite

/-! ## 0.3 Telescoping Sum Bounds -/

/-- The sum of power differences is bounded by 1 (since it telescopes).
    For N ≥ 2 and σ > 0:
    ∑_{k=1}^{N-1} |k^{-σ} - (k+1)^{-σ}| = 1 - N^{-σ} ≤ 1 -/
lemma sum_power_diff_telescope (N : ℕ) (hN : 2 ≤ N) (σ : ℝ) (hσ : 0 < σ) :
    ∑ k ∈ range (N - 1), |((k + 1 : ℕ) : ℝ)^(-σ) - ((k + 2 : ℕ) : ℝ)^(-σ)| ≤ 1 := by
  -- The terms are all non-negative (decreasing function), so abs = the term itself
  have hdecr : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ)^(-σ) ≥ ((k + 2 : ℕ) : ℝ)^(-σ) := by
    intro k
    have hk1_pos : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hle : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      linarith
    have hneg : -σ ≤ 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos hk1_pos hle hneg
  have habs_eq : ∀ k ∈ range (N - 1),
      |((k + 1 : ℕ) : ℝ)^(-σ) - ((k + 2 : ℕ) : ℝ)^(-σ)| =
      ((k + 1 : ℕ) : ℝ)^(-σ) - ((k + 2 : ℕ) : ℝ)^(-σ) := by
    intro k _
    exact abs_of_nonneg (by linarith [hdecr k])
  rw [sum_congr rfl habs_eq]
  -- The sum telescopes: ∑_{k=0}^{N-2} (k+1)^{-σ} - (k+2)^{-σ} = 1^{-σ} - N^{-σ}
  have hN_pos : 0 < N := by omega
  have hN_cast_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hone_pow : (1 : ℝ)^(-σ) = 1 := Real.one_rpow (-σ)
  have hN_pow_nonneg : 0 ≤ (N : ℝ)^(-σ) := Real.rpow_nonneg (le_of_lt hN_cast_pos) _
  -- Use telescoping directly: the sum equals 1^{-σ} - N^{-σ} ≤ 1
  -- We prove this is ≤ 1 by noting 1 - N^{-σ} ≤ 1 since N^{-σ} ≥ 0
  have hbound :
      ∑ k ∈ range (N - 1),
          (((k + 1 : ℕ) : ℝ)^(-σ) - ((k + 2 : ℕ) : ℝ)^(-σ)) ≤ 1 := by
    classical
    have htelesc :
        ∑ k ∈ range (N - 1),
            (((k + 1 : ℕ) : ℝ)^(-σ) - ((k + 2 : ℕ) : ℝ)^(-σ)) =
          1 - (N : ℝ)^(-σ) := by
      have hflip :
          ∑ k ∈ range (N - 1),
              (((k + 1 : ℕ) : ℝ)^(-σ) - ((k + 2 : ℕ) : ℝ)^(-σ)) =
            -∑ k ∈ range (N - 1),
                (((k + 2 : ℕ) : ℝ)^(-σ) - ((k + 1 : ℕ) : ℝ)^(-σ)) := by
        calc
          _ = ∑ k ∈ range (N - 1),
                -(((k + 2 : ℕ) : ℝ)^(-σ) - ((k + 1 : ℕ) : ℝ)^(-σ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          _ = -∑ k ∈ range (N - 1),
                (((k + 2 : ℕ) : ℝ)^(-σ) - ((k + 1 : ℕ) : ℝ)^(-σ)) := by
            simp [Finset.sum_neg_distrib]
      have hsum :=
        (Finset.sum_range_sub
          (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)^(-σ)) (N - 1))
      have hsum_simp :
          ∑ k ∈ range (N - 1),
              (((k + 2 : ℕ) : ℝ)^(-σ) - ((k + 1 : ℕ) : ℝ)^(-σ)) =
            (N : ℝ)^(-σ) - 1 := by
        simpa [Nat.cast_add, Nat.cast_one, hone_pow] using hsum
      simpa [hsum_simp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hflip
    have hle_one : 1 - (N : ℝ)^(-σ) ≤ 1 := by
      linarith [hN_pow_nonneg]
    simpa [htelesc] using hle_one
  exact hbound

/-! ## 1. Exponential Sum Hypothesis -/

/-- Ford-Vinogradov-Korobov exponential sum bounds.

    The classical VK method gives bounds of the form:
    |∑_{n≤X} n^{-it}| ≤ A * X^{1-θ} * t^θ + B * X^{1/2}

    where θ depends on the exponent pair used (typically θ ≈ 1/6 for VK). -/
structure FordExponentialSumHypothesis where
  /-- Leading constant in the exponential sum bound. -/
  A_VK : ℝ
  /-- Secondary constant for the X^{1/2} term. -/
  B_VK : ℝ
  /-- The VK exponent (typically around 1/6). -/
  θ_VK : ℝ
  /-- The exponent is positive. -/
  hθ_pos : 0 < θ_VK
  /-- The exponent is less than 1. -/
  hθ_lt_one : θ_VK < 1
  /-- The constants are non-negative. -/
  hA_nonneg : 0 ≤ A_VK
  hB_nonneg : 0 ≤ B_VK
  /-- The main exponential sum bound.
      For X, t ≥ 2: |∑_{n≤X} n^{-it}| ≤ A * X^{1-θ} * t^θ + B * X^{1/2} -/
  exp_sum_bound : ∀ (X t : ℝ), 2 ≤ X → 2 ≤ t →
    ‖∑ n ∈ range ⌊X⌋₊, (n : ℂ) ^ (-(Complex.I * t))‖ ≤
      A_VK * X ^ (1 - θ_VK) * t ^ θ_VK + B_VK * X ^ (1/2 : ℝ)

/-- Default Ford exponential sum hypothesis with standard VK constants.
    These are placeholder values; the actual constants come from explicit computations. -/
def defaultFordHypothesis : FordExponentialSumHypothesis where
  A_VK := 10
  B_VK := 10
  θ_VK := 1/6
  hθ_pos := by norm_num
  hθ_lt_one := by norm_num
  hA_nonneg := by norm_num
  hB_nonneg := by norm_num
  exp_sum_bound := fun _X _t _hX _ht => by
    -- This requires the actual Ford-VK exponential sum analysis
    sorry

/-! ## 2. Dirichlet Polynomial Bounds -/

/-- Dirichlet polynomial bound hypothesis.

    For σ ∈ [1/2, 1], the exponential sum bound implies:
    |∑_{n≤X} n^{-σ-it}| ≤ A * X^{1-θ-σ} * t^θ + B * X^{1/2-σ} -/
structure DirichletPolynomialBoundHypothesis where
  /-- The underlying exponential sum hypothesis. -/
  ford : FordExponentialSumHypothesis
  /-- The Dirichlet polynomial bound derived from exponential sums. -/
  dirichlet_bound : ∀ (X t σ : ℝ), 2 ≤ X → 2 ≤ t → 1/2 ≤ σ → σ ≤ 1 →
    ‖∑ n ∈ range ⌊X⌋₊, (n : ℂ) ^ (-(σ + Complex.I * t))‖ ≤
      ford.A_VK * X ^ (1 - ford.θ_VK - σ) * t ^ ford.θ_VK +
      ford.B_VK * X ^ (1/2 - σ)

/-- Derive Dirichlet polynomial bounds from exponential sum bounds.

    The key observation is that n^{-σ-it} = n^{-σ} * n^{-it}, and
    partial summation converts the exponential sum bound to a Dirichlet bound. -/
theorem dirichlet_poly_bound_from_exp_sum
    (hyp : FordExponentialSumHypothesis)
    (X t σ : ℝ) (hX : 2 ≤ X) (ht : 2 ≤ t) (hσ_lo : 1/2 ≤ σ) (hσ_hi : σ ≤ 1) :
    ‖∑ n ∈ range ⌊X⌋₊, (n : ℂ) ^ (-(σ + Complex.I * t))‖ ≤
      hyp.A_VK * X ^ (1 - hyp.θ_VK - σ) * t ^ hyp.θ_VK +
      hyp.B_VK * X ^ (1/2 - σ) := by
  -- Strategy: Use partial summation (Abel's summation formula)
  -- The sum ∑_{n≤X} n^{-σ-it} can be rewritten using partial summation.
  -- Let a(n) = n^{-it} and f(n) = n^{-σ}, then we bound using:
  -- 1. The boundary term: B(N) * |f(N-1)| where B bounds the partial sums
  -- 2. The telescoping sum: ∑ B(k+1) * |f(k+1) - f(k)|
  -- The Ford hypothesis bounds B(k), and power_diff_bound controls the differences.
  sorry

/-- Construct a Dirichlet polynomial bound hypothesis from Ford hypothesis. -/
def mkDirichletPolynomialBoundHypothesis
    (ford : FordExponentialSumHypothesis) : DirichletPolynomialBoundHypothesis where
  ford := ford
  dirichlet_bound := fun X t σ hX ht hσ_lo hσ_hi =>
    dirichlet_poly_bound_from_exp_sum ford X t σ hX ht hσ_lo hσ_hi

/-! ## 3. Zeta Function Bounds from Exponential Sums -/

/-- Hypothesis for bounding |ζ(s)| using exponential sums.

    In the critical strip, the approximate functional equation expresses ζ(s)
    as a sum of two Dirichlet polynomials plus a small error. -/
structure ZetaBoundFromExpSumHypothesis where
  /-- The underlying Dirichlet polynomial hypothesis. -/
  dirichlet : DirichletPolynomialBoundHypothesis
  /-- Constant for the zeta bound. -/
  C_zeta : ℝ
  hC_pos : 0 < C_zeta
  /-- Bound for |ζ(σ+it)| in the critical strip. -/
  zeta_bound : ∀ (σ t : ℝ), 1/2 ≤ σ → σ ≤ 1 → 3 ≤ t →
    ‖riemannZeta (σ + t * Complex.I)‖ ≤
      C_zeta * t ^ ((1 - σ) * dirichlet.ford.θ_VK / (1 - dirichlet.ford.θ_VK))

/-- The bound for log|ζ(s)| derived from the zeta bound. -/
theorem log_zeta_bound_from_exp_sum
    (hyp : ZetaBoundFromExpSumHypothesis)
    (σ t : ℝ) (hσ_lo : 1/2 ≤ σ) (hσ_hi : σ ≤ 1) (ht : 3 ≤ t) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖ ≤
      Real.log hyp.C_zeta +
      ((1 - σ) * hyp.dirichlet.ford.θ_VK / (1 - hyp.dirichlet.ford.θ_VK)) * Real.log t := by
  -- Apply log to both sides of zeta_bound
  have _hzeta := hyp.zeta_bound σ t hσ_lo hσ_hi ht
  -- Need to handle the case where ζ might be zero (but it's not in this region for large t)
  sorry

end

end RH.AnalyticNumberTheory.ExponentialSums
