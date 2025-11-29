# Lean Formalization Backlog: Unconditional Proof Obligations

## 1. Context & Strategic Direction
**Objective:** Complete an unconditional proof of the Riemann Hypothesis using the "Active Route" ($\zeta$-normalized product certificate).

**Core Strategy (from `Riemann-active.txt`):**
1.  **$\zeta$-Normalization:** We work with the ratio $\mathcal J = \det_2(I-A) / (\mathcal O_\zeta \cdot \zeta)$. This eliminates the need for a "Prime Bandlimit" constant ($C_P$) or Archimedean constant ($C_\Gamma$).
2.  **Total Energy Control:** The central analytic difficulty is **Gap B**. We must prove that the *Total Energy* of the log-ratio on a Whitney box is $O(c)$ (bounded), even though the zero density grows as $\log T$. This works because the box width shrinks as $1/\log T$.
3.  **Neutralization:** To make the energy integral converge near zeros, we must use a local Blaschke product to "neutralize" the singular part of the field (Lemma 20 in manuscript).

---

## 2. The "Big Four" Gaps (Parallelizable Tracks)

These tracks are logically independent and can be worked on by separate agents.

### Track 1: Analytic Number Theory (Gap B - The Engine)
**Goal:** Discharge `VKZeroDensityHypothesis`, provide explicit `VKWeightedSumHypothesis`, and feed a numeric `Kxi_finite` to the final integration.

*   **Primary files:** `riemann/Riemann/AnalyticNumberTheory/ExponentialSums.lean`, `riemann/Riemann/AnalyticNumberTheory/VinogradovKorobov.lean`, `riemann/Riemann/AnalyticNumberTheory/VKZeroFreeRegion.lean`, `riemann/Riemann/RS/BWP/ZeroDensity.lean`.
*   **Current status:** All architectural reductions exist, but every file still contains `sorry`s representing the substantive estimates.
*   **Deliverables (must be fully proved in Lean):**
    1.  **Ford/Korobov Exponential Sums**
        * `dirichlet_poly_bound_from_exp_sum`: execute Abel summation rigorously (handle boundary + integral terms, interpolate partial sums for non-integer cutoffs).
        * `log_zeta_bound_from_exp_sum`: finish the positivity/log arguments to obtain the standard VK growth exponent.
    2.  **Integral Bound & Littlewood Link**
        * In `VinogradovKorobov.lean`, close `littlewood_jensen_rectangle`, `zero_density_from_integral_bound`, and every remaining lemma so that `VKIntegralBoundHypothesis` ⇒ `VKZeroDensityHypothesis` holds unconditionally.
        * Explicitly prove the inequality absorbing the `C'_\eta \log T` error into the `T^{1-\kappa}` main term for large `T`.
    3.  **Zero-Free Region**
        * Complete `zeta_zero_free_VK_conditional` by combining the Hadamard inequality, pole bounds, log-derivative control, and the Ford/Korobov estimates to show $\text{Re}\,\rho \le 1 - c/(\log t)^{2/3}$.
    4.  **Total Energy / Whitney Sums**
        * In `ZeroDensity.lean`, give an explicit geometric-series bound showing
          ```lean
          ((Finset.range (Nat.succ K)).sum (phi_of_nu …)) ≤ VK_B_budget
          ```
          for every Whitney interval, using the relation between `I.len`, `I.t0`, and the VK constants.
        * Provide any missing structural lemmas (e.g., `I.len = c / log I.t0`, nonnegativity facts) so the proof is self-contained.
    5.  **Neutralization / Local Polar Control**
        * Tie the analytic zero counts back to the `Green potential` decomposition: verify the neutralization lemmas that subtract the Blaschke part so that the energy integral converges. (Touch points: `ZeroDensity.lean`, `VKToCarlesonHypothesis.lean`.)

*   **Exit criteria:** `ZeroDensity.lean`, `VinogradovKorobov.lean`, `ExponentialSums.lean`, and `VKZeroFreeRegion.lean` compile with zero `sorry`s, yielding a concrete numerical `VK_B_budget` and `Kxi_finite` that can be consumed by `FinalIntegration.lean`.

*   **Pending sub-lemmas for Deliverable 1 (Abel summation)**
    1.  ✅ **`exp_sum_partial_bound_real`**
        Statement: for any `u ≥ 1`, the Ford hypothesis bounds the complex partial sum taken up to the real cutoff,
        \[
          \left\|\sum_{n ≤ ⌊u⌋₊} n^{-it}\right\| \le A u^{1-θ} t^{θ} + B u^{1/2}.
        \]
        (Needed to control the integrand in `sum_mul_eq_sub_integral_mul₀'`.)
    2.  ✅ **Discrete partial summation lemmas** (implemented in `ExponentialSums.lean`):
        - ✅ **`partial_summation_identity`**: For `N ≥ 1`,
          \[
            \sum_{n \in \text{range } N} a(n) f(n) = S(N) f(N-1) - \sum_{k \in \text{range }(N-1)} S(k+1)(f(k+1) - f(k))
          \]
          where $S(k) = \sum_{n \in \text{range } k} a(n)$.
        - ✅ **`partial_summation_norm_bound`**: If $\|S(k)\| \le B(k)$ for all $k \le N$, then
          \[
            \left\|\sum_{n \in \text{range } N} a(n) f(n)\right\| \le B(N) \|f(N-1)\| + \sum_{k < N-1} B(k+1) \|f(k+1) - f(k)\|.
          \]
    3.  ✅ **Floor/power comparison lemmas** (implemented in `ExponentialSums.lean`):
        - ✅ **`rpow_le_one_of_nonpos_exponent`**: if `M ≥ 1` and `γ ≤ 0`, then `M^γ ≤ 1`.
        - ✅ **`floor_nat_ge_half`**: for `X ≥ 2`, we have `X/2 ≤ ⌊X⌋₊`.
        - ✅ **`floor_pow_le_two_mul_pow`**: for `X ≥ 2` and `p ≥ -1`, we have `⌊X⌋₊^p ≤ 2 X^p`.
        - ✅ **`boundary_term_power_bound_with_ratio`**: for `X ≥ 2`, `θ ≤ 1`, `σ ≤ 1`, letting `m = ⌊X⌋₊`:
          \[
            m^{1-θ-σ} \le 2 X^{1-θ-σ} \quad \text{and} \quad m^{1/2-σ} \le 2 X^{1/2-σ}.
          \]
        - ✅ **Dirichlet sum reindexing**: `sum_range_succ_shift` / `dirichlet_sum_drop_zero` shift the ranges so only positive bases appear, eliminating the `n = 0` issue before applying Abel summation.
    4.  **Remaining work to complete `dirichlet_poly_bound_from_exp_sum`:**
        - Need to combine `partial_summation_norm_bound` with the Ford hypothesis bound on partial sums.
        - The sum $\sum_k B(k+1) \|f(k+1) - f(k)\|$ must be converted to an integral bound using the mean value theorem for $f(n) = n^{-\sigma}$.
        - The integral $\int_1^X u^{-(1+\sigma)} (Au^{1-\theta} t^\theta + Bu^{1/2}) du$ then evaluates to the target bound.
        - ✅ Telescoping sum control is done: `sum_power_diff_telescope` now gives the $\|n^{-\sigma} - (n+1)^{-\sigma}\|$ bounds, so the remaining steps reduce to the integral estimate and Abel summation bookkeeping.
        - ⛔ **New blocker:** Need a `partial_summation_norm_bound_from_one` variant whose boundary term uses the same positive cutoff as the Ford bound. With the current range-shifted lemma, the boundary term scales like $(m : ℝ)^{1-θ} (m-1)^{-σ}$ for $m = ⌊X⌋₊$, which can exceed the desired $X^{1-θ-σ}$ when $σ$ is close to $1$. Without this sharpened Abel summation statement we cannot fit the constants demanded in the hypothesis.

    5.  **Solution approach for the blocker (Abel summation from index 1):**
        The fix requires two new lemmas in `ExponentialSums.lean`:

        - **`partial_summation_identity_from_one`**: Abel summation for `Finset.Icc 1 N`:
          \[
            \sum_{n \in \text{Icc } 1\, N} a(n) f(n) = A(N) f(N) - \sum_{k \in \text{Ico } 1\, N} A(k)(f(k+1) - f(k))
          \]
          where $A(k) = \sum_{n \in \text{Icc } 1\, k} a(n)$. **Key:** boundary term uses $f(N)$ not $f(N-1)$.

        - **`partial_summation_norm_bound_from_one`**: The norm bound version with hypotheses:
          - `hS_bound : ∀ k, 1 ≤ k → k ≤ N → ‖∑ n ∈ Icc 1 k, a n‖ ≤ B k`
          - Conclusion: `‖∑ n ∈ Icc 1 N, a n * f n‖ ≤ B N * ‖f N‖ + ∑ k ∈ Ico 1 N, B k * ‖f (k+1) - f k‖`

        **Why this fixes the blocker:** The Ford hypothesis bounds `∑_{n ∈ range (k+1)} n^{-it}`. Since `0^{-it} = 0`, this equals `∑_{n ∈ Icc 1 k} n^{-it}`. Using the new lemma, the boundary term becomes `B(N) * ‖f(N)‖ = B(N) * N^{-σ}` where both factors use the same index `N`. This avoids the mismatch where the old formula had `B(N) * (N-1)^{-σ}`.

        **Implementation steps:**
        1. Add induction proof for `partial_summation_identity_from_one` using `Finset.Icc/Ico` union splitting
        2. Add helper `ford_bound_on_Icc` converting range-based Ford bound to Icc-based bound
        3. Add `dirichlet_term_zero_vanishes` showing `0^{-(σ + it)} = 0` for `t ≠ 0`
        4. Rewire `dirichlet_poly_bound_from_exp_sum` to use the new machinery

### Track 2: Geometric Function Theory (Gap C - The Pairing)
**Goal:** Prove the CR-Green machinery that ports boundary integrals to interior energy and handles the Blaschke neutralization.

*   **Primary files:** `riemann/Riemann/RS/BWP/CRCalculus.lean`, `riemann/Riemann/RS/BWP/WedgeHypotheses.lean`, `riemann/Riemann/RS/BWP/WedgeVerify.lean`.
*   **Deliverables:**
    - `test_function_energy_bound`, `boundary_term_control`, `cr_green_identity_on_tent`: full proofs for Lipschitz tent domains using measure-theory lemmas already imported.
    - `OuterCancellation` / `OuterEnergyBalance`: algebraic statements removing the outer function contribution on admissible windows, with constants tracked explicitly.
    - Window data lemmas: prove the estimates for cutoff functions (support, gradient bounds, normalization) needed to plug into Green’s identity.

### Track 3: Functional Analysis & Limits (Gap A - The Setup)
**Goal:** Prove the limiting behavior of the operator field and the phase velocity identity.

*   **Primary files:** `riemann/Riemann/RS/BWP/PhaseVelocityHypothesis.lean`, `riemann/Riemann/RS/BWP/SmoothedLimitHypothesis.lean` (if split).
*   **Deliverables:**
    - `SmoothedLimitHypothesis`: convergence of mollified log-modulus fields, including Bochner integrability and dominated convergence in the tent geometry.
    - `PhaseVelocityHypothesis`: prove the CR-Green pairing equals the boundary phase derivative (distributional equality + Poisson balayage), eliminating all `sorry`s around `measureBal`.
    - Prove `NoSingularInner` by implementing the F. & M. Riesz argument for the certificate’s boundary measure.

### Track 4: Harmonic Analysis (Gap D - The Wedge)
**Goal:** Prove the harmonic measure estimates that convert the energy budget into positivity on the boundary.

*   **Primary files:** `riemann/Riemann/RS/BWP/WedgeHypotheses.lean`, `riemann/Riemann/RS/BWP/WedgeVerify.lean`, `riemann/Riemann/RS/BWP/PoissonPlateau.lean` (if extracted).
*   **Deliverables:**
    - `PoissonPlateauHypothesis`: compute the explicit lower bound for the windowed Poisson integral (arctangent calculus) and show it depends only on the admissible window class.
    - `LebesgueDifferentiationHypothesis`: formalize the local-to-global wedge lemma via Lebesgue differentiation and Carleson packing, filling every `sorry`.
    - `HarmonicMeasureHypothesis`: supply the technical inequalities for harmonic measure on Carleson boxes (arctan/geometry lemmas).

---

## 3. Integration and Constants (The Glue)

*   **File:** `riemann/Riemann/RS/BWP/FinalIntegration.lean`
    *   **Status:** Architecturally complete.
    *   **Remaining obligation:** Provide an explicit numeric inequality `hUpsilon_lt : Upsilon < 1/2` once Track 1 supplies the concrete `Kxi` bound. No other `sorry`s should remain here once the upstream tracks are done.

---

## 4. Parallel Execution Guide

*   **Agent A (The Number Theorist):** Take **Track 1**. This is the hardest part. Start with `ExponentialSums.lean`.
*   **Agent B (The Geometer):** Take **Track 2**. This is self-contained calculus on domains.
*   **Agent C (The Analyst):** Take **Track 3 & 4**. These are standard analysis proofs (measure theory, limits) and can be grouped.

**Dependencies:**
*   Tracks 1, 2, and 3/4 are **mutually independent**.
*   `FinalIntegration.lean` depends on *all* tracks completing.
