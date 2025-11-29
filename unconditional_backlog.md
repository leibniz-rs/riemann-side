# Unconditional Proof Backlog: Riemann Hypothesis Formalization

**Date:** November 2025
**Project:** Riemann Hypothesis Formalization (Hardy-Schur Pinch Route)
**Target Audience:** Analytic Number Theorists and Lean Formalization Team

---

## Executive Summary

This document identifies the specific mathematical theorems that must be **proven** (not assumed or derived from RS principles) to convert the current "conditionally valid" Lean formalization into a fully **unconditional** proof of the Riemann Hypothesis.

The current proof relies on a set of `Hypothesis` structures (Gaps A, B, C, D) justified by Recognition Science (RS) principles. To achieve unconditional status in the classical sense (ZFC + Mathlib), these hypotheses must be discharged by proving the underlying analytic theorems.

---

## Gap A: Phase-Velocity Identity (Distributional Limits)

**Current State:**
`PhaseVelocityHypothesis` assumes the identity $-w'(t) = \pi \mu_{\text{zeros}} + \pi \sum m_\gamma \delta_\gamma$. This is justified by RS Flux Conservation (T3).

**Unconditional Requirement:**
Prove the distributional limit of the Hilbert transform for the specific function $J(s)$ constructed from $\zeta$.

**Classical Proof Obligations:**
1.  **No Singular Inner Factor:** Prove that the function $J(s) = \det_2(I-A(s))/(\mathcal{O}(s)\xi(s))$ has no singular inner factor in its canonical factorization.
    *   *Strategy:* Show that $\log |J(s)|$ behaves well enough at the boundary (e.g., VMOA or similar condition) to preclude singular measures.
    *   *Difficulty:* High. Requires careful estimates of the infinite product $\det_2$ near the boundary.
2.  **Distributional Convergence:** Prove that the sequence of smoothed phase derivatives converges in $\mathcal{D}'(\mathbb{R})$ to the Poisson balayage.
    *   *Strategy:* Use the uniform $L^1$ bounds (Gap B) and the continuity of the Hilbert transform on distributions.

---

## Gap B: Carleson Energy (Vinogradov-Korobov Estimates) - THE BIGGEST TASK

**Current State:**
`VKZeroDensityHypothesis` assumes a zero-density bound $N(\sigma, T) \le C \cdot T^{1-\kappa(\sigma)}$ and derives $K_\xi \le 0.16$. This is justified by RS Prime Sieve / 8-Tick constraints.

**Unconditional Requirement:**
**Prove** the Vinogradov-Korobov zero-density estimate starting from the definition of $\zeta$.

**Classical Proof Obligations:**
1.  **Littlewood-Jensen Lemma:** Formalize the lemma relating zero counts in a rectangle to the integral of $\log |\zeta|$ on the boundary.
    *   *Status:* `sorry` in `VinogradovKorobov.lean`.
    *   *Difficulty:* Medium/High.
2.  **Exponential Sum Estimates:** Formalize the Van der Corput method (A and B processes) or Vinogradov's method to bound exponential sums $\sum n^{it}$.
    *   *Status:* Not started.
    *   *Difficulty:* Very High.
3.  **Integral Mean Values:** Use the large sieve or mean value theorems to bound $\int |\zeta(\sigma+it)|^k dt$.
    *   *Status:* Not started.
    *   *Difficulty:* Very High.
4.  **Zero-Density Theorem:** Combine the above to prove $N(\sigma, T) \ll T^{A(1-\sigma)^{3/2}}$.
    *   *Status:* Not started.
    *   *Difficulty:* Extreme.

**Note:** This gap represents a multi-month (or year) formalization project of deep analytic number theory.

---

## Gap C: CR-Green Pairing (Metric Geometry)

**Current State:**
`GreenIdentityHypothesis` assumes Green's identity on Whitney tents. `CostMinimizationHypothesis` assumes outer orthogonality. Justified by RS Cost Uniqueness (T5).

**Unconditional Requirement:**
Prove Green's Identity for harmonic functions on the non-smooth Whitney tent domain.

**Classical Proof Obligations:**
1.  **Green's Identity on Lipschitz Domains:** Prove that the divergence theorem holds for the specific "sawtooth" geometry of Whitney tents.
    *   *Strategy:* Approximate the domain by smooth domains or use geometric measure theory results for Lipschitz domains.
    *   *Difficulty:* Medium.
2.  **Trace Theorems:** Ensure the boundary values of the test functions $V_\varphi$ are well-defined in the Sobolev sense.
    *   *Difficulty:* Standard analysis.
3.  **Outer Orthogonality:** Prove explicitly that $\langle \nabla U_{outer}, \nabla V_{test} \rangle_{L^2} \approx 0$.
    *   *Strategy:* Use the specific properties of the outer function constructed from the BMO boundary modulus.

---

## Gap D: Quantitative Wedge (Measure Theory)

**Current State:**
`WindowNeutralityHypothesis` assumes the phase integral is small. `LebesgueDifferentiationHypothesis` assumes local-to-global control. Justified by RS Window Neutrality (T6).

**Unconditional Requirement:**
Prove that the specific window function defined by the 8-tick scale satisfies the integral bounds for $\zeta$.

**Classical Proof Obligations:**
1.  **Window Construction:** Construct an explicit `AdmissibleWindow` function $\varphi$ (smooth, compact support) that "dodges" the atoms (zeros) while maintaining the energy bounds.
    *   *Difficulty:* Medium combinatorial geometry.
2.  **Lebesgue Differentiation:** The lemma `local_to_global_wedge` is proved conditionally. The condition (local integrability of phase) needs to be verified for the specific $w(t)$.
    *   *Difficulty:* Low/Medium.

---

## Minor Gaps

1.  **Poisson Representation (`hRepOn`):** Prove `HasPoissonRepOn` for the function $F = 2J$. This requires showing $F$ belongs to an appropriate Hardy class (e.g., $H^1$ or $H^2$).
2.  **Guard Condition (`hRe_one`):** Verify $0 \le \Re(2J(1))$. This is a concrete numerical check.

---

## Summary

To make the proof unconditional:
1.  **Gap B (VK)** is the primary blocker. It requires formalizing a significant portion of modern analytic number theory.
2.  **Gap A (Phase)** and **Gap C (Green)** are substantial analysis tasks but standard in principle.
3.  **Gap D (Wedge)** is mostly a matter of careful construction.

The current Lean repository provides the **structure** and **logic** of the proof, assuming these deep analytic theorems hold.
