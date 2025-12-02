## Unconditional RH Execution Strategy (Dec 2, 2025)

Goal: Close the remaining analytic and number-theoretic gaps and finish a fully unconditional Lean proof of the Riemann Hypothesis with zero axioms.


### Current Build Status

- Build: compiles successfully (no errors)
- FinalIntegration.lean sorries: 11
  - 791: upsilon_lt_half_implies_PPlus_canonical (Whitney wedge → P+)
  - 909: canonical_pinch_has_poisson_rep (Poisson integral formula on offXi)
  - 934: special_value_at_one_nonneg (intentionally false; ignored)
  - 1066, 1073, 1079, 1089: theta_cr_pinned_data (4 focused sorries: analyticity on U\{ρ}, Cayley EqOn, Tendsto u→0, witness)
  - 1275, 1316: no_zeros_from_interior_positivity z=1 edge cases (unreachable)
  - 1290: no_zeros_from_interior_positivity analyticity transfer (z ≠ 1)
- Other files:
  - CRGreenOuter.lean: 2 sorries (unreachable z=1 branches)
  - PhaseVelocityHypothesis.lean: 3 sorries
  - VinogradovKorobov.lean: 4 sorries


### Strategy Selection (Best Path)

We execute the minimal path to unconditional closure, prioritized by impact on the main chain:

1) Close theta_cr_pinned_data (4 targeted sorries)
   - Prove analyticity of Θ_CR_offXi on U \ {ρ} using analyticity of J_canonical and Cayley transform (OuterData.hDen assures denom ≠ 0).
   - Prove EqOn Θ_CR_offXi = (1 - u)/(1 + u) with u = 1/(2 J_canonical) by algebra on (F-1)/(F+1).
   - Prove Tendsto u → 0 at ρ via J_canonical = det2 / (outer · ξ_ext), with ξ_ext(ρ)=0 and det2, outer ≠ 0.
   - Produce witness z ∈ U \ {ρ} with Θ ≠ 1 (denominator argument; F+1 ≠ 0).

2) Prove upsilon_lt_half_implies_PPlus_canonical (Whitney wedge → P+)
   - Use: J_CR_boundary_abs_one_ae, Carleson phase-energy control, Whitney dyadic decomposition, Lebesgue differentiation on ℝ.
   - Derive a.e. bound |θ| < π/4, conclude cos(θ) ≥ √2/2 > 0 ⇒ Re J > 0 a.e.

3) Prove canonical_pinch_has_poisson_rep (Poisson representation on offXi)
   - Re(F_pinch) harmonic on Ω; boundary a.e. bound and measurability established; apply half-plane Poisson representation.

4) Fix analyticity transfer for Θ_ext at z ≠ 1 (no_zeros_from_interior_positivity)
   - Use local analyticity and EqOn on a neighborhood avoiding {1}; transfer analyticAt via eventuallyEq.

5) VK sorries in VinogradovKorobov.lean
   - Replace trivialLogDeriv*, trivialLogZeta*, finite_zeros with references from existing PNT/ZetaBounds modules and standard compactness/identity arguments.

6) JensenRectangleHypothesis
   - Implement rectangle Jensen via Green’s theorem (or by conformal map to disk), using Mathlib intervalIntegral and existing Green identities.

7) Wire final schemas and low-height verification
   - Ensure rh_from_master_hypotheses closes using strong pipeline + ζ↔ξ bridge + LowHeightRHCheck (existing finite certificate).

### Parallel Track: Nonclassical focus (axiom‑bridged), aligned with RH_focus_nonclassical_plan.md

Purpose: keep the unconditional mainline above as the primary route, while in parallel pursuing the “single non‑classical ingredient” route that axiomatizes standard classical inputs and focuses effort on a uniform per‑zero band‑energy lower bound at VK scale.

- Files (present): `riemann/Riemann/RS/ClassicalAxioms.lean`, `riemann/Riemann/RS/BWP/PerZeroLowerBound.lean`, `riemann/Riemann/RS/BWP/RHFromAxiomsAndPerZero.lean`.
- Goal: prove `PerZeroEnergyLowerBoundHypothesis` (aka Poisson–Jensen per‑zero band‑energy lower bound) without axioms; use axiom shims only for VK, Whitney→P+, Poisson rep, and removable singularities until later removal.
- Deliverable (alt route): `rh_from_classical_axioms_and_per_zero : PerZeroEnergyLowerBoundHypothesis → RiemannHypothesis`.
- Current status (Dec 2, 2025):
  - PerZeroLowerBound.lean: 3 sorries (core research target)
  - RHFromAxiomsAndPerZero.lean: 0 sorries (bridge wired)
  - ClassicalAxioms.lean: 0 sorries (contains axioms to be discharged later)
- Acceptance (parallel track):
  - Interim: RH under classical axioms + proven per‑zero bound (for exploration).
  - Final: remove axioms by completing VK, Whitney→P+, Poisson rep, Jensen rectangle, and analyticity transfer proofs; then both routes yield unconditional RH.


### Detailed Milestones and Acceptance Criteria

- M1: Close theta_cr_pinned_data (FinalIntegration.lean lines ~1066–1089)
  - Deliverables:
    - AnalyticOn ℂ (Θ_CR_offXi hIntPos) (U \ {ρ})
    - EqOn Θ_CR_offXi (fun z => (1 - u z) / (1 + u z)) (U \ {ρ})
    - Tendsto u (nhdsWithin ρ (U \ {ρ})) (𝓝 0)
    - ∃ z ∈ U, Θ_CR_offXi z ≠ 1
  - Acceptance: 0 sorries under theta_cr_pinned_data.
  - Tests: grep -n "theta_cr_pinned_data" FinalIntegration.lean; should show no sorry.

- M2: Prove upsilon_lt_half_implies_PPlus_canonical (FinalIntegration.lean ~791)
  - Deliverables: Full formal proof using Carleson energy → phase control → Whitney/LDT → PPlus.
  - Acceptance: theorem closed; PPlus wires through to interior positivity.

- M3: Prove canonical_pinch_has_poisson_rep (FinalIntegration.lean ~909)
  - Deliverables: HasPoissonRepOn witness for F_pinch on offXi; aligns with boundary aliases.
  - Acceptance: theorem closed; used by interior_positive_J_canonical_from_PPlus_offXi.

- M4: Analyticity transfer for Θ_ext at z ≠ 1 (FinalIntegration.lean ~1290)
  - Deliverables: analyticAt transfer via local EqOn on an open neighborhood disjoint from {1}.
  - Acceptance: sorry removed; no extraneous assumptions added.

- M5: VK sorries (VinogradovKorobov.lean)
  - Deliverables: real bounds for log-deriv and log|ζ|, finite zeros on slabs, coherent constants.
  - Acceptance: 0 sorries in VinogradovKorobov.lean.

- M6: JensenRectangleHypothesis
  - Deliverables: rectangle Jensen inequality lemma with explicit constants; integrated into chain.
  - Acceptance: feeds VK/Carleson closure as intended; no remaining placeholder Jensen sorries.

- M7: Final schemas and low-height wiring
  - Deliverables: master_to_rh_large_T_strong remains closed; rh_from_master_hypotheses closes with LowHeightRHCheck instance; final top-level RH theorem.
  - Acceptance: grep -n "sorry" across repo returns none (excluding intentionally false doc-lemma if still present but unused).


### Implementation Notes and References

- Θ/Cayley: Θ_of O = (F-1)/(F+1), with F = 2·J_canonical; EqOn proof is algebraic where denom ≠ 0.
- Removable singularities: use analyticOn_update_from_pinned; for local extension at zeros of ξ_ext.
- offXi domain avoids z=1; Θ_CR_ext only needed to state Schur bound on Ω \ Z(ζ); z=1 branches remain unreachable in the global proof flow.
- Half-plane Poisson: leverage Mathlib’s harmonic/Poisson framework; boundary a.e. and boundedness already available.
- VK bounds/Jensen: reuse and adapt existing PNT/Zeta lemmas; reduce bespoke analysis by gluing standard results to the regions used here.


### Execution Rules

- No axioms; no conditional proofs; all results must be unconditional.
- Keep build green; after each edit, fix lints if trivial and re-run grep for sorries.
- Update RH_remaining_work.md after each milestone with current sorry counts and changes.
- Prefer small, composable lemmas; avoid deep monolithic proofs.
- Use offXi everywhere positivity/Schur are needed; never rely on z=1.


### Verification Commands

- Build target file: `lake build Riemann.RS.BWP.FinalIntegration`
- Count sorries: `grep -n "sorry$" riemann/Riemann/RS/BWP/FinalIntegration.lean`
- Repo-wide sorries: `grep -RIn "sorry$" riemann | wc -l`


### Risks and Mitigations

- R1: Wedge → PPlus complexity (Whitney + LDT + Carleson)
  - Mitigation: split into 3–4 lemmas; reuse existing Mathlib building blocks; add intermediate tactics.
- R2: Poisson rep measurability/alias mismatches
  - Mitigation: establish canonical alias lemmas centrally; small wrappers for boundary equalities.
- R3: VK region constants alignment
  - Mitigation: isolate constants and region definitions; provide translation lemmas; use existing PNT bounds.
- R4: Jensen rectangle edge cases (corners, orientation)
  - Mitigation: follow a fixed reference proof; encode rectangle orientation once and reuse.


### Timeline (best-effort)

- Week 1–2: M1 + M2
- Week 3: M3 + M4
- Week 4–5: M5
- Week 6: M6 + M7


### Done Definition (DoD)

- All sorries removed (except intentionally false doc-lemma, unused by the proof).
- Top-level RH theorem in FinalIntegration.lean proved unconditionally.
- CI: build passes; repo-wide sorries count is zero (excluding explicit doc placeholder if still present and unused).
