# Must‑Prove Elements Plan (Riemann Hypothesis)

Last updated: Dec 3, 2025

Goal: Identify every element that cannot remain an axiom (or placeholder) without risking correctness, and prescribe the proofs/certifications needed to make the RH deduction unconditional. Classical, widely accepted theorems may remain axioms temporarily unless they hide a weakness in this particular proof chain.

## Criteria

- Must‑prove (cannot be axioms):
  - Anything equivalent to RH itself
  - Any numerical/quantitative bound specific to this proof (not a standard theorem)
  - Any bridge where constants, domain subtleties, or measurability could invalidate Υ < 1/2 or the wedge→Schur→globalization chain
  - Low‑height verification: must be provided by verifiable certificate or eliminated analytically
- May remain axioms (for now):
  - Standard classical theorems (Lebesgue differentiation, Green identity, removable singularities, Poisson kernel basics), unless their use here requires non‑standard hypotheses or quantitative constants that are not spelled out

---

## A. Immediate must‑prove (blocking/critical)

1) Remove RH‑equivalent axiom (de Branges track)
- What: `XiGenerator_is_HB_axiom` in `riemann/Riemann/RS/DeBranges/DBEmbedding.lean`
- Why: Equivalent to RH; cannot be assumed in any path
- Plan: Ensure the de Branges route is not imported by the main proof; gate as experimental only. If pursued as a second route, this axiom must be removed and replaced with an actual proof (which is RH itself) – so keep out of any unconditional claim.
- Acceptance: Main final theorem does not import or depend on this file. A repository‑wide `grep -R "XiGenerator_is_HB_axiom"` shows zero references in the proof path.

2) Fix placeholder statement for RH at large height
- What: `RH_large_T` currently defined with `→ True` placeholder in `Riemann/RS/BWP/FinalIntegration.lean`
- Why: Not an axiom, but a correctness hazard; must be replaced with the actual predicate `ξ(s)=0 → Re(s)=1/2`
- Plan: Replace the placeholder with the strong predicate already used elsewhere (`RH_large_T_strong`). Remove any trivial proofs relying on `True`.
- Acceptance: No definitions/theorems with `→ True` remain on the path to the final theorem.

3) Eliminate intentionally false lemma (z = 1 special value)
- What: `special_value_at_one_nonneg` in `FinalIntegration.lean` (intentionally false `sorry`)
- Why: Must not be part of any chain; avoid confusion
- Plan: Move it to documentation or delete. Ensure all proofs use the offXi variant that excludes z=1.
- Acceptance: The lemma is removed (or isolated in docs) and not referenced anywhere.

4) Low‑height verification cannot be an axiom
- What: `low_height_rh_check_axiom` in `Riemann/RS/ClassicalAxioms.lean`
- Why: This is not a classical theorem; it is a finite computational certification. It must be provided by verifiable data or removed by analysis.
- Options:
  - (Preferred) Provide a Lean‑verifiable certificate (Platt/Odlyzko style) up to the threshold actually used (`vk.T0`, currently ≲ exp(30)).
  - (Alternative) Strengthen the analytic route to remove the threshold (very hard; not expected).
- Acceptance: Replace axiom with a theorem `LowHeightRHCheck T0` justified by a certificate file and checked in Lean; or remove the dependency entirely.

5) Quantitative phase bound cannot be axiomatized in aggregate
- What: `phase_bound_from_energy_axiom` in `FinalIntegration.lean`
- Why: This collapses multiple quantitative steps (Carleson energy, CR–Green pairing, Poisson plateau, Lebesgue differentiation) and ties directly to the numerical wedge threshold Υ < 1/2. Leaving it as a single axiom can hide mistakes in constants or hypotheses.
- Plan: Prove the chain with explicit constants:
  - 5.1 Carleson energy: `E(I) ≤ (K₀ + Kξ) · |I|` (produce concrete `K₀, Kξ`)
  - 5.2 Green/Cauchy–Schwarz: `|∫_I φ(−θ')| ≤ M_ψ · √E(I)`
  - 5.3 Plateau lower bound: `c₀ · μ(Q(I)) ≤ ∫_I φ(−θ')`
  - 5.4 Combine to phase average bound, then apply Lebesgue differentiation a.e.
  - 5.5 Conclude `PPlus_canonical` when Υ < 1/2.
- Deliverables:
  - Replace `phase_bound_from_energy_axiom` by theorems in `BWP` namespace; have `upsilon_lt_half_implies_PPlus_canonical` become lemma using those theorems.
- Acceptance: `upsilon_lt_half_implies_PPlus_canonical` proved without axioms; all constant inputs audited end‑to‑end.

---

## B. Core classical bridges (may stay axioms temporarily; prove to harden)

6) Poisson representation for the pinch field (offXi)
- What: `poisson_rep_on_offXi_axiom` (also mirrored in `ClassicalAxioms`)
- Why: Classical (analyticity + boundary modulus + Poisson formula) but domain subtleties (offXi excludes zeros and z=1) and integrability need checking. Safe to keep temporarily, but should be proved to remove doubt.
- Plan to prove:
  - Show analyticity of `F_pinch` on offXi
  - Boundary modulus equality holds (outer × det2 vs completed Xi)
  - Boundary integrability and Fatou trace on the boundary line
  - Apply the half‑plane Poisson representation on the admissible domain
- Acceptance: Replace axiom by theorem `canonical_pinch_has_poisson_rep`.

7) Removable singularity & Cayley pinned data for Θ_CR
- What: `theta_cr_pinned_data_axiom` (also mirrored in `ClassicalAxioms`)
- Why: Classical removable singularity + Cayley transform with local limit; likely safe as an axiom now. Still central to Schur globalization, so we should prove it to avoid edge‑case risk.
- Plan to prove:
  - `J_canonical` meromorphic; simple pole at each ξ‑zero
  - Define `u = 1/(2J)`; show `u → 0` at each ξ‑zero; Θ = (1−u)/(1+u)
  - Provide `U` excluding z=1 and isolating the zero; prove `AnalyticOn` and `EqOn` claims
- Acceptance: Provide theorem `theta_cr_pinned_data` used by `localAssignmentHypothesis_from_intPos`.

---

## C. Numeric constants that must be justified (cannot be "assumed")

8) K₀ bound (Euler/outer tail)
- Where: `riemann/Riemann/academic_framework/EulerProduct/K0Bound.lean` (contains `sorry`s)
- Why: This feeds the energy/Υ budget. It is a bespoke numeric estimate; cannot be left as an axiom.
- Plan: Replace `sorry` blocks with interval‑arithmetic proofs or certified inequalities. Produce a Lean‑checked bound (e.g., `K₀ ≤ 1/8`).
- Acceptance: `lake build` with file proven; budget contributes to `Upsilon_paper` without axioms.

9) Kξ (Whitney/RvM) Carleson constant
- Where: `riemann/Riemann/Cert/KxiWhitney_RvM.lean` (currently ends with `sorry`/trivial constant)
- Why: This is the other half of the energy budget; cannot be assumed.
- Plan: Finish Poisson energy lemmas, instantiate VK annular counts, derive an explicit `Kξ` (≤ Kxi_paper). Integrate with VK hypotheses actually used in `FinalIntegration`.
- Acceptance: The certificate produces a numeric `Kξ` and discharges all `sorry`s; `energy_paper` and `Upsilon_paper` become theorem‑backed.

10) VK package compatibility with budget
- Where: `Riemann/AnalyticNumberTheory/VinogradovKorobov.lean` and `RS/BWP/ZeroDensity*.lean`
- Why: Though VK bounds may be treated as classical, the specific constants used with K₀/Kξ must be compatible to keep Υ < 1/2.
- Plan: Either: (a) formalize VK with explicit constants used by the budget, or (b) add a thin verification lemma that the imported VK constants imply the budget inequalities required by the wedge step.
- Acceptance: A Lean lemma `VK_B_budget_ok : Upsilon_paper < 1/2` derived from K₀, Kξ, and VK constants, no axioms.

---

## D. Cleanups to avoid hidden reliance

11) Remove/disable unused axioms
- What: `wedge_closure_axiom` in `BWP/EnergyToPPlus.lean` (not on main path)
- Why: Avoid accidental import/use; this duplicates part of (5)
- Plan: Guard behind `#if/#endif` dev section or delete and replace with TODO comment/reference to (5).

12) z = 1 “unreachable” sorries
- Where: `CRGreenOuter.lean`
- Why: Documented as unreachable; keep off the main imports or refactor to the `offXi` formulation to remove these branches entirely.
- Plan: Either prove trivial impossibility lemmas or excise these branches by construction.

---

## E. Execution order (minimal path to hardening the main chain)

1. Axiom cleanup and placeholders
   - Remove RH_large_T placeholder True
   - Remove/relocate `special_value_at_one_nonneg`
   - Ensure de Branges axiom not in main path

2. Phase bound chain (5) – prove end‑to‑end with constants → `PPlus_canonical`

3. Poisson representation (6) – prove on offXi

4. Θ pinned data (7) – prove removable singularity and Cayley structure

5. Numeric constants (8–10)
   - Prove `K₀` file
   - Finish `Kξ` certificate
   - Verify VK compatibility → `Upsilon_paper < 1/2`

6. Low‑height check (4)
   - Add certified dataset or analytic replacement

After 1–6, the `WedgeToRHBridgeHypothesis` and `master_to_rh_large_T_strong` should be fully theorem‑backed; combine with `LowHeightRHCheck` certificate to conclude Mathlib’s `RiemannHypothesis` without axioms.

---

## F. Deliverables and acceptance tests

- No use of: `XiGenerator_is_HB_axiom`, `phase_bound_from_energy_axiom`, `poisson_rep_on_offXi_axiom`, `theta_cr_pinned_data_axiom`, `low_height_rh_check_axiom` in the final proof path
- `upsilon_lt_half_implies_PPlus_canonical` is a theorem with no axioms
- `canonical_pinch_has_poisson_rep` is a theorem with no axioms
- `theta_cr_pinned_data` is a theorem with no axioms
- `K0Bound.lean` and `KxiWhitney_RvM.lean` contain no `sorry`
- A certificate file (or analytic result) provides `LowHeightRHCheck T0`
- Sanity script (informal):
  - `grep -RIn "^axiom" riemann | wc -l` drops to 0 (or only in isolated dev files not imported)
  - `grep -RIn "sorry$" riemann | grep -v isolated_dirs` shows none in the proof path
  - `lake build Riemann.RS.BWP.FinalIntegration` succeeds

---

## G. Notes on acceptable axioms (for now)
- Lebesgue differentiation, Green identity, Poisson plateau, standard removable singularity statements may remain axioms temporarily if used only qualitatively and without custom constants. As soon as they are used quantitatively (e.g., to establish the phase bound with a numerical Υ), they must be unpacked and proved with explicit constants or accompanied by checked certificates.
