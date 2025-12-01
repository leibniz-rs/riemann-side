## Riemann Hypothesis Completion Plan (Dec 1 2025)

This document tracks the remaining steps needed to turn the current Hardy–Schur / boundary‑wedge Lean development into an unconditional proof of the Riemann Hypothesis. Re‑prompt this file as often as needed; it contains all context, current status, milestones, and execution rules. Treat it as the single source of truth for this effort.

---

### 1. Current Status Snapshot

- **Project builds:** `lake build Riemann.RS.BWP.FinalIntegration` succeeds.
- **Quantitative inputs:** `Constants.lean` proves `Υ_paper < 1/2`; VK zero‑density bounds instantiated.
- **Architecture:** RS → VK → Carleson energy → CR–Green pairing → Wedge hypotheses.
- **Blocking gaps:**
  1. `RH_large_T` in `FinalIntegration.lean` still states `∀ s, cond → True`.
  2. `PoissonTransport.lean` and `PPlusFromCarleson.lean` each contain a single `sorry` covering the local‑to‑global wedge implication.
  3. No Lean theorem yet turns `Υ < 1/2` + VK budget into the Mathlib `RiemannHypothesis` statement.
- **De Branges route:** presently relies on `axiom XiGenerator_is_HB_axiom` (equivalent to RH). Leave untouched until BWP route is complete.

---

### 2. Target End State

Produce a Lean theorem of the form:

```lean
theorem rh_from_vk_and_wedge :
  RiemannHypothesis := ...
```

where `RiemannHypothesis` is Mathlib’s official statement (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`).

Intermediate goal: a genuine (nontrivial) predicate `RH_large_T_strong T0` defined inside `Riemann/RS/BWP/FinalIntegration.lean` such that

```lean
theorem hardy_schur_main_result_strong ... :
  RH_large_T_strong (rh_threshold N vk)
```

and then a bridge from `RH_large_T_strong` to `RiemannHypothesis`.

---

### 3. Immediate Action Items (in execution order)

1. **Define the strong predicate**
   - File: `riemann/Riemann/RS/BWP/FinalIntegration.lean`
   - Add
     ```lean
     def RH_large_T_strong (T0 : ℝ) : Prop :=
       ∀ s : ℂ, |s.im| > T0 → riemannXi_ext s = 0 → s.re = 1/2
     ```
   - Keep the old `RH_large_T` temporarily (so existing theorems still compile). New proofs should target `_strong`.

2. **Statement stubs**
   - In `FinalIntegration.lean`, add theorem shells (no `sorry` yet) for:
     ```lean
     theorem rs_implies_rh_large_T_strong ... :
       RH_large_T_strong (rh_threshold N vk)
     theorem hardy_schur_main_result_strong ... :
       RH_large_T_strong (rh_threshold N vk)
     ```
   - Initially implement them by delegating to a placeholder lemma `wedge_closure_implies_zero_free`, which will be supplied later.

3. **Introduce temporary Poisson transport hypothesis (added)**
   - File: `riemann/Riemann/RS/PoissonTransport.lean`
   - Added:
     ```lean
     structure PoissonTransportHypothesis : Prop :=
       (transport :
         ∀ (F : ℂ → ℂ),
           AnalyticOn ℂ F RH.RS.Ω →
           ContinuousOn F (closure RH.RS.Ω) →
           (∀ᵐ t : ℝ, 0 ≤ (F ((1/2 : ℝ) + t * I)).re) →
           ∀ z ∈ RH.RS.Ω, 0 ≤ (F z).re)
     ```
   - Purpose: unblock wiring by treating boundary→interior positivity as a named hypothesis we can assume and later discharge with a full maximum‑principle proof.
   - Follow‑up: optionally keep `poisson_transport_positivity` as the target theorem that will prove `PoissonTransportHypothesis` (currently still a `sorry`).

4. **Fill `PPlusFromCarleson.lean`**
   - Implement `PPlus_from_Carleson_impl`. Steps:
     - Use certificate readiness + `ConcreteHalfPlaneCarleson Kξ` to deduce `EBand.fromUpsilon` energy control.
     - Apply `upsilon_param_lt_half_of_Kxi_lt_max` (from `WedgeHypotheses.lean`) to conclude `Υ(Kξ) < 1/2`.
     - Use the temporary `PoissonTransportHypothesis` (or a specialized boundary‑closure lemma) to complete the wedge→boundary step if needed; later replace with a direct proof and remove the hypothesis.
   - Result: `(CertificateReady ∧ ConcreteHalfPlaneCarleson Kξ) → PPlus F`.

5. **Strong main theorem**
   - After steps 3–4 compile, refactor the main theorem bodies in `FinalIntegration.lean` so they call the new strong predicate and eliminate the trivial `True`.

6. **Bridge to Mathlib `RiemannHypothesis`**
   - In a dedicated section (either `FinalIntegration.lean` or a new file), connect `riemannXi_ext s = 0` to `riemannZeta s = 0`, excluding trivial zeros and the pole at 1. Use existing lemmas relating ξ and ζ (search `CompletedXi`).
   - Conclude `RiemannHypothesis` from the strong Hardy–Schur result and the VK threshold (currently `exp 30`).

7. **(New) Prove PoissonTransportHypothesis (discharge the temporary hypothesis)**
   - File: `riemann/Riemann/RS/PoissonTransport.lean`
   - Goal: provide a theorem filling `PoissonTransportHypothesis.transport`:
     - Input: `F` analytic on Ω, continuous on `closure Ω`, boundary a.e. nonnegativity of `Re F`.
     - Output: `∀ z ∈ Ω, 0 ≤ (Re F z)`.
   - Suggested approaches:
     - Herglotz/Poisson representation on half‑plane, or
     - Harmonic maximum/minimum principle for `u = Re F`, using boundary limits.
   - Acceptance criteria: replace all uses of `PoissonTransportHypothesis` with the proven lemma and delete the temporary structure.

8. **(New) Prove ζ→ξ zero bridge (ZetaXiBridgeHypothesis)**
   - File: `riemann/Riemann/RS/BWP/FinalIntegration.lean` (or a new `ZetaXiBridge.lean`)
   - Prove: if `riemannZeta s = 0` and `s` is not a trivial zero and `s ≠ 1`, then `riemannXi_ext s = 0`.
   - Strategy: unfold the completed xi definition in `CompletedXi`, use the standard identity expressing ξ in terms of Γ and ζ, and isolate the nonvanishing Γ and `(s−1)` factors.

9. **(New) Low-height verification (LowHeightRHCheck)**
   - Provide `LowHeightRHCheck T0`:
     - Option A (computational): import a certified dataset and verification proofs for zeros up to `T0 = exp 30`. This requires a curated data module with a verified checker in Lean.
     - Option B (analytic): strengthen the wedge/energy machinery so the threshold drops to `T0 = 0` (removing the finite-height requirement). This would require new unconditional bounds beyond the current VK inputs.
   - Near‑term recommendation: keep `LowHeightRHCheck` as an explicit input to the final bridge theorem `rh_from_strong_via_bridge_and_lowheight`. Do not assert it as an axiom.

---

### 4. Non-Goals / Deferred Items

- Do **not** modify the De Branges files until the BWP path is complete.
- Do **not** remove the existing `RH_large_T` predicate until all callers migrate.
- Leave knobs (`PoissonJensenPerZeroHypothesis`, `WedgeEnergyBudgetHypothesis`) in place; they are optional generalizations for later numeric tightening.

---

### 5. Execution Guidelines for Future Agents

1. When prompted with this file, **read it fully before acting**.
2. Work on the action items in order unless the user explicitly reprioritizes.
3. After each significant change, run `lake build Riemann.RS.BWP.FinalIntegration`.
4. Every PR or major edit should cite this plan in its description.
5. If you encounter new blockers (additional `sorry`, missing lemmas, etc.), append a dated “Blockers” section to this file with precise file/line references.

---

### 6. Blockers Log (append as needed)

| Date | File | Description | Status |
|------|------|-------------|--------|
| 2025‑12‑01 | (none) | Initial plan captured | Active |
| 2025‑12‑01 | PoissonTransport.lean | Need a full maximum principle proof to discharge `PoissonTransportHypothesis` | Open |
| 2025‑12‑01 | FinalIntegration.lean | Need a proof of `ZetaXiBridgeHypothesis` | Open |
| 2025‑12‑01 | (new) | Need a strategy for `LowHeightRHCheck T0` (data or stronger analysis) | Open |

---

### 7. Quick Reference (file map)

- `riemann/Riemann/RS/BWP/FinalIntegration.lean` — main integration + RH predicates.
- `riemann/Riemann/RS/PPlusFromCarleson.lean` — wedge closure implication (needs proof).
- `riemann/Riemann/RS/PoissonTransport.lean` — maximum principle / transport lemma.
- `riemann/Riemann/RS/CRGreenOuter.lean` — outer function + pairing scaffolding.
- `riemann/Riemann/RS/WedgeHypotheses.lean` — band‑energy abstractions (`BandEnergy`, `WedgeToRHHypothesis`).
- `riemann/Riemann/RS/WhitneyAeCore.lean` — definition of `(P+)` and boundary positivity.
- `riemann/Riemann/AnalyticNumberTheory/VinogradovKorobov.lean` — VK bounds (already complete).

Keep this document updated whenever meaningful progress occurs.
