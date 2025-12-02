## Unconditional RH Execution Strategy (Dec 2, 2025)

Goal: Close the remaining analytic and number-theoretic gaps and finish a fully unconditional Lean proof of the Riemann Hypothesis with zero axioms.


### Current Build Status (Updated Dec 2, 2025)

- Build: compiles successfully (no errors)
- **PARALLEL TRACK IMPLEMENTED**: Key theorems now use axiom-bridged versions

#### FinalIntegration.lean Status:
- **Axioms** (4 total):
  - `poisson_rep_on_offXi_axiom` (line 878): Poisson representation for pinch field
  - `theta_cr_pinned_data_axiom` (line 894): Local Cayley data for removable extension
  - `phase_bound_from_energy_axiom` (line 919): Energy → phase bound (classical harmonic analysis)
  - `z1_edge_case_unreachable` (line 1233): z=1 edge cases are unreachable (trivial)

- **Sorries remaining** (8 total):
  - Line 822: Measure-zero case for ξ-zeros (in `whitney_wedge_to_PPlus_theorem`)
  - Line 868: Classical harmonic analysis (in `whitney_wedge_to_PPlus_theorem`)
  - Line 970: Measure-zero case for ξ-zeros (in `upsilon_lt_half_implies_PPlus_canonical`)
  - Line 998: Technical namespace mismatch (in `upsilon_lt_half_implies_PPlus_canonical`)
  - Line 1094: `special_value_at_one_nonneg` (INTENTIONALLY FALSE; not used in proof)
  - Lines 1339, 1354, 1380: z=1 unreachable cases in `no_zeros_from_interior_positivity`

- **Key theorems**:
  - `upsilon_lt_half_implies_PPlus_canonical` → uses `phase_bound_from_energy_axiom` + trigonometric closure
  - `whitney_wedge_to_PPlus_theorem` → detailed proof outline with sorries
  - `canonical_pinch_has_poisson_rep` → uses `poisson_rep_on_offXi_axiom`
  - `theta_cr_pinned_data` → uses `theta_cr_pinned_data_axiom`

#### Other files:
- CRGreenOuter.lean: 2 sorries (unreachable z=1 branches)
- PhaseVelocityHypothesis.lean: 4 sorries
- VinogradovKorobov.lean: 7 sorries
- PerZeroLowerBound.lean: 2 sorries (core research target)
- RHFromAxiomsAndPerZero.lean: 0 sorries (uses axioms)


### Two Parallel Routes to Unconditional RH

#### Route A: Unconditional Mainline (remove axioms)
Replace each axiom with a real proof:
1. Prove `upsilon_lt_half_implies_PPlus_canonical` (the "hardest nonstandard element")
2. Prove `canonical_pinch_has_poisson_rep`
3. Prove `theta_cr_pinned_data`
4. Close z=1 edge case sorries (unreachable by construction)

#### Route B: Per-Zero Lower Bound (parallel track)
Focus on the single non-classical ingredient:
1. Prove `per_zero_lower_bound_exists` in PerZeroLowerBound.lean
2. This gives `riemann_hypothesis_via_per_zero` immediately
3. Then backfill classical axioms (VK, etc.)


### The Hardest Nonstandard Element: Υ < 1/2 → PPlus

**File**: `riemann/Riemann/RS/BWP/EnergyToPPlus.lean` (newly created)

The proof chain:
1. **Green + Cauchy-Schwarz**: |∫_I φ(-θ')| ≤ M_ψ · √E(I)
2. **Poisson Plateau**: c₀ · μ(Q(I)) ≤ ∫_I φ(-θ')
3. **Carleson Energy**: E(I) ≤ C_box · |I|
4. **Harmonic Analysis (KEY)**: μ(Q(I))/|I| controls |⨍_I θ|
5. **Combining**: |⨍_I θ| ≤ (π/2) · Υ
6. **Lebesgue Differentiation**: |θ(t)| ≤ (π/2) · Υ a.e.
7. **Since Υ < 1/2**: |θ(t)| < π/4 a.e.
8. **Trigonometry**: cos(θ) > 0
9. **Since |J| = 1 a.e.**: Re(J) = cos(θ) > 0 a.e.

**Status**: Axiom-bridged via `whitney_wedge_to_PPlus_axiom`. Full proof requires:
- Phase-average-from-balayage lemma (the missing harmonic analysis step)
- Correct wiring of `energy_implies_wedge`


### Immediate Next Steps

1. **For Route A** (unconditional):
   - Implement the phase-average-from-balayage lemma
   - Wire it through `EnergyToPPlus.lean`
   - Replace `whitney_wedge_to_PPlus_axiom` with the real proof

2. **For Route B** (per-zero bound):
   - Prove `blaschke_phase_deriv_L2_lower_bound`
   - Replace placeholder in `per_zero_lower_bound_exists.lower_bound`
   - Close functional-equation branch


### Verification Commands

```bash
# Build the main file
cd riemann && lake build Riemann.RS.BWP.FinalIntegration

# Count axioms in FinalIntegration
grep -c "^axiom" riemann/Riemann/RS/BWP/FinalIntegration.lean

# Count sorries in FinalIntegration
grep -c "sorry$" riemann/Riemann/RS/BWP/FinalIntegration.lean

# Repo-wide sorry count
grep -RIn "sorry$" riemann/Riemann | wc -l
```


### Milestones (Updated)

- **M0 (DONE)**: Implement parallel track with axiom bridges
  - Created `EnergyToPPlus.lean` with proof outline
  - Added axioms to `FinalIntegration.lean`
  - Build passes

- **M0.5 (DONE)**: Convert `whitney_wedge_to_PPlus_axiom` to theorem
  - Axiom removed, replaced with theorem + sorry
  - Detailed proof outline in place
  - Key sorry: classical harmonic analysis (energy → phase → Re(J) > 0)

- **M1**: Close the key sorry in `upsilon_lt_half_implies_PPlus_canonical`
  - Prove phase-average-from-balayage lemma
  - Implement Lebesgue differentiation application
  - Complete trigonometric closure

- **M2**: Remove `poisson_rep_on_offXi_axiom`
  - Verify Poisson integral formula for canonical pinch field

- **M3**: Remove `theta_cr_pinned_data_axiom`
  - Prove analyticity of Θ_CR on U \ {ρ}
  - Prove Cayley relation and limit

- **M4**: Close z=1 edge cases
  - These are unreachable by construction; formalize the geometric argument

- **M5**: VK and classical ANT
  - Complete VinogradovKorobov.lean
  - Jensen rectangle
  - Log-derivative bounds

- **M6**: Final assembly
  - Verify `riemann_hypothesis_unconditional` compiles with zero axioms


### Done Definition (DoD)

- All axioms removed from FinalIntegration.lean
- All sorries removed (except intentionally false `special_value_at_one_nonneg`)
- Top-level RH theorem proved unconditionally
- Build passes with zero errors
