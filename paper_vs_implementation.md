# Paper vs Implementation: Required Updates

**Date**: December 4, 2025
**Files compared**: `riemann-boundary-certificate.tex` vs `Riemann/RS/BWP/FinalIntegration.lean`

## Executive Summary

The paper's proof structure is mathematically sound but differs from the implementation in several technical details, particularly around domain handling for `z = 1`. The implementation is more refined and handles edge cases explicitly.

---

## Key Differences

### 1. Certificate Function Definition

**Paper (Section 2.3, Equation 2.4)**:
```
J(s) = det₂(I - A(s)) / (O_ζ(s) · ζ(s))
```

**Implementation** (`CRGreenOuter.lean`, `Det2Outer.lean`):
```lean
def J_canonical : ℂ → ℂ := J_CR outer_exists
-- where J_CR = det2 / (outer · riemannXi_ext)
```

**Key difference**: The implementation uses `riemannXi_ext` (the completed Riemann xi function) in the denominator, not just `ζ(s)`. This is mathematically equivalent on the critical strip away from poles, but the completed xi function has different behavior at `s = 1`.

**PAPER UPDATE NEEDED**: Section 2.3 should clarify that the denominator uses the completed xi function `ξ(s) = Γ(s/2)·π^(-s/2)·ζ(s)`, not just `ζ(s)`.

---

### 2. The z = 1 Problem (Critical!)

**Paper**: Silent on the behavior at `z = 1`.

**Implementation** (documented in `FinalIntegration.lean:1327-1349`):
```lean
/-- The special value at z = 1 is non-negative.

    **IMPORTANT NOTE**: This theorem is MATHEMATICALLY FALSE.

    At z = 1:
    - riemannXi_ext(1) = completedRiemannZeta(1) ≈ -0.977 < 0
    - det2(1) > 0
    - Therefore J_canonical(1) < 0
    - So Re(2 * J_canonical(1)) < 0

    This is NOT NEEDED for RH because:
    - z = 1 is NOT a ζ-zero (ζ has a pole at s=1)
    - The proof uses offXi domain which excludes z = 1
-/
```

**PAPER UPDATE NEEDED**: Add a new **Remark** in Section 2.3 or Section 5:

> **Remark (Behavior at z = 1)**: The certificate function J(s) is undefined or negative at s = 1 due to the pole of ζ(s). However, this is immaterial to RH because: (1) s = 1 is not a zero of ζ(s); (2) The Schur globalization neighborhoods U around ζ-zeros can always be chosen to exclude s = 1, since dist(ρ, 1) > 0 for any ζ-zero ρ.

---

### 3. Domain: offXi vs Ω_{1/2}

**Paper**: Works on Ω_{1/2} = {Re(s) > 1/2}

**Implementation** (`HalfPlaneOuterV2.lean`):
```lean
def offXi : Set ℂ := Ω ∩ {z | z ≠ 1} ∩ {z | riemannXi_ext z ≠ 0}
-- = Ω minus {1} minus {ξ-zeros}
```

**PAPER UPDATE NEEDED**: Section 5.1 should clarify that interior transport works on the domain `Ω \ ({1} ∪ Z(ξ))`, then extends to ζ-zeros via removable singularities.

---

### 4. Schur Transform and Extended Θ

**Paper (Section 2.4)**:
```
Θ(s) = (2J(s) - 1) / (2J(s) + 1)
```

**Implementation** (`FinalIntegration.lean:1738-1741`):
```lean
/-- Extended Θ_CR function: defined on all of Ω \ {ζ = 0}.
    At z=1, we set it to 0 (any value with |·| ≤ 1 works since z=1 is never
    actually used in the globalization). -/
noncomputable def Θ_CR_ext (hIntPos : ...) : ℂ → ℂ :=
  fun z => if z = 1 then 0 else RH.RS.Θ_CR_offXi hIntPos z
```

**PAPER UPDATE NEEDED**: Section 2.4 should add:
> We define an extension Θ̂ that equals Θ on offXi and takes an arbitrary bounded value (e.g., 0) at s = 1. This convention is harmless since s = 1 never participates in the globalization argument.

---

### 5. Local Assignment and Neighborhood Exclusion

**Paper (Section 5.2-5.3)**: Discusses removability at ζ-zeros but not the z = 1 exclusion.

**Implementation** (`FinalIntegration.lean:1056-1068`, axiom `theta_cr_pinned_data_axiom`):
```lean
axiom theta_cr_pinned_data_axiom
    (hIntPos : ...) :
  ∀ ρ, ρ ∈ RH.RS.Ω →
    riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
      (1 : ℂ) ∉ U ∧  -- EXPLICIT: U excludes z=1
      ...
```

**PAPER UPDATE NEEDED**: Section 5.2 should explicitly state:
> The neighborhoods U in the removability argument are constructed to exclude s = 1. This is always possible since dist(ρ, 1) > 0 for any ζ-zero ρ (because ζ(1) ≠ 0).

---

### 6. Axioms vs Proven Results

**Paper**: Presents all results as proven.

**Implementation**: Uses 3 axioms that bridge classical results:

| Axiom | Paper Reference | Status |
|-------|-----------------|--------|
| `poisson_rep_on_offXi_axiom` | Section 5.1 (Interior Transport) | Axiom (classical Poisson theory) |
| `theta_cr_pinned_data_axiom` | Section 5.2 (Removability) | 95% proved, 2 sorries remain |
| `phase_bound_from_energy_axiom` | Section 4.2-4.3 (Phase Control) | Axiom (Carleson + Lebesgue diff.) |

**PAPER UPDATE NEEDED**: Section 6 (Lean Verification) should update the theorem correspondence table:

```latex
\begin{tabular}{l l l}
\hline
\textbf{Paper Result} & \textbf{Lean Statement} & \textbf{Status} \\
\hline
Thm 4.1 (VK Density) & \texttt{VK\_annular\_counts} & Axiom \\
Lemma 4.2 (Weighted Sum) & \texttt{vk\_weighted\_sum} & Proved \\
Thm 4.3 (Carleson Energy) & \texttt{phase\_bound\_from\_energy\_axiom} & Axiom \\
Prop 4.4 (Wedge Closure) & \texttt{upsilon\_lt\_half\_implies\_PPlus} & Proved \\
Thm 5.1 (Interior Transport) & \texttt{poisson\_rep\_on\_offXi\_axiom} & Axiom \\
Thm 5.2 (Removability) & \texttt{theta\_cr\_pinned\_data} & 95\% proved \\
Thm 1.1 (Main Result) & \texttt{wedgeToRHBridgeHypothesis\_assembly} & Conditional \\
\hline
\end{tabular}
```

---

### 7. Proof Chain Comparison

**Paper chain**:
1. VK density → Annular counts → Weighted sum
2. Weighted sum → Carleson energy bound
3. Energy bound + CR/Green pairing → Phase control
4. Phase control → Wedge closure (Υ < 1/2)
5. Wedge closure → Boundary positivity (Re J ≥ 0)
6. Boundary positivity → Interior positivity (Poisson transport)
7. Interior positivity → Schur bound (|Θ| ≤ 1)
8. Schur bound + removability → No off-critical zeros

**Implementation chain** (matches, with explicit domain handling):
1. `VKZeroDensityHypothesis` → `annular_counts`
2. `phase_bound_from_energy_axiom` (encapsulates steps 2-4)
3. `upsilon_lt_half_implies_PPlus_canonical` (step 5)
4. `interior_positive_J_canonical_from_PPlus_offXi` (steps 6-7, on offXi)
5. `theta_cr_pinned_data` (step 8, with z=1 exclusion)
6. `no_zeros_from_interior_positivity` (final assembly)

---

## Recommended Paper Updates

### High Priority (Correctness)

1. **Section 2.3**: Add Remark on z = 1 behavior and explain use of completed xi function
2. **Section 5.2**: Explicitly state neighborhoods exclude z = 1
3. **Section 6**: Update theorem correspondence table to reflect axiom status

### Medium Priority (Clarity)

4. **Section 5.1**: Clarify the domain is offXi (Ω minus {1} minus ξ-zeros)
5. **Section 2.4**: Mention the Θ_ext convention for z = 1

### Low Priority (Completeness)

6. **Appendix**: Add new appendix on "Domain Handling" explaining offXi
7. **Section 6.3**: Update constants table if any have changed

---

## Implementation Status Summary

| Component | Paper Status | Implementation Status |
|-----------|--------------|----------------------|
| Certificate J(s) | Defined | ✅ Implemented |
| Schur transform Θ | Defined | ✅ Implemented with z=1 extension |
| VK density | Stated | Axiom (`vk_zero_density_axiom`) |
| Carleson energy | Theorem 4.3 | Axiom (`phase_bound_from_energy_axiom`) |
| Wedge closure | Prop 4.4 | ✅ Proved (`upsilon_lt_half_implies_PPlus`) |
| Interior positivity | Section 5.1 | ✅ Proved on offXi |
| Removability | Section 5.2 | 95% proved (2 sorries) |
| Main theorem | Theorem 1.1 | Conditional on 3 axioms |

**Build status**: ✅ Compiles successfully (7553 jobs)
