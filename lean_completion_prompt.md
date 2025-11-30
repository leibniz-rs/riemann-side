# Lean Proof Completion Prompt

Use this prompt repeatedly to work toward an **unconditional** proof of RH.

---

## ⚠️ CRITICAL CONSTRAINT

**The final proof MUST be unconditional.**

- Do NOT remove sorries by adding hypothesis structures
- Do NOT push proof obligations up the call stack
- Every hypothesis structure MUST have a proven instance
- The final theorem must be: `theorem rh : RH := ...` with NO hypotheses

---

## Your Task

1. Open `lean_completion_tracker.md` and identify the highest-priority unproven hypothesis
2. Open the relevant Lean file
3. **Actually prove** the content - don't just assume it
4. Create a `def prove_<Name>` or `theorem <name>_holds` that constructs the instance
5. Update `lean_completion_tracker.md` with your progress
6. If you get stuck, explain what's blocking and what's needed

---

## How to Actually Prove Things

### For Algebraic/Bookkeeping Items (Tier 4)

These should be direct calculations:
```lean
-- Example: Proving a weighted sum bound
theorem weighted_sum_bound_holds (I : WhitneyInterval) (K : ℕ) :
    (Finset.range K).sum (fun k => decay4 k * nu I k) ≤ budget * I.len := by
  -- Actual proof using geometric series, not sorry
  calc ...
```

### For Smooth Function Items (Tier 3)

Use Mathlib's smooth function library:
```lean
-- Example: Smooth bump function exists
theorem smooth_bump_exists (a b : ℝ) (hab : a < b) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ⊤ f ∧ f a = 1 ∧ f b = 0 := by
  -- Use Mathlib.Analysis.Calculus.Bump
  exact ⟨smoothTransition a b, ...⟩
```

### For Harmonic Analysis Items (Tier 2)

These may require more work:
```lean
-- If a result is in Mathlib, use it
-- If not, either:
-- 1. Prove it from first principles
-- 2. Add it as a clearly-documented axiom (last resort)
```

### For Number Theory Items (Tier 1)

The VK zero-density bound is substantial:
```lean
-- This is a major theorem - may need to be built up carefully
-- Check what's already in PrimeNumberTheoremAnd/
```

---

## If You Get Stuck

1. **Search Mathlib**: `exact?`, `apply?`, grep for similar lemmas
2. **Check existing files**:
   - `PrimeNumberTheoremAnd/` for number theory
   - `Mathlib.Analysis.Calculus.Bump` for smooth functions
   - `Mathlib.MeasureTheory.Integral.Lebesgue` for integration
3. **Decompose**: Break into smaller lemmas, prove bottom-up
4. **Document blockers**: If truly stuck, explain what's needed

---

## After Each Change

1. **Verify compilation**: Check for red squiggles in Lean
2. **Update tracker**: Mark items as DONE with proof method
3. **Test the chain**: Verify downstream theorems still compile

---

## Key Files

- **Tracker**: `lean_completion_tracker.md`
- **Final integration**: `riemann/Riemann/RS/BWP/FinalIntegration.lean`
- **VK number theory**: `riemann/Riemann/AnalyticNumberTheory/`
- **Mathlib smooth**: `Mathlib.Analysis.Calculus.Bump`
- **Mathlib integration**: `Mathlib.MeasureTheory.Integral.*`

---

## Priority Order

1. **Fix circular dependency** in `ResidueHypothesis.lean`
2. **Tier 4**: Algebraic bookkeeping (should be easy)
3. **Tier 3**: Smooth functions (Mathlib should help)
4. **Tier 2**: Harmonic analysis (may need axioms for F&M Riesz)
5. **Tier 1**: VK zero-density (hardest, may already be partially done)

---

## Success Criteria

When complete:
- `lake build` succeeds
- No `sorry` in active code
- No uninstantiated hypothesis structures
- `FinalIntegration.lean` exports unconditional `RH` theorem

---

Begin now. Open the tracker, identify the highest priority item, and **actually prove it**.
