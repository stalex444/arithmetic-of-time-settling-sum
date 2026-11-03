module
public import Mathlib

@[expose] public section
/-!
# The settling sum of the plastic number: `∑_{n ≥ 1} ‖ρⁿ‖² = ρ`

Write `‖x‖ = |x − round x|` for the distance from a real number to the nearest integer. For a
Pisot number `θ` the series `∑_{n ≥ 1} ‖θⁿ‖²` converges — Pisot (1938): for real `θ > 1`,
`∑ ‖λθⁿ‖² < ∞` for some real `λ ≠ 0` iff `θ` is a Pisot number — but its value is not in general
known in closed form. This entry evaluates it for the plastic number `ρ`, the real root of
`x³ = x + 1` and the smallest Pisot number (Siegel 1944): **the sum is `ρ` itself**. The entry
compares exactly these seven statements.

Vocabulary. `distInt x = |x − round x|` is `‖x‖`. `powerSum a b c n` is the `n`-th Newton power
sum `Sₙ = θⁿ + αⁿ + ᾱⁿ` of the three roots of `x³ − a x² + b x − c`, an integer defined by the
recurrence `S₀ = 3, S₁ = a, S₂ = a² − 2b, Sₙ₊₃ = a Sₙ₊₂ − b Sₙ₊₁ + c Sₙ`. `perrin n` is the Perrin
sequence `3, 0, 2, 3, 2, 5, 5, 7, 10, 12, …` (the case `a = 0, b = −1, c = 1`: `P(n) = ρⁿ + zⁿ + z̄ⁿ`
for the complex roots `z, z̄` of `x³ − x − 1`). `geo α = α²/(1 − α²) + ᾱ²/(1 − ᾱ²) + 2αᾱ/(1 − αᾱ)`,
the sum of `αᵢαⱼ/(1 − αᵢαⱼ)` over the two conjugates `α, ᾱ` inside the unit disc; it is real.
In statements 1–4 the plastic number enters as any real `ρ` with `ρ ^ 3 = ρ + 1` (statement 7:
the equation has exactly one real solution).

The plastic number:

1. `plastic_settling_sum` — for every real `ρ` with `ρ³ = ρ + 1`:
   `HasSum (fun n ↦ ‖ρ^(n+1)‖²) ρ`, that is `∑_{n ≥ 1} ‖ρⁿ‖² = ρ`. The headline.
2. `plastic_tsum` — the `tsum` form, `∑' n, ‖ρ^(n+1)‖² = ρ`. A routine consequence of 1.
3. `plastic_even_trace` — for every complex `α ≠ ρ` with `α³ = α + 1` (so `α` is one of the two
   conjugates of `ρ` inside the unit disc): `∑_{n ≥ 0} (α^(2n) + ᾱ^(2n)) = ρ`. The even-power
   trace of the hidden pair is the generator. This is the mechanism behind 1: because
   `x³ − x − 1 = (x − 1)·x·(x + 1) − 1`, the resolvent trace `∑_{roots r} 1/(1 − r²)` vanishes, so
   the two hidden conjugates contribute `−1/(1 − ρ²) = 1/(ρ² − 1) = ρ`.
4. `perrin_round_threshold` — for every `n ≥ 10` the nearest integer to `ρⁿ` is the Perrin number
   `P(n)`, and for `n = 9` it is not (`P(9) = 12`, `ρ⁹ = 12.56…`). The threshold stated in OEIS
   A001608 (R. Stephan, 2002), here proved and shown sharp.

Cubic numbers with a complex conjugate pair (the general form):

5. `cubic_trace_sum` — for a real `θ`, a complex `α` with `‖α‖ < 1`, and integers `a, b, c` that
   are the elementary symmetric functions of `(θ, α, ᾱ)` (`θ + α + ᾱ = a`,
   `θ(α + ᾱ) + αᾱ = b`, `θαᾱ = c`): `∑_{n ≥ 1} (Sₙ − θⁿ)² = Re (geo α)`. The Pisot series of the
   trace defect is a rational function of the conjugates.
6. `cubic_settling_sum` — under the same hypotheses, for every `N` with `‖α‖^N < 1/4`:
   `∑_{n ≥ 1} ‖θⁿ‖² = Re (geo α) + ∑_{n = 1}^{N} (‖θⁿ‖² − (Sₙ − θⁿ)²)`. Pisot's convergence in
   quantitative form for this class: the value is `geo` plus a finite rounding correction, because
   beyond `N` the nearest integer to `θⁿ` is `Sₙ`. Statement 1 is the case `a = 0, b = −1, c = 1`,
   `N = 10` (the smallest `N` with `ρ^(−N/2) < 1/4`; the `n = 10` correction term is zero), with
   `Re (geo α) = 2ρ² + 3ρ − 2` and correction `2 − 2ρ − 2ρ²`, summing to `ρ`.

Supporting:

7. `existsUnique_root` — `x³ = x + 1` has exactly one real solution.

Statements 5 and 6 assume neither `θ > 1` nor irreducibility; they hold for any real `θ` with
such a conjugate pair. Pisot's theorem itself (convergence iff Pisot, for every degree) is not
formalized; statements 5–6 give the convergent value for the cubic complex-pair case. The four
definitions above are the only ones the entry adds, and `Solution.lean` repeats them verbatim.
Every statement here is left unproved as a placeholder; `Solution.lean` proves each, with the
identical statement.

Not to be confused with `ρ = ∑_{n ≥ 0} ρ^(−5n)` (equivalently `ρ⁵ = ρ⁴ + 1`), a geometric series
in `ρ` with no nearest-integer content. Among Pisot numbers the value `∑ ‖θⁿ‖² = θ` is specific to
`ρ` as far as computed (for the golden ratio the sum is `φ⁻²`; no other instance among 109 Pisot
units of degree 2–4 with small coefficients; computed, not formalized), and whether it
characterizes `ρ` is open.

Application to time (no compared statement asserts it). In the arithmetic of time (the registered
entries PALOMAR-2026-08-19-000006 and its companions) the tick is multiplication by `ρ` on `ℚ(ρ)`
and the record is the integer lattice: the Perrin integers are the settled values of the powers
(statement 4). Read so, statement 1 says that the total squared distance by which the tick history
falls short of its record is exactly one tick's unit, `ρ`, and statement 3 says that this unit is
returned by the two conjugates that are not seen — the generator is the trace of its own hidden
places. The quartic companion `Q`, `Q⁴ = Q + 1`, is not Pisot (a conjugate pair of modulus
`1.063…`), so by Pisot's theorem its series diverges for every `λ` (not proved here): the cubic
step settles onto a record and the quartic step does not. That physical time is this arithmetic
is the identification stated in the companion entry, as an identification; the theorems here are
its arithmetic content.
-/

open Complex Finset ComplexConjugate

namespace SettlingSum

/-- Distance from a real number to the nearest integer, `‖x‖ = |x − round x|`. -/
noncomputable def distInt (x : ℝ) : ℝ := |x - round x|

/-- Newton power sums `Sₙ = θⁿ + αⁿ + ᾱⁿ` of the three roots of `x³ − a x² + b x − c`, as
integers: `S₀ = 3, S₁ = a, S₂ = a² − 2b, Sₙ₊₃ = a Sₙ₊₂ − b Sₙ₊₁ + c Sₙ`. -/
def powerSum (a b c : ℤ) : ℕ → ℤ
  | 0 => 3
  | 1 => a
  | 2 => a ^ 2 - 2 * b
  | (n + 3) => a * powerSum a b c (n + 2) - b * powerSum a b c (n + 1) + c * powerSum a b c n

/-- The Perrin sequence `3, 0, 2, 3, 2, 5, 5, 7, 10, 12, …`: `P(n) = ρⁿ + zⁿ + z̄ⁿ` for the roots
`ρ, z, z̄` of `x³ − x − 1`. -/
def perrin : ℕ → ℤ
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | (n + 3) => perrin (n + 1) + perrin n

/-- The geometric part `geo α = α²/(1 − α²) + ᾱ²/(1 − ᾱ²) + 2αᾱ/(1 − αᾱ)`: the sum of
`αᵢαⱼ/(1 − αᵢαⱼ)` over the two conjugates `α, ᾱ` inside the unit disc. It is real. -/
noncomputable def geo (α : ℂ) : ℂ :=
  α ^ 2 / (1 - α ^ 2) + conj α ^ 2 / (1 - conj α ^ 2) + 2 * (α * conj α) / (1 - α * conj α)

/-- **1. The settling sum of the plastic number.** For every real root `ρ` of `x³ − x − 1`,
`∑_{n ≥ 1} ‖ρⁿ‖² = ρ`. -/
theorem plastic_settling_sum {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    HasSum (fun n : ℕ => distInt (ρ ^ (n + 1)) ^ 2) ρ := by
  sorry

/-- **2.** The `tsum` form of statement 1. -/
theorem plastic_tsum {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∑' n : ℕ, distInt (ρ ^ (n + 1)) ^ 2 = ρ := by
  sorry

/-- **3. The even-power trace of the hidden pair is the generator.** For every complex root
`α ≠ ρ` of `x³ − x − 1`, `∑_{n ≥ 0} (α^(2n) + ᾱ^(2n)) = ρ`. -/
theorem plastic_even_trace {ρ : ℝ} {α : ℂ} (hρ : ρ ^ 3 = ρ + 1) (hα : α ^ 3 = α + 1)
    (hne : α ≠ (ρ : ℂ)) :
    HasSum (fun n : ℕ => α ^ (2 * n) + conj α ^ (2 * n)) (ρ : ℂ) := by
  sorry

/-- **4. Perrin numbers are the nearest integers to `ρⁿ` from `n = 10` on, and not at `n = 9`.** -/
theorem perrin_round_threshold {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    (∀ n : ℕ, 10 ≤ n → round (ρ ^ n) = perrin n) ∧ round (ρ ^ 9) ≠ perrin 9 := by
  sorry

/-- **5. The Pisot series of the trace defect.** `∑_{n ≥ 1} (Sₙ − θⁿ)² = Re (geo α)`. -/
theorem cubic_trace_sum {θ : ℝ} {α : ℂ} {a b c : ℤ}
    (h1 : (θ : ℂ) + α + conj α = a) (h2 : (θ : ℂ) * (α + conj α) + α * conj α = b)
    (h3 : (θ : ℂ) * (α * conj α) = c) (hα : ‖α‖ < 1) :
    HasSum (fun n : ℕ => ((powerSum a b c (n + 1) : ℝ) - θ ^ (n + 1)) ^ 2) (geo α).re := by
  sorry

/-- **6. The settling sum of a cubic number with a complex conjugate pair.** For every `N` with
`‖α‖^N < 1/4`, `∑_{n ≥ 1} ‖θⁿ‖² = Re (geo α) + ∑_{n = 1}^{N} (‖θⁿ‖² − (Sₙ − θⁿ)²)`. -/
theorem cubic_settling_sum {θ : ℝ} {α : ℂ} {a b c : ℤ}
    (h1 : (θ : ℂ) + α + conj α = a) (h2 : (θ : ℂ) * (α + conj α) + α * conj α = b)
    (h3 : (θ : ℂ) * (α * conj α) = c) (hα : ‖α‖ < 1) {N : ℕ} (hN : ‖α‖ ^ N < 1 / 4) :
    HasSum (fun n : ℕ => distInt (θ ^ (n + 1)) ^ 2)
      ((geo α).re + ∑ n ∈ range N,
        (distInt (θ ^ (n + 1)) ^ 2 - ((powerSum a b c (n + 1) : ℝ) - θ ^ (n + 1)) ^ 2)) := by
  sorry

/-- **7.** `x³ = x + 1` has exactly one real solution. -/
theorem existsUnique_root : ∃! x : ℝ, x ^ 3 = x + 1 := by
  sorry

end SettlingSum
