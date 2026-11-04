# The settling sum of the plastic number: `∑_{n ≥ 1} ‖ρⁿ‖² = ρ`

Kernel-checked, in Lean 4 + Mathlib: write `‖x‖ = |x − round x|` for the distance from a real number to
the nearest integer, and let `ρ = 1.3247…` be the plastic number, the real root of `x³ = x + 1` and the
smallest Pisot number (Siegel 1944). Convergence of `∑_{n ≥ 1} ‖θⁿ‖²` for a Pisot number `θ` is elementary, and Pisot (1938) proved the
converse (convergence for some real `λ ≠ 0` forces `θ` Pisot); neither gives the value. For `ρ` the value is `ρ` itself: the total squared
distance by which the powers of `ρ` miss the integers is the number that generates them. The principal step of the mechanism
is also a theorem here: the two conjugates of `ρ` inside the unit disc have even-power trace
`∑_{n ≥ 0} (z^(2n) + z̄^(2n)) = ρ`, because `x³ − x − 1 = (x − 1)·x·(x + 1) − 1` takes the value `−1` at
`−1`, `0` and `1`, so the resolvent trace `∑_{roots} 1/(1 − r²)` vanishes (the one remaining step, a finite identity in
`ℚ(ρ)`, is computed, not explained; see below). The entry also proves the
general cubic form (the Pisot series of any real `θ` with a complex conjugate pair inside the disc is a
rational function of the conjugates plus a finite rounding correction) and the sharp threshold from which
the Perrin numbers are the nearest integers to `ρⁿ` (`n ≥ 10`, and not at `n = 9`).

## The objects

- `‖x‖ = |x − round x|`, written `distInt x` in the Lean files, with Mathlib's `round`.
- The **Perrin sequence** `P(0), P(1), P(2), … = 3, 0, 2, 3, 2, 5, 5, 7, 10, 12, …`, `P(n+3) = P(n+1) + P(n)`.
  It is the trace of the powers: `P(n) = ρⁿ + zⁿ + z̄ⁿ`, where `z, z̄` are the complex roots of
  `x³ − x − 1`.
- The **hidden pair** `z, z̄`, with `|z|² = ρ² − 1 = 1/ρ` (the product of the three roots is `1`), so
  `|z| = ρ^(−1/2) = 0.8688…` and the trace defect `t_n := P(n) − ρⁿ = zⁿ + z̄ⁿ` decays geometrically.
- The **Newton power sums** `powerSum a b c n = Sₙ = θⁿ + αⁿ + ᾱⁿ` of the three roots of
  `x³ − a x² + b x − c`, integers by the recurrence `S₀ = 3, S₁ = a, S₂ = a² − 2b,
  Sₙ₊₃ = a Sₙ₊₂ − b Sₙ₊₁ + c Sₙ`; the Perrin sequence is the case `a = 0, b = −1, c = 1`.
- The **geometric part** `geo α = α²/(1 − α²) + ᾱ²/(1 − ᾱ²) + 2αᾱ/(1 − αᾱ)`: the sum of
  `αᵢαⱼ/(1 − αᵢαⱼ)` over the two conjugates `α, ᾱ` inside the unit disc. It is real.

## The compared statements (namespace `SettlingSum`)

In statements 1–4 the plastic number enters as any real `ρ` with `ρ³ = ρ + 1` (statement 7: there is
exactly one). Sums over `n ≥ 1` are written `fun n ↦ ·^(n+1)` over `ℕ`.

| # | name | statement |
|---|------|-----------|
| 1 | `plastic_settling_sum` | `HasSum (fun n ↦ ‖ρ^(n+1)‖²) ρ`: `∑_{n ≥ 1} ‖ρⁿ‖² = ρ`. The headline. |
| 2 | `plastic_tsum` | the `tsum` form, `∑' n, ‖ρ^(n+1)‖² = ρ`; a routine consequence of 1 |
| 3 | `plastic_even_trace` | for every complex `α ≠ ρ` with `α³ = α + 1`: `∑_{n ≥ 0} (α^(2n) + ᾱ^(2n)) = ρ`. The even-power trace of the hidden pair is the generator; the mechanism behind 1 |
| 4 | `perrin_round_threshold` | `round (ρⁿ) = P(n)` for every `n ≥ 10`, and `round (ρ⁹) ≠ P(9)` (`P(9) = 12`, `ρ⁹ = 12.56…`): the threshold in OEIS A001608 (R. Stephan, 2002), proved and shown sharp |
| 5 | `cubic_trace_sum` | for real `θ`, complex `α` with `‖α‖ < 1`, integers `a, b, c` with `θ + α + ᾱ = a`, `θ(α + ᾱ) + αᾱ = b`, `θαᾱ = c`: `∑_{n ≥ 1} (Sₙ − θⁿ)² = Re (geo α)` |
| 6 | `cubic_settling_sum` | under the same hypotheses, for every `N` with `‖α‖^N < 1/4`: `∑_{n ≥ 1} ‖θⁿ‖² = Re (geo α) + ∑_{n=1}^{N} (‖θⁿ‖² − (Sₙ − θⁿ)²)` |
| 7 | `existsUnique_root` | `x³ = x + 1` has exactly one real solution |

Statements 5 and 6 assume neither `θ > 1` nor irreducibility nor that `a, b, c` come from a Pisot
number: a real `θ`, a complex `α` with `‖α‖ < 1` and the three Vieta equations are the whole
hypothesis. Statement 1 is statement 6 at `a = 0, b = −1, c = 1` with `N = 10` (the smallest `N` with
`ρ^(−N/2) < 1/4`; the `n = 10` correction term is zero), where
`Re (geo α) = 2ρ² + 3ρ − 2` and the correction is `2 − 2ρ − 2ρ²`, summing to `ρ`. Every compared
theorem depends on `propext`, `Classical.choice` and `Quot.sound` only.

## The proof in five lines

1. `ρⁿ = P(n) − t_n` with `t_n = zⁿ + z̄ⁿ`, so `‖ρⁿ‖ = |t_n − round t_n|`, and `‖ρⁿ‖ = |t_n|` whenever
   `|t_n| < 1/2`.
2. `|t_n| ≤ 2|z|ⁿ = 2ρ^(−n/2)`, and `2ρ^(−5) = 0.490… < 1/2`, so `‖ρⁿ‖ = |t_n|` for every `n ≥ 10`
   (statement 4 is this bound with the single check at `n = 9`).
3. `∑_{n ≥ 1} t_n² = ∑ (z²)ⁿ + ∑ (z̄²)ⁿ + 2 ∑ (zz̄)ⁿ`, three geometric series (Mathlib's
   `hasSum_geometric_of_norm_lt_one`), with sum `Re (geo z) = 2ρ² + 3ρ − 2 = 5.4839…` in `ℚ(ρ)`.
4. The exceptions are `n ∈ {1, 3, 4, 5, 8, 9}`, with `round t_n = −1, 1, −1, 1, 1, −1`; at each,
   `‖ρⁿ‖² − t_n² = k² − 2k·t_n` with `k = round t_n`, and the six corrections sum to `2 − 2ρ − 2ρ²`.
5. `(2ρ² + 3ρ − 2) + (2 − 2ρ − 2ρ²) = ρ`, an identity in `ℚ(ρ)` (it needs only `ρ³ = ρ + 1`).

**The mechanism.** Split `t_n² = t_{2n} + 2|z|^(2n)`, so the geometric part is a rotational half
`∑_{n ≥ 1} t_{2n}` plus a radial half `2 ∑_{n ≥ 1} ρ^(−n)`. The polynomial is
`f(x) = x³ − x − 1 = (x − 1)·x·(x + 1) − 1`, so `f(−1) = f(0) = f(1) = −1` and `f'(1) = f'(−1) = 2`.
Hence the resolvent trace over all three roots,
`∑_{roots r} 1/(1 − r²) = ½ [f'(1)/f(1) − f'(−1)/f(−1)] = ½ [(−2) − (−2)] = 0`, vanishes, and the
hidden pair alone gives `1/(1 − z²) + 1/(1 − z̄²) = −1/(1 − ρ²) = 1/(ρ² − 1) = ρ`: that is
statement 3, `∑_{n ≥ 0} (z^(2n) + z̄^(2n)) = ρ`, so the rotational half is `ρ − 2`. The radial half is
`2/(ρ − 1) = 2ρ⁴ = 2ρ² + 2ρ`, again because `ρ(ρ − 1)(ρ + 1) = 1`. What remains is one equality:
the six rounding events refund exactly `2ρ⁴ − 2` (`2ρ⁴ − 2 + (2 − 2ρ⁴) = 0`), so that the headline
reduces to statement 3. That last step is a finite computation in `ℚ(ρ)` — the signed exceptional sum
`∑ k·ρⁿ = (ρ³ − ρ) + (ρ⁵ − ρ⁴) + ρ⁸(1 − ρ) = 1 + 1 − ρ⁴` — and no principle is offered for it here.

## Relation to the literature

- Pisot (1938): for real `θ > 1`, `∑ ‖λθⁿ‖² < ∞` for some real `λ ≠ 0` iff `θ` is a Pisot number (and
  then `λ ∈ ℚ(θ)`). The convergence of the series in statement 1 is this theorem at `λ = 1`; the value
  is not part of it. Siegel (1944): `ρ` is the smallest Pisot number.
- Salem (1944) gives an explicit upper bound for the series, `∑_{n ≥ 0} sin²(πλθⁿ) ≤ π²(2θ+1)²/(θ−1)²`
  for some `1 ≤ λ < θ`: a bound, not an evaluation.
- OEIS A001608 (Perrin) carries R. Stephan's comment (2002) that `P(n) = round(ρⁿ)` for `n > 9`; statement
  4 proves it and shows the threshold sharp. OEIS A084252 (H. Bottomley, 2003) tabulates
  `round(1/(ρⁿ − round ρⁿ))`, the nearest prior tabulation of `‖ρⁿ‖`; it states no sum.
- We are not aware of a prior statement of the value `∑_{n ≥ 1} ‖ρⁿ‖² = ρ`, of a closed-form evaluation
  of `∑ ‖θⁿ‖²` for any specific Pisot number, or of statements 5–6 as stated results. The search behind
  that sentence, recorded on 2026-11-02, covered OEIS A060006, A001608 and A084252, MathWorld ("Plastic
  Constant"), Wikipedia ("Plastic ratio"), the CRC Concise Encyclopedia entry on Pisot–Vijayaraghavan
  constants, and six web searches (including Dubickas's and Zaïmi's work on `‖λαⁿ‖`, which concerns
  limits and lower bounds, not series values). Not read: Bertin et al., *Pisot and Salem Numbers*
  (1992), chapter 5; Pisot's 1938 paper itself; MathSciNet. Pisot 1938, Siegel 1944 and Salem 1944 are
  cited from the CRC reference list, not from the originals. The general formula
  `∑_{n ≥ 1} (∑ᵢ αᵢⁿ)² = ∑_{i,j} αᵢαⱼ/(1 − αᵢαⱼ)` behind statement 5 is a two-line consequence of
  expanding the square; no novelty is claimed for it.
- Not to be confused with the identity `ρ = ∑_{n ≥ 0} ρ^(−5n)` (equivalently `ρ⁵ = ρ⁴ + 1`), a plain
  geometric series in `ρ` with no nearest-integer content.

## What is not claimed

- Pisot's theorem (convergence iff Pisot, in every degree) is not formalized. Statements 5–6 give the
  convergent value for the cubic complex-pair case only, and the divergence for non-Pisot numbers is
  not proved here.
- The census is computed, not formalized. Among 109 Pisot units of degree 2–4 with small coefficients
  (33 cubic, `x³ + ax² + bx ± 1` with `|a|, |b| ≤ 4`; 10 quadratic, coefficients up to 6; 66 quartic,
  coefficients up to 3), `ρ` is the only one whose sum `S(θ) = ∑ ‖θⁿ‖²` equals `θ`, and the only one
  whose sum is any element `a + bθ + cθ²` with `a, b, c ∈ {−1, 0, 1}`. The only other monomial value is
  the golden ratio's, `S(φ) = φ⁻² = 0.3819…`; the supergolden number (`x³ = x² + 1`) gives `0.9775…`
  and the tribonacci number `0.5685…`. Whether `S(θ) = θ` characterizes `ρ` among Pisot numbers is open.
- The exact value `2ρ² + 3ρ − 2` is an algebraic integer because `ρ ± 1` are units (`f(±1) = −1`); the
  census shows other cubics acquiring denominators from `f(1)·f(−1)`. Only the `ρ` case is in the kernel.
- Statements 2 and 7 are routine (the `tsum` form of 1; uniqueness of the real root).
- The content first presented here is the exact value (statement 1), its mechanism (statement 3: the
  resolvent trace at `±1` vanishes for `x³ − x − 1`, a principle, not a computation) and the general cubic
  form (statements 5–6). Statement 4 is different in kind: its claim is prior work (R. Stephan's 2002
  comment on OEIS A001608, stated there without proof), which this entry proves and shows sharp; the
  provenance metadata records it so. The three geometric series and the Perrin trace identity
  `P(n) = ρⁿ + zⁿ + z̄ⁿ` are classical; the six-exception bookkeeping is a finite computation.

## Application to time (no compared statement asserts it)

In the arithmetic of time (the registered entries below) the tick is multiplication by `ρ` on `ℚ(ρ)`
and the record is the integer lattice: the Perrin integers are the settled values of the powers
(statement 4). Read so, statement 1 says that the total squared distance by which the tick history
falls short of its record is exactly one tick's unit, `ρ`, and statement 3 says that this unit is
returned by the two conjugates that are not seen — the generator is the trace of its own hidden
places. The quartic companion `Q`, `Q⁴ = Q + 1`, is not Pisot (a conjugate pair of modulus `1.063…`),
so by Pisot's theorem its series diverges for every `λ` (not proved here): the cubic step settles onto
a record and the quartic step does not. That physical time is this arithmetic is the identification
stated in the companion entry, as an identification; the theorems here are its arithmetic content.

## Companion entries

This entry is a companion of the registered entry PALOMAR-2026-08-19-000006,
[stalex444/arithmetic-of-time](https://github.com/stalex444/arithmetic-of-time), whose compared
statements include the tick's exact contraction rate and the chirality of the Padovan substitution; this
entry gives the settling of the tick history onto its record, as an exact value. The other registered
arrow entries are PALOMAR-2026-09-04-000004
([stalex444/chiral-padovan-histories](https://github.com/stalex444/chiral-padovan-histories)) and
PALOMAR-2026-10-18-000019
([stalex444/arithmetic-of-time-slowest-clock](https://github.com/stalex444/arithmetic-of-time-slowest-clock)).
No statement is shared with any of them, and no module is.

## Scope: the claim

The Scope of the companion entry applies to this one unchanged. It is reproduced verbatim below from
that entry's README (its one relative link, to the paper directory, now points into the companion
repository); the declarations and files it names are in the companion repository at its registered
revision
[`c48eb12`](https://github.com/stalex444/arithmetic-of-time/tree/c48eb12817dd1d7ff3dc4d92306c7a4f249e6d7d),
not in this one.

The position taken here is that **time is this arithmetic** — an identity, in
the same grammar as "heat is molecular motion," and earned the same way: by
coverage. The temporal invariants are, one by one, theorems of a single
structure. The tick is multiplication by a unit, and its contraction rate is
exact (`Time.tick_contraction`). The tick never repeats (the rotation is
irrational, `Time.aperiodic`), yet is never random (the word is balanced,
`Time.balanced`). And the settled history is *handed*: read backwards, it is
provably a different object — not by convention, but by theorem
(`Chirality.lean`). On this reading the history is one completed object; the
asymmetry of time is a property of the whole; and nothing needs to orient a
flow, because nothing flows — the "now" is where an observer sits in the
structure, with records on one side (the marked origin of
`OriginDefect.lean`).

Two kinds of statement appear in this repository, and the boundary between
them is kept explicit. **Theorems**: every mathematical claim in the Lean
modules compiles in the kernel; nothing rests on trust. **The
identification**: that physical time is this structure — rather than merely
being described by it — is an identification, the same kind of statement as
"the metric tensor is spacetime geometry." No experiment distinguishes an
exact description from an identity, so this is not a claim any theorem could
settle; it is validated the way every physical identification is validated,
through the measured consequences of the framework it belongs to (see [`paper/`](https://github.com/stalex444/arithmetic-of-time/tree/c48eb12817dd1d7ff3dc4d92306c7a4f249e6d7d/paper) and the companion deposits, e.g. doi:10.5281/zenodo.20417378). The mathematics stands regardless. The claim is which
thing it is.

## Building

```
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The
build record, axiom audit and statement-identity checks are in `BUILD.txt`.

## Files

- `Challenge.lean`: the seven statements, Mathlib-only, as `sorry` placeholders, with the four
  definitions the entry adds (`distInt`, `powerSum`, `perrin`, `geo`).
- `Solution.lean`: the same statements and definitions, verbatim, the statements proved by transfer
  from the library.
- `PisotSum.lean`: the plastic number — the trace identity with the Perrin sequence, the bound
  `|t_n| < 1/2` for `n ≥ 10`, the three geometric series, the six corrections, and the real root.
- `PisotSumCubic.lean`: the general cubic form (statements 5–6) for any real `θ` with a complex
  conjugate pair inside the unit disc.
- `comparator.json`, `formalization.yaml`, `BUILD.txt`: the comparator configuration, the registry
  metadata, and the build record.
- `.github/workflows/palomar-preflight.yml`: the registry's mechanical preflight, run on demand.

License: MIT. Author: Stephanie Alexander.
