module
public import Mathlib
public import PisotSum
public import PisotSumCubic

@[expose] public section
/-!
# The settling sum of the plastic number: proofs of the compared statements

Each of the seven statements of `Challenge.lean` is proved here, with the identical statement, by
transfer from the proof library (`PisotSum.lean`, `PisotSumCubic.lean`, namespace `PisotSum`). The
four definitions of `Challenge.lean` are repeated verbatim.

* Statement 1: `PisotSum.plastic_settling_sum_of_root` (`SettlingSum.distInt` and
  `PisotSum.distInt` have the same body, so the transfer is definitional).
* Statement 2: statement 1 and `HasSum.tsum_eq`.
* Statement 3: proved here. From `α³ = α + 1` and `ρ³ = ρ + 1`,
  `(α − ρ)(α² + ρα + ρ² − 1) = 0`, so `α` satisfies the real-coefficient quadratic
  `x² + ρx + (ρ² − 1) = 0`; `α` is not real (a real root of `x³ = x + 1` is `ρ`, by
  `PisotSum.existsUnique_root`), so `ᾱ ≠ α` is the other root and Vieta gives `α + ᾱ = −ρ`,
  `αᾱ = ρ² − 1`. Hence `‖α‖² = ρ² − 1 < 1`, the two geometric series converge, and
  `1/(1 − α²) + 1/(1 − ᾱ²) = (2 − s)/(1 − s + p)` with `s = α² + ᾱ² = 2 − ρ²`, `p = (ρ² − 1)²`,
  which is `ρ` by `ρ³ = ρ + 1`.
* Statement 4: `PisotSum.abs_t_lt_half` (`|P(n) − ρⁿ| < 1/2` for `n ≥ 10`) with `round_eq_iff`,
  after `SettlingSum.perrin = PisotSum.perrin` (same recurrence); the `n = 9` half from
  `ρ⁹ = 3ρ² + 4ρ + 2 > 12.5` and `P(9) = 12`.
* Statement 5: `PisotSum.cubic_hasSum_t_sq`, after `SettlingSum.powerSum = PisotSum.powerSum`
  (same recurrence) and `SettlingSum.geo = PisotSum.geoC` (same body).
* Statement 6: `PisotSum.cubic_settling_sum_of_lt`, the same bridges.
* Statement 7: `PisotSum.existsUnique_root`.
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

/-! ### Bridges to the library -/

/-- `SettlingSum.distInt` is `PisotSum.distInt` (same body). -/
private theorem distInt_eq (x : ℝ) : distInt x = PisotSum.distInt x := rfl

/-- `SettlingSum.distInt` is `PisotSum.distInt'` (same body). -/
private theorem distInt_eq' (x : ℝ) : distInt x = PisotSum.distInt' x := rfl

/-- `SettlingSum.geo` is `PisotSum.geoC` (same body). -/
private theorem geo_eq (α : ℂ) : geo α = PisotSum.geoC α := rfl

/-- `SettlingSum.perrin` is `PisotSum.perrin` (same recurrence; three consecutive values). -/
private theorem perrin_eq_aux (n : ℕ) :
    perrin n = PisotSum.perrin n ∧ perrin (n + 1) = PisotSum.perrin (n + 1) ∧
      perrin (n + 2) = PisotSum.perrin (n + 2) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show perrin (n + 3) = PisotSum.perrin (n + 3)
    rw [perrin, PisotSum.perrin, h0, h1]

/-- `SettlingSum.perrin` is `PisotSum.perrin`. -/
private theorem perrin_eq (n : ℕ) : perrin n = PisotSum.perrin n := (perrin_eq_aux n).1

/-- `SettlingSum.powerSum` is `PisotSum.powerSum` (same recurrence; three consecutive values). -/
private theorem powerSum_eq_aux (a b c : ℤ) (n : ℕ) :
    powerSum a b c n = PisotSum.powerSum a b c n ∧
      powerSum a b c (n + 1) = PisotSum.powerSum a b c (n + 1) ∧
      powerSum a b c (n + 2) = PisotSum.powerSum a b c (n + 2) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show powerSum a b c (n + 3) = PisotSum.powerSum a b c (n + 3)
    rw [powerSum, PisotSum.powerSum, h0, h1, h2]

/-- `SettlingSum.powerSum` is `PisotSum.powerSum`. -/
private theorem powerSum_eq (a b c : ℤ) (n : ℕ) :
    powerSum a b c n = PisotSum.powerSum a b c n := (powerSum_eq_aux a b c n).1

/-! ### The compared statements -/

/-- **1. The settling sum of the plastic number.** For every real root `ρ` of `x³ − x − 1`,
`∑_{n ≥ 1} ‖ρⁿ‖² = ρ`. -/
theorem plastic_settling_sum {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    HasSum (fun n : ℕ => distInt (ρ ^ (n + 1)) ^ 2) ρ := by
  simpa only [distInt_eq] using PisotSum.plastic_settling_sum_of_root hρ

/-- **2.** The `tsum` form of statement 1. -/
theorem plastic_tsum {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∑' n : ℕ, distInt (ρ ^ (n + 1)) ^ 2 = ρ :=
  (plastic_settling_sum hρ).tsum_eq

/-- **3. The even-power trace of the hidden pair is the generator.** For every complex root
`α ≠ ρ` of `x³ − x − 1`, `∑_{n ≥ 0} (α^(2n) + ᾱ^(2n)) = ρ`. -/
theorem plastic_even_trace {ρ : ℝ} {α : ℂ} (hρ : ρ ^ 3 = ρ + 1) (hα : α ^ 3 = α + 1)
    (hne : α ≠ (ρ : ℂ)) :
    HasSum (fun n : ℕ => α ^ (2 * n) + conj α ^ (2 * n)) (ρ : ℂ) := by
  have hρC : (ρ : ℂ) ^ 3 = ρ + 1 := by exact_mod_cast hρ
  -- `α` satisfies the quadratic `x² + ρx + (ρ² − 1) = 0`
  have hq : α ^ 2 + (ρ : ℂ) * α + ((ρ : ℂ) ^ 2 - 1) = 0 := by
    have h : (α - ρ) * (α ^ 2 + (ρ : ℂ) * α + ((ρ : ℂ) ^ 2 - 1)) = 0 := by
      linear_combination hα - hρC
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  -- so does `ᾱ` (real coefficients)
  have hq' : conj α ^ 2 + (ρ : ℂ) * conj α + ((ρ : ℂ) ^ 2 - 1) = 0 := by
    have h := congrArg conj hq
    simpa only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, Complex.conj_ofReal]
      using h
  -- `α` is not real: a real root of `x³ = x + 1` is `ρ`
  have hαre : α ≠ (α.re : ℂ) := by
    intro h
    have h3 : (α.re : ℂ) ^ 3 = (α.re : ℂ) + 1 := by rw [← h]; exact hα
    have h3' : α.re ^ 3 = α.re + 1 := by exact_mod_cast h3
    obtain ⟨x, -, hx⟩ := PisotSum.existsUnique_root
    have e : α.re = ρ := (hx _ h3').trans (hx _ hρ).symm
    exact hne (by rw [h, e])
  have hconj : α - conj α ≠ 0 := fun h =>
    hαre (Complex.conj_eq_iff_re.1 (sub_eq_zero.1 h).symm).symm
  -- Vieta
  have hsum : α + conj α = -(ρ : ℂ) := by
    have h : (α - conj α) * (α + conj α + ρ) = 0 := by linear_combination hq - hq'
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hconj
    · linear_combination h
  have hprod : α * conj α = (ρ : ℂ) ^ 2 - 1 := by linear_combination α * hsum - hq
  -- norms
  have hn : ‖α‖ ^ 2 = ρ ^ 2 - 1 := by
    have h := hprod
    rw [Complex.mul_conj] at h
    rw [Complex.sq_norm]
    exact_mod_cast h
  have hlt : ‖α‖ < 1 := by
    have := (PisotSum.rho_sq_bounds hρ).2
    nlinarith [norm_nonneg α]
  have ha : ‖α ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg α]
  have hb : ‖conj α ^ 2‖ < 1 := by rw [norm_pow, Complex.norm_conj]; nlinarith [norm_nonneg α]
  have h1 : (1 : ℂ) - α ^ 2 ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at ha
    exact lt_irrefl _ ha
  have h2 : (1 : ℂ) - conj α ^ 2 ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at hb
    exact lt_irrefl _ hb
  -- the two geometric series
  have g := (hasSum_geometric_of_norm_lt_one ha).add (hasSum_geometric_of_norm_lt_one hb)
  convert g using 1
  · funext n
    rw [pow_mul, pow_mul]
  · have hA : α ^ 2 + conj α ^ 2 = 2 - (ρ : ℂ) ^ 2 := by
      linear_combination (α + conj α - ρ) * hsum - 2 * hprod
    have hB : α ^ 2 * conj α ^ 2 = ((ρ : ℂ) ^ 2 - 1) ^ 2 := by
      linear_combination (α * conj α + ρ ^ 2 - 1) * hprod
    rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ h1 h2, eq_div_iff (mul_ne_zero h1 h2)]
    linear_combination (1 - (ρ : ℂ)) * hA + (ρ : ℂ) * hB + (ρ : ℂ) ^ 2 * hρC

/-- **4. Perrin numbers are the nearest integers to `ρⁿ` from `n = 10` on, and not at `n = 9`.** -/
theorem perrin_round_threshold {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    (∀ n : ℕ, 10 ≤ n → round (ρ ^ n) = perrin n) ∧ round (ρ ^ 9) ≠ perrin 9 := by
  constructor
  · intro n hn
    have h := PisotSum.abs_t_lt_half hρ hn
    rw [abs_lt] at h
    unfold PisotSum.t at h
    rw [perrin_eq]
    exact round_eq_iff.2 ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    rw [round_eq_iff] at h
    have p9 : perrin 9 = 12 := rfl
    rw [p9] at h
    have e9 : ρ ^ 9 = 3 * ρ ^ 2 + 4 * ρ + 2 := by
      linear_combination (ρ ^ 6 + ρ ^ 4 + ρ ^ 3 + ρ ^ 2 + 2 * ρ + 2) * hρ
    have hlo := (PisotSum.plastic_bounds hρ).1
    have hlo2 := (PisotSum.rho_sq_bounds hρ).1
    have h2 := h.2
    push_cast at h2
    linarith

/-- **5. The Pisot series of the trace defect.** `∑_{n ≥ 1} (Sₙ − θⁿ)² = Re (geo α)`. -/
theorem cubic_trace_sum {θ : ℝ} {α : ℂ} {a b c : ℤ}
    (h1 : (θ : ℂ) + α + conj α = a) (h2 : (θ : ℂ) * (α + conj α) + α * conj α = b)
    (h3 : (θ : ℂ) * (α * conj α) = c) (hα : ‖α‖ < 1) :
    HasSum (fun n : ℕ => ((powerSum a b c (n + 1) : ℝ) - θ ^ (n + 1)) ^ 2) (geo α).re := by
  have h := PisotSum.cubic_hasSum_t_sq h1 h2 h3 hα
  rw [geo_eq]
  convert h using 1
  funext n
  simp only [PisotSum.tc, powerSum_eq]

/-- **6. The settling sum of a cubic number with a complex conjugate pair.** For every `N` with
`‖α‖^N < 1/4`, `∑_{n ≥ 1} ‖θⁿ‖² = Re (geo α) + ∑_{n = 1}^{N} (‖θⁿ‖² − (Sₙ − θⁿ)²)`. -/
theorem cubic_settling_sum {θ : ℝ} {α : ℂ} {a b c : ℤ}
    (h1 : (θ : ℂ) + α + conj α = a) (h2 : (θ : ℂ) * (α + conj α) + α * conj α = b)
    (h3 : (θ : ℂ) * (α * conj α) = c) (hα : ‖α‖ < 1) {N : ℕ} (hN : ‖α‖ ^ N < 1 / 4) :
    HasSum (fun n : ℕ => distInt (θ ^ (n + 1)) ^ 2)
      ((geo α).re + ∑ n ∈ range N,
        (distInt (θ ^ (n + 1)) ^ 2 - ((powerSum a b c (n + 1) : ℝ) - θ ^ (n + 1)) ^ 2)) := by
  have h := PisotSum.cubic_settling_sum_of_lt h1 h2 h3 hα hN
  rw [geo_eq]
  simp only [distInt_eq', powerSum_eq]
  exact h

/-- **7.** `x³ = x + 1` has exactly one real solution. -/
theorem existsUnique_root : ∃! x : ℝ, x ^ 3 = x + 1 :=
  PisotSum.existsUnique_root

end SettlingSum
