module
public import Mathlib

@[expose] public section
/-!
# Settling sums of cubic Pisot numbers: `∑_{n ≥ 1} ‖θⁿ‖² = GEO(θ) + finite correction`

Let `θ` be a real algebraic integer of degree 3 whose other two conjugates form a complex pair
`α, ᾱ` with `|α| < 1` (a cubic Pisot number with complex conjugates).  Write the Vieta data as
integers `a = θ + α + ᾱ`, `b = θ(α + ᾱ) + αᾱ`, `c = θ α ᾱ`, and put `tₙ = Sₙ − θⁿ = αⁿ + ᾱⁿ`
where `Sₙ = θⁿ + αⁿ + ᾱⁿ ∈ ℤ` is the `n`-th power sum (`powerSum a b c n` below).

* `cubic_hasSum_t_sq`: `∑_{n ≥ 1} tₙ² = GEO(θ)`, with
  `GEO(θ) = α²/(1 − α²) + ᾱ²/(1 − ᾱ²) + 2αᾱ/(1 − αᾱ) = ∑_{i,j} αᵢαⱼ/(1 − αᵢαⱼ)` over the two
  small conjugates (a real number, exposed as the real part of that complex expression).
* `cubic_settling_sum_of_lt`: for every `N` with `‖α‖^N < 1/4`,
  `∑_{n ≥ 1} ‖θⁿ‖² = GEO(θ) + ∑_{n=1}^{N} (‖θⁿ‖² − tₙ²)`, the finite correction being the
  rounding defect on the initial segment where `|tₙ|` may exceed `1/2`.
* `cubic_settling_sum`: the `∃ N` form of the same statement.

The plastic number case (`PisotSum.lean`) is `a = 0, b = −1, c = 1`, `N = 10` (the smallest `N` with
`ρ^(−N/2) < 1/4`), with
`GEO = 2ρ² + 3ρ − 2` and correction `2 − 2ρ − 2ρ²`.
-/

open Complex Finset ComplexConjugate

namespace PisotSum

/-- Distance from a real number to the nearest integer, `‖x‖ = |x − round x|`. -/
noncomputable def distInt' (x : ℝ) : ℝ := |x - round x|

/-- Power sums `Sₙ = θⁿ + αⁿ + ᾱⁿ` of the roots of `x³ − a x² + b x − c`, by Newton's identities. -/
def powerSum (a b c : ℤ) : ℕ → ℤ
  | 0 => 3
  | 1 => a
  | 2 => a ^ 2 - 2 * b
  | (n + 3) => a * powerSum a b c (n + 2) - b * powerSum a b c (n + 1) + c * powerSum a b c n

lemma distInt'_eq_of_round (x : ℝ) (m : ℤ) (h1 : (m : ℝ) - 1 / 2 ≤ x) (h2 : x < m + 1 / 2) :
    distInt' x = |x - m| := by
  unfold distInt'
  rw [round_eq_iff.2 ⟨h1, h2⟩]

section Cubic

variable {θ : ℝ} {α : ℂ} {a b c : ℤ}
  (h1 : (θ : ℂ) + α + conj α = a)
  (h2 : (θ : ℂ) * (α + conj α) + α * conj α = b)
  (h3 : (θ : ℂ) * (α * conj α) = c)
include h1 h2 h3

lemma powerSum_eq_aux (n : ℕ) :
    ((powerSum a b c n : ℤ) : ℂ) = (θ : ℂ) ^ n + α ^ n + conj α ^ n ∧
    ((powerSum a b c (n + 1) : ℤ) : ℂ) = (θ : ℂ) ^ (n + 1) + α ^ (n + 1) + conj α ^ (n + 1) ∧
    ((powerSum a b c (n + 2) : ℤ) : ℂ) = (θ : ℂ) ^ (n + 2) + α ^ (n + 2) + conj α ^ (n + 2) := by
  have hθ : (θ : ℂ) ^ 3 = a * (θ : ℂ) ^ 2 - b * θ + c := by
    linear_combination (θ : ℂ) ^ 2 * h1 - (θ : ℂ) * h2 + h3
  have hα : α ^ 3 = a * α ^ 2 - b * α + c := by
    linear_combination α ^ 2 * h1 - α * h2 + h3
  have hβ : conj α ^ 3 = a * conj α ^ 2 - b * conj α + c := by
    linear_combination conj α ^ 2 * h1 - conj α * h2 + h3
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · norm_num [powerSum]
    · simp only [powerSum, pow_one, zero_add]
      linear_combination -h1
    · simp only [powerSum, zero_add]
      push_cast
      linear_combination (-(θ : ℂ) - α - conj α - a) * h1 + 2 * h2
  | succ n ih =>
    obtain ⟨e0, e1, e2⟩ := ih
    refine ⟨e1, e2, ?_⟩
    show ((powerSum a b c (n + 3) : ℤ) : ℂ) =
      (θ : ℂ) ^ (n + 3) + α ^ (n + 3) + conj α ^ (n + 3)
    rw [powerSum]
    push_cast
    rw [e0, e1, e2]
    linear_combination (-(θ : ℂ) ^ n) * hθ + (-(α ^ n)) * hα + (-(conj α ^ n)) * hβ

/-- `tₙ = Sₙ − θⁿ`. -/
noncomputable def tc (θ : ℝ) (a b c : ℤ) (n : ℕ) : ℝ := (powerSum a b c n : ℝ) - θ ^ n

lemma tc_eq (n : ℕ) : ((tc θ a b c n : ℝ) : ℂ) = α ^ n + conj α ^ n := by
  unfold tc
  push_cast
  rw [(powerSum_eq_aux h1 h2 h3 n).1]
  ring

lemma abs_tc_le (n : ℕ) : |tc θ a b c n| ≤ 2 * ‖α‖ ^ n := by
  have h := tc_eq h1 h2 h3 n
  have e : ‖((tc θ a b c n : ℝ) : ℂ)‖ = |tc θ a b c n| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [← e, h]
  calc ‖α ^ n + conj α ^ n‖ ≤ ‖α ^ n‖ + ‖conj α ^ n‖ := norm_add_le _ _
    _ = 2 * ‖α‖ ^ n := by rw [norm_pow, norm_pow, Complex.norm_conj]; ring

/-- The geometric part, as a complex number: `GEO = α²/(1−α²) + ᾱ²/(1−ᾱ²) + 2αᾱ/(1−αᾱ)`. -/
noncomputable def geoC (α : ℂ) : ℂ :=
  α ^ 2 / (1 - α ^ 2) + conj α ^ 2 / (1 - conj α ^ 2) + 2 * (α * conj α) / (1 - α * conj α)

omit h1 h2 h3 in
lemma geoC_real (α : ℂ) : ((geoC α).re : ℂ) = geoC α := by
  apply Complex.conj_eq_iff_re.1
  unfold geoC
  simp only [map_add, map_div₀, map_mul, map_pow, map_sub, map_one, map_ofNat, Complex.conj_conj]
  ring

/-- `∑_{n ≥ 1} tₙ² = GEO(θ)`. -/
lemma cubic_hasSum_t_sq (hα : ‖α‖ < 1) :
    HasSum (fun n : ℕ => tc θ a b c (n + 1) ^ 2) (geoC α).re := by
  have hw1 : ‖conj α‖ < 1 := by rw [Complex.norm_conj]; exact hα
  have ha : ‖α ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg α]
  have hb : ‖conj α ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg (conj α)]
  have hc : ‖α * conj α‖ < 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg α, norm_nonneg (conj α)]
  have g1 := (hasSum_geometric_of_norm_lt_one ha).mul_left (α ^ 2)
  have g2 := (hasSum_geometric_of_norm_lt_one hb).mul_left (conj α ^ 2)
  have g3 := (hasSum_geometric_of_norm_lt_one hc).mul_left (2 * (α * conj α))
  have h := (g1.add g2).add g3
  rw [← Complex.hasSum_ofReal, geoC_real]
  convert h using 1
  · funext n
    push_cast
    rw [tc_eq h1 h2 h3 (n + 1)]
    ring
  · unfold geoC
    simp only [div_eq_mul_inv]

/-- **Settling sum of a cubic Pisot number with complex conjugates**, with the threshold explicit:
for every `N` with `‖α‖^N < 1/4`, `∑_{n ≥ 1} ‖θⁿ‖² = GEO(θ) + ∑_{n=1}^{N} (‖θⁿ‖² − tₙ²)`
(beyond `N`, `|tₙ| ≤ 2‖α‖ⁿ < 1/2`, so the nearest integer to `θⁿ` is `Sₙ`). -/
theorem cubic_settling_sum_of_lt (hα : ‖α‖ < 1) {N : ℕ} (hN : ‖α‖ ^ N < 1 / 4) :
    HasSum (fun n : ℕ => distInt' (θ ^ (n + 1)) ^ 2)
      ((geoC α).re + ∑ n ∈ range N, (distInt' (θ ^ (n + 1)) ^ 2 - tc θ a b c (n + 1) ^ 2)) := by
  have hg := cubic_hasSum_t_sq h1 h2 h3 hα
  have hd : HasSum (fun n : ℕ => distInt' (θ ^ (n + 1)) ^ 2 - tc θ a b c (n + 1) ^ 2)
      (∑ n ∈ range N, (distInt' (θ ^ (n + 1)) ^ 2 - tc θ a b c (n + 1) ^ 2)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    -- `|t_{n+1}| < 1/2`
    have hle := abs_tc_le h1 h2 h3 (n + 1)
    have hpow : ‖α‖ ^ (n + 1) ≤ ‖α‖ ^ N :=
      pow_le_pow_of_le_one (norm_nonneg _) hα.le (by omega)
    have ht : |tc θ a b c (n + 1)| < 1 / 2 := by linarith
    rw [abs_lt] at ht
    have e : θ ^ (n + 1) = (powerSum a b c (n + 1) : ℝ) - tc θ a b c (n + 1) := by
      unfold tc; ring
    rw [distInt'_eq_of_round (θ ^ (n + 1)) (powerSum a b c (n + 1)) (by rw [e]; linarith)
      (by rw [e]; linarith), e, sq_abs]
    ring
  convert hg.add hd using 1
  funext n
  ring

/-- **Settling sum of a cubic Pisot number with complex conjugates.**  For some `N`,
`∑_{n ≥ 1} ‖θⁿ‖² = GEO(θ) + ∑_{n=1}^{N} (‖θⁿ‖² − tₙ²)`. -/
theorem cubic_settling_sum (hα : ‖α‖ < 1) :
    ∃ N : ℕ, HasSum (fun n : ℕ => distInt' (θ ^ (n + 1)) ^ 2)
      ((geoC α).re + ∑ n ∈ range N, (distInt' (θ ^ (n + 1)) ^ 2 - tc θ a b c (n + 1) ^ 2)) := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 4 by norm_num) hα
  exact ⟨N, cubic_settling_sum_of_lt h1 h2 h3 hα hN⟩

end Cubic

end PisotSum
