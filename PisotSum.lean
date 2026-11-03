module
public import Mathlib

@[expose] public section
/-!
# The settling sum of the plastic number: `∑_{n ≥ 1} ‖ρⁿ‖² = ρ`

Let `ρ` be the plastic number, the real root of `x³ − x − 1`, and write
`‖x‖ = |x − round x|` for the distance from a real number to the nearest integer.
Since `ρ` is a Pisot number, `‖ρⁿ‖ → 0` geometrically and the series
`∑_{n ≥ 1} ‖ρⁿ‖²` converges.  This file proves that its value is exactly `ρ`:

`∑_{n ≥ 1} ‖ρⁿ‖² = ρ`.

## Proof

Let `z, z̄` be the two complex roots of `x³ − x − 1`, so that `ρ + z + z̄ = 0`,
`z z̄ = ρ² − 1 = 1/ρ`, and the Perrin numbers `P(n) = ρⁿ + zⁿ + z̄ⁿ` are integers
(`P(0) = 3, P(1) = 0, P(2) = 2, P(n+3) = P(n+1) + P(n)`).  Put `tₙ = P(n) − ρⁿ = zⁿ + z̄ⁿ`.

* `|tₙ| ≤ 2|z|ⁿ = 2ρ^{−n/2}`, which is `< 1/2` for `n ≥ 10`; there `‖ρⁿ‖² = tₙ²`.
* `∑_{n ≥ 1} tₙ² = ∑ (z²)ⁿ + (z̄²)ⁿ + 2(z z̄)ⁿ` is a sum of three geometric series,
  equal to `2ρ² + 3ρ − 2`.
* For `1 ≤ n ≤ 9` the nearest integer to `ρⁿ` is computed from the explicit
  elements `ρⁿ ∈ ℤ[ρ]` and the bounds `1.324 < ρ < 1.325`; the finite correction
  `∑_{n=1}^{9} (‖ρⁿ‖² − tₙ²)` equals `2 − 2ρ − 2ρ²`.
* Total: `(2ρ² + 3ρ − 2) + (2 − 2ρ − 2ρ²) = ρ`.

## Main statements

* `PisotSum.plastic_settling_sum_of_root` — for any real `ρ` with `ρ³ = ρ + 1`,
  `HasSum (fun n ↦ distInt (ρ ^ (n+1)) ^ 2) ρ`.
* `PisotSum.plastic_settling_sum` — the same for `PisotSum.plastic`, the real root.
* `PisotSum.plastic_tsum` — the `tsum` form `∑' n, distInt (plastic ^ (n+1)) ^ 2 = plastic`.
-/

open Complex Finset ComplexConjugate

namespace PisotSum

/-- Distance from a real number to the nearest integer, `‖x‖ = |x − round x|`. -/
noncomputable def distInt (x : ℝ) : ℝ := |x - round x|

/-- The Perrin sequence `3, 0, 2, 3, 2, 5, 5, 7, 10, 12, …`. -/
def perrin : ℕ → ℤ
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | (n + 3) => perrin (n + 1) + perrin n

lemma distInt_eq_of_round (x : ℝ) (m : ℤ) (h1 : (m : ℝ) - 1 / 2 ≤ x) (h2 : x < m + 1 / 2) :
    distInt x = |x - m| := by
  unfold distInt
  rw [round_eq_iff.2 ⟨h1, h2⟩]

section Root

variable {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1)
include hρ

/-- `1.324 < ρ < 1.325` for any real root of `x³ − x − 1`. -/
lemma plastic_bounds : 331 / 250 < ρ ∧ ρ < 53 / 40 := by
  constructor
  · refine lt_of_not_ge fun h => ?_
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sq_nonneg (ρ + 331 / 500)), sub_nonneg.2 h]
  · refine lt_of_not_ge fun h => ?_
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sq_nonneg (ρ + 53 / 80)), sub_nonneg.2 h]

lemma rho_sq_bounds : 1752976 / 1000000 < ρ ^ 2 ∧ ρ ^ 2 < 1755625 / 1000000 := by
  obtain ⟨h1, h2⟩ := plastic_bounds hρ
  constructor <;> nlinarith

/-- `s = √(3ρ² − 4)`, twice the imaginary part of the complex root. -/
noncomputable def s (ρ : ℝ) : ℝ := Real.sqrt (3 * ρ ^ 2 - 4)

/-- The complex root `z = (−ρ + i√(3ρ² − 4))/2` of `x³ − x − 1`. -/
noncomputable def z (ρ : ℝ) : ℂ := ⟨-ρ / 2, s ρ / 2⟩

lemma s_sq : s ρ ^ 2 = 3 * ρ ^ 2 - 4 := by
  have := (rho_sq_bounds hρ).1
  exact Real.sq_sqrt (by linarith)

omit hρ in
lemma z_add_conj : z ρ + conj (z ρ) = -(ρ : ℂ) := by
  rw [Complex.add_conj, show (z ρ).re = -ρ / 2 from rfl]
  push_cast
  ring

lemma normSq_z : Complex.normSq (z ρ) = ρ ^ 2 - 1 := by
  rw [Complex.normSq_apply, show (z ρ).re = -ρ / 2 from rfl, show (z ρ).im = s ρ / 2 from rfl]
  have hs := s_sq hρ
  linear_combination (1 / 4 : ℝ) * hs

lemma z_mul_conj : z ρ * conj (z ρ) = (ρ : ℂ) ^ 2 - 1 := by
  rw [Complex.mul_conj, normSq_z hρ]
  push_cast
  ring

lemma norm_z_sq : ‖z ρ‖ ^ 2 = ρ ^ 2 - 1 := by
  rw [Complex.sq_norm, normSq_z hρ]

lemma norm_z_lt_one : ‖z ρ‖ < 1 := by
  have h := norm_z_sq hρ
  have := (rho_sq_bounds hρ).2
  nlinarith [norm_nonneg (z ρ)]

/-- The Perrin numbers are the power sums of the three roots (three consecutive values). -/
lemma perrin_eq_aux (n : ℕ) :
    ((perrin n : ℤ) : ℂ) = (ρ : ℂ) ^ n + z ρ ^ n + conj (z ρ) ^ n ∧
    ((perrin (n + 1) : ℤ) : ℂ) = (ρ : ℂ) ^ (n + 1) + z ρ ^ (n + 1) + conj (z ρ) ^ (n + 1) ∧
    ((perrin (n + 2) : ℤ) : ℂ) = (ρ : ℂ) ^ (n + 2) + z ρ ^ (n + 2) + conj (z ρ) ^ (n + 2) := by
  have hρC : (ρ : ℂ) ^ 3 = ρ + 1 := by exact_mod_cast hρ
  have hsum := z_add_conj (ρ := ρ)
  have hprod := z_mul_conj hρ
  have hz3 : z ρ ^ 3 = z ρ + 1 := by
    linear_combination (z ρ ^ 2 - ρ * z ρ) * hsum - (z ρ - ρ) * hprod + hρC
  have hw3 : conj (z ρ) ^ 3 = conj (z ρ) + 1 := by
    linear_combination (conj (z ρ) ^ 2 - ρ * conj (z ρ)) * hsum - (conj (z ρ) - ρ) * hprod + hρC
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · norm_num [perrin]
    · norm_num [perrin]
      linear_combination -hsum
    · norm_num [perrin]
      linear_combination (ρ - conj (z ρ) - z ρ) * hsum + 2 * hprod
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show ((perrin (n + 3) : ℤ) : ℂ) = (ρ : ℂ) ^ (n + 3) + z ρ ^ (n + 3) + conj (z ρ) ^ (n + 3)
    rw [perrin]
    push_cast
    rw [h0, h1]
    linear_combination (-(ρ : ℂ) ^ n) * hρC + (-(z ρ ^ n)) * hz3 + (-(conj (z ρ) ^ n)) * hw3

/-- `tₙ = P(n) − ρⁿ`, the integer-centred remainder of `ρⁿ`. -/
noncomputable def t (ρ : ℝ) (n : ℕ) : ℝ := (perrin n : ℝ) - ρ ^ n

lemma t_eq (n : ℕ) : ((t ρ n : ℝ) : ℂ) = z ρ ^ n + conj (z ρ) ^ n := by
  unfold t
  push_cast
  rw [(perrin_eq_aux hρ n).1]
  ring

lemma abs_t_le (n : ℕ) : |t ρ n| ≤ 2 * ‖z ρ‖ ^ n := by
  have h := t_eq hρ n
  have e : ‖((t ρ n : ℝ) : ℂ)‖ = |t ρ n| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [← e, h]
  calc ‖z ρ ^ n + conj (z ρ) ^ n‖ ≤ ‖z ρ ^ n‖ + ‖conj (z ρ) ^ n‖ := norm_add_le _ _
    _ = 2 * ‖z ρ‖ ^ n := by rw [norm_pow, norm_pow, Complex.norm_conj]; ring

lemma abs_t_lt_half {n : ℕ} (hn : 10 ≤ n) : |t ρ n| < 1 / 2 := by
  have h1 := abs_t_le hρ n
  have hz := norm_z_lt_one hρ
  have h2 : ‖z ρ‖ ^ n ≤ ‖z ρ‖ ^ 10 := pow_le_pow_of_le_one (norm_nonneg _) hz.le hn
  have h3 : ‖z ρ‖ ^ 10 = (ρ ^ 2 - 1) ^ 5 := by rw [← norm_z_sq hρ]; ring
  have hu : (ρ ^ 2 - 1) * ρ = 1 := by linear_combination hρ
  have h5 : (ρ ^ 2 - 1) ^ 5 * ρ ^ 5 = 1 := by rw [← mul_pow, hu, one_pow]
  have hρ5 : ρ ^ 5 = ρ ^ 2 + ρ + 1 := by linear_combination (ρ ^ 2 + 1) * hρ
  have hb := (rho_sq_bounds hρ).1
  have hb' := (plastic_bounds hρ).1
  have h4 : 4 < ρ ^ 5 := by rw [hρ5]; linarith
  have hpos : 0 < (ρ ^ 2 - 1) ^ 5 := pow_pos (by linarith) 5
  have h6 := mul_lt_mul_of_pos_left h4 hpos
  linarith

/-- For `n ≥ 10`, `‖ρⁿ‖² = tₙ²`. -/
lemma distInt_sq_tail {n : ℕ} (hn : 10 ≤ n) : distInt (ρ ^ n) ^ 2 = t ρ n ^ 2 := by
  have h := abs_t_lt_half hρ hn
  rw [abs_lt] at h
  have e : ρ ^ n = (perrin n : ℝ) - t ρ n := by unfold t; ring
  rw [distInt_eq_of_round (ρ ^ n) (perrin n) (by rw [e]; linarith) (by rw [e]; linarith), e,
    sq_abs]
  ring

/-- The geometric part: `∑_{n ≥ 1} tₙ² = 2ρ² + 3ρ − 2`. -/
lemma hasSum_t_sq : HasSum (fun n : ℕ => t ρ (n + 1) ^ 2) (2 * ρ ^ 2 + 3 * ρ - 2) := by
  have hρC : (ρ : ℂ) ^ 3 = ρ + 1 := by exact_mod_cast hρ
  have hsum := z_add_conj (ρ := ρ)
  have hprod := z_mul_conj hρ
  have hz1 : ‖z ρ‖ < 1 := norm_z_lt_one hρ
  have hw1 : ‖conj (z ρ)‖ < 1 := by rw [Complex.norm_conj]; exact hz1
  have ha : ‖z ρ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg (z ρ)]
  have hb : ‖conj (z ρ) ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg (conj (z ρ))]
  have hc : ‖z ρ * conj (z ρ)‖ < 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg (z ρ), norm_nonneg (conj (z ρ))]
  have g1 := (hasSum_geometric_of_norm_lt_one ha).mul_left (z ρ ^ 2)
  have g2 := (hasSum_geometric_of_norm_lt_one hb).mul_left (conj (z ρ) ^ 2)
  have g3 := (hasSum_geometric_of_norm_lt_one hc).mul_left (2 * (z ρ * conj (z ρ)))
  have h := (g1.add g2).add g3
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext n
    push_cast
    rw [t_eq hρ (n + 1)]
    ring
  · have h1 : (1 : ℂ) - z ρ ^ 2 ≠ 0 := by
      intro h
      rw [← sub_eq_zero.1 h, norm_one] at ha
      exact lt_irrefl _ ha
    have h2 : (1 : ℂ) - conj (z ρ) ^ 2 ≠ 0 := by
      intro h
      rw [← sub_eq_zero.1 h, norm_one] at hb
      exact lt_irrefl _ hb
    have h3 : (1 : ℂ) - z ρ * conj (z ρ) ≠ 0 := by
      intro h
      rw [← sub_eq_zero.1 h, norm_one] at hc
      exact lt_irrefl _ hc
    have hA : z ρ ^ 2 + conj (z ρ) ^ 2 = 2 - (ρ : ℂ) ^ 2 := by
      linear_combination (z ρ + conj (z ρ) - ρ) * hsum - 2 * hprod
    have hB : z ρ ^ 2 * conj (z ρ) ^ 2 = ((ρ : ℂ) ^ 2 - 1) ^ 2 := by
      linear_combination (z ρ * conj (z ρ) + ρ ^ 2 - 1) * hprod
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_add_div _ _ h1 h2,
      div_add_div _ _ (mul_ne_zero h1 h2) h3, eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) h3)]
    push_cast
    linear_combination
      (-(-2 * (ρ : ℂ) ^ 2 * conj (z ρ) * z ρ + 2 * (ρ : ℂ) ^ 2 - 3 * (ρ : ℂ) * conj (z ρ) * z ρ
        + 3 * (ρ : ℂ) - conj (z ρ) * z ρ - 1)) * hA
      + (-(2 * (ρ : ℂ) ^ 2 * conj (z ρ) * z ρ - 2 * (ρ : ℂ) ^ 2 + 3 * (ρ : ℂ) * conj (z ρ) * z ρ
        - 3 * (ρ : ℂ) + 2 * conj (z ρ) * z ρ)) * hB
      + (-(2 * (ρ : ℂ) ^ 6 + 3 * (ρ : ℂ) ^ 5 - 3 * (ρ : ℂ) ^ 3 - 3 * (ρ : ℂ) ^ 2)) * hprod
      + (-(2 * (ρ : ℂ) ^ 5 + 3 * (ρ : ℂ) ^ 4 - 2 * (ρ : ℂ) ^ 3 - 4 * (ρ : ℂ) ^ 2)) * hρC

/-- The finite correction over `1 ≤ n ≤ 9`: `∑ (‖ρⁿ‖² − tₙ²) = 2 − 2ρ − 2ρ²`. -/
lemma finite_correction :
    ∑ n ∈ range 9, (distInt (ρ ^ (n + 1)) ^ 2 - t ρ (n + 1) ^ 2) = 2 - 2 * ρ - 2 * ρ ^ 2 := by
  obtain ⟨hlo, hhi⟩ := plastic_bounds hρ
  obtain ⟨hlo2, hhi2⟩ := rho_sq_bounds hρ
  have e4 : ρ ^ 4 = ρ ^ 2 + ρ := by linear_combination ρ * hρ
  have e5 : ρ ^ 5 = ρ ^ 2 + ρ + 1 := by linear_combination (ρ ^ 2 + 1) * hρ
  have e6 : ρ ^ 6 = ρ ^ 2 + 2 * ρ + 1 := by linear_combination (ρ ^ 3 + ρ + 1) * hρ
  have e7 : ρ ^ 7 = 2 * ρ ^ 2 + 2 * ρ + 1 := by
    linear_combination (ρ ^ 4 + ρ ^ 2 + ρ + 1) * hρ
  have e8 : ρ ^ 8 = 2 * ρ ^ 2 + 3 * ρ + 2 := by
    linear_combination (ρ ^ 5 + ρ ^ 3 + ρ ^ 2 + ρ + 2) * hρ
  have e9 : ρ ^ 9 = 3 * ρ ^ 2 + 4 * ρ + 2 := by
    linear_combination (ρ ^ 6 + ρ ^ 4 + ρ ^ 3 + ρ ^ 2 + 2 * ρ + 2) * hρ
  have d1 : distInt (ρ ^ 1) = |ρ ^ 1 - ((1 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 1 (by rw [pow_one]; push_cast; linarith)
      (by rw [pow_one]; push_cast; linarith)
  have d2 : distInt (ρ ^ 2) = |ρ ^ 2 - ((2 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 2 (by push_cast; linarith) (by push_cast; linarith)
  have d3 : distInt (ρ ^ 3) = |ρ ^ 3 - ((2 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 2 (by rw [hρ]; push_cast; linarith) (by rw [hρ]; push_cast; linarith)
  have d4 : distInt (ρ ^ 4) = |ρ ^ 4 - ((3 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 3 (by rw [e4]; push_cast; linarith) (by rw [e4]; push_cast; linarith)
  have d5 : distInt (ρ ^ 5) = |ρ ^ 5 - ((4 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 4 (by rw [e5]; push_cast; linarith) (by rw [e5]; push_cast; linarith)
  have d6 : distInt (ρ ^ 6) = |ρ ^ 6 - ((5 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 5 (by rw [e6]; push_cast; linarith) (by rw [e6]; push_cast; linarith)
  have d7 : distInt (ρ ^ 7) = |ρ ^ 7 - ((7 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 7 (by rw [e7]; push_cast; linarith) (by rw [e7]; push_cast; linarith)
  have d8 : distInt (ρ ^ 8) = |ρ ^ 8 - ((9 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 9 (by rw [e8]; push_cast; linarith) (by rw [e8]; push_cast; linarith)
  have d9 : distInt (ρ ^ 9) = |ρ ^ 9 - ((13 : ℤ) : ℝ)| :=
    distInt_eq_of_round _ 13 (by rw [e9]; push_cast; linarith) (by rw [e9]; push_cast; linarith)
  have p1 : perrin 1 = 0 := rfl
  have p2 : perrin 2 = 2 := rfl
  have p3 : perrin 3 = 3 := rfl
  have p4 : perrin 4 = 2 := rfl
  have p5 : perrin 5 = 5 := rfl
  have p6 : perrin 6 = 5 := rfl
  have p7 : perrin 7 = 7 := rfl
  have p8 : perrin 8 = 10 := rfl
  have p9 : perrin 9 = 12 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd]
  rw [d1, d2, d3, d4, d5, d6, d7, d8, d9]
  simp only [t, sq_abs, p1, p2, p3, p4, p5, p6, p7, p8, p9]
  push_cast
  linear_combination (-2 * ρ ^ 6 + 2 * ρ ^ 5 - 2 * ρ ^ 4 + 2 * ρ ^ 2 - 4 * ρ + 4) * hρ

/-- **The settling sum of the plastic number.** For any real root `ρ` of `x³ − x − 1`,
`∑_{n ≥ 1} ‖ρⁿ‖² = ρ`, where `‖x‖ = |x − round x|`. -/
theorem plastic_settling_sum_of_root :
    HasSum (fun n : ℕ => distInt (ρ ^ (n + 1)) ^ 2) ρ := by
  have hg := hasSum_t_sq hρ
  have hd : HasSum (fun n : ℕ => distInt (ρ ^ (n + 1)) ^ 2 - t ρ (n + 1) ^ 2)
      (2 - 2 * ρ - 2 * ρ ^ 2) := by
    rw [← finite_correction hρ]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [distInt_sq_tail hρ (by omega)]
    ring
  have := hg.add hd
  convert this using 1
  · funext n; ring
  · ring

end Root

/-- `x³ = x + 1` has exactly one real solution. -/
theorem existsUnique_root : ∃! x : ℝ, x ^ 3 = x + 1 := by
  have hc : ContinuousOn (fun y : ℝ => y ^ 3 - y - 1) (Set.Icc 1 2) := by fun_prop
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hc
    (show (0:ℝ) ∈ Set.Icc ((1:ℝ) ^ 3 - 1 - 1) ((2:ℝ) ^ 3 - 2 - 1) by norm_num)
  have hx' : x ^ 3 = x + 1 := by simp only at hx; linarith
  refine ⟨x, hx', fun y hy => ?_⟩
  obtain ⟨hx1, -⟩ := plastic_bounds hx'
  obtain ⟨hy1, -⟩ := plastic_bounds hy
  have : (y - x) * (y ^ 2 + y * x + x ^ 2 - 1) = 0 := by linear_combination hy - hx'
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · nlinarith

/-- The plastic number `ρ`, the real root of `x³ − x − 1`. -/
noncomputable def plastic : ℝ := Classical.choose existsUnique_root.exists

theorem plastic_spec : plastic ^ 3 = plastic + 1 := Classical.choose_spec existsUnique_root.exists

/-- **The settling sum of the plastic number**: `∑_{n ≥ 1} ‖ρⁿ‖² = ρ`. -/
theorem plastic_settling_sum :
    HasSum (fun n : ℕ => distInt (plastic ^ (n + 1)) ^ 2) plastic :=
  plastic_settling_sum_of_root plastic_spec

theorem plastic_tsum : ∑' n : ℕ, distInt (plastic ^ (n + 1)) ^ 2 = plastic :=
  plastic_settling_sum.tsum_eq

end PisotSum
