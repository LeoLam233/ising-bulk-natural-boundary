import IsingBulk.AnisoF002.C03.NegativeWindingModelNormalization

/-!
# Every higher-winding Beta majorant relative to the exact model

The leading temperature scale remains exact.  In particular the power
in the winding number is retained before any particle-window estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology BigOperators

theorem winding_beta_normalization_algebra (α k : ℕ)
    {N a A s h τ μ : ℝ} (hN : N ≠ 0) (ha : a ≠ 0) (hA : A ≠ 0)
    (hs : s ≠ 0) (hh : h ≠ 0) (hτ : τ ≠ 0) (hμ : μ ≠ 0)
    (u D R E G F J : ℝ) :
    (2 * (N / (2 * s) * u ^ 2 * D * R) * E / (A * N)) *
        (N / a) ^ (α + k) * (G * F / (J * μ ^ k)) =
      (2 * R * (G * F / (J * (h / (2 * N)) ^ α * τ ^ k))) *
        (u ^ 2 / (2 * A * s)) * D * E * (h / (2 * a)) ^ α *
        (N * τ / (a * μ)) ^ k := by
  simp only [pow_add, div_pow, mul_pow]
  field_simp

namespace PhysicalWindingResidueControl
variable {b B : ℂ → ℂ} {φ : ℝ} (c : PhysicalWindingResidueControl b B φ)

theorem beta_majorant_model_identity {l : ℕ} (hl : 0 < l) (m : ℕ)
    {s τ : ℝ} (hsc : s ≤ c.cutoff) (hτ : 0 < τ)
    {b1 B1 h : ℂ} (hB1 : B1 ≠ 0) (hb1 : b1 ^ 2 = B1) (hh : 0 < h.re)
    (hφ : 0 < φ) (hπ : φ < Real.pi) {w : ℤ} (hw : w ≠ 0) :
    c.sectorFactor (2 * l) (2 * l * (l + 1) + m + 1) s *
        (constrainedGaussianIntegral (2 * l) * (m.factorial : ℝ) /
          (((2 * l * (l + 1) + m).factorial : ℝ) * windingMass (2 * l) w ^ (m + 1))) =
      ‖modelCoefficient (2 * l + 1) (2 * l * (l + 1) + m) B1 h (Real.sin φ) τ‖ *
        (‖b1‖ ^ 2 / (2 * c.A * Real.sin φ)) * (‖b 0‖ / ‖b1‖) ^ ((2 * l + 1) ^ 2) *
        Real.exp (c.C * ((2 * l + 1 : ℕ) : ℝ) * s) *
        (‖h‖ / (2 * (1 / 2 - c.K * s))) ^ (2 * l * (l + 1)) *
        (((2 * l + 1 : ℕ) : ℝ) * τ / ((1 / 2 - c.K * s) * windingMass (2 * l) w)) ^ (m + 1) := by
  have hsφ := Real.sin_pos_of_pos_of_lt_pi hφ hπ
  have hbne : b1 ≠ 0 := by
    intro he
    rw [he, zero_pow two_ne_zero] at hb1
    exact hB1 hb1.symm
  have hhn : 0 < ‖h‖ := hh.trans_le (Complex.re_le_norm h)
  rw [norm_modelCoefficient_center_period hl m hB1 hb1 hsφ hτ hh]
  unfold sectorFactor
  rw [allWindingCenterMagnitude_center_ratio (by omega : 2 ≤ 2 * l + 1)
    (b 0) b1 hbne hsφ φ rfl]
  convert winding_beta_normalization_algebra (2 * l * (l + 1)) (m + 1)
    (by positivity : (((2 * l + 1 : ℕ) : ℝ)) ≠ 0) (c.alpha_pos hsc).ne' c.A_pos.ne'
    hsφ.ne' hhn.ne' hτ.ne' (windingMass_pos (2 * l) hw).ne'
    ‖b1‖ ((‖b 0‖ / ‖b1‖) ^ ((2 * l + 1) ^ 2))
    ‖centerDensityScalar (2 * l + 1) b1 (Real.sin φ)‖
    (Real.exp (c.C * ((2 * l + 1 : ℕ) : ℝ) * s))
    (constrainedGaussianIntegral (2 * l)) (m.factorial : ℝ)
    ((2 * l * (l + 1) + m).factorial : ℝ) using 1

theorem winding_temperature_ratio_le {n : ℕ} {s : ℝ} (hsc : s ≤ c.cutoff)
    {τ : ℝ} (hτ : τ ≤ Real.pi ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2))
    {w : ℤ} (hw : w ≠ 0) :
    ((n + 1 : ℕ) : ℝ) * τ / ((1 / 2 - c.K * s) * windingMass n w) ≤ 2 / (w : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hw2 : 0 < (w : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hw)
  have ha := c.alpha_pos hsc
  have ha4 : (1 / 4 : ℝ) ≤ 1 / 2 - c.K * s := by
    have hk := (mul_le_mul_of_nonneg_left hsc c.K_pos.le).trans c.K_cutoff
    linarith
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) * (Real.pi ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2)) /
        ((1 / 2 - c.K * s) * windingMass n w) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hN.le)
        (mul_pos ha (windingMass_pos n hw)).le
    _ ≤ ((n + 1 : ℕ) : ℝ) * (Real.pi ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2)) /
        ((1 / 4) * windingMass n w) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity [windingMass_pos n hw])
        (mul_le_mul_of_nonneg_right ha4 (windingMass_pos n hw).le)
    _ = _ := by unfold windingMass; field_simp; ring

theorem beta_majorant_higher_bound {l : ℕ} (hl : 0 < l) (m : ℕ)
    {s τ D U : ℝ} (hsc : s ≤ c.cutoff) (hτ : 0 < τ)
    (hτup : τ ≤ Real.pi ^ 2 / (2 * ((2 * l + 1 : ℕ) : ℝ) ^ 2))
    {b1 B1 h : ℂ} (hB1 : B1 ≠ 0) (hb1 : b1 ^ 2 = B1) (hh : 0 < h.re)
    (hhup : ‖h‖ ≤ 2) (hD : ‖b 0‖ / ‖b1‖ ≤ D) (hU : ‖b1‖ ≤ U)
    (hφ : 0 < φ) (hπ : φ < Real.pi) {w : ℤ} (hw : (3 : ℝ) ≤ |(w : ℝ)|) :
    c.sectorFactor (2 * l) (2 * l * (l + 1) + m + 1) s *
        (constrainedGaussianIntegral (2 * l) * (m.factorial : ℝ) /
          (((2 * l * (l + 1) + m).factorial : ℝ) * windingMass (2 * l) w ^ (m + 1))) ≤
      ‖modelCoefficient (2 * l + 1) (2 * l * (l + 1) + m) B1 h (Real.sin φ) τ‖ *
        (U ^ 2 / (2 * c.A * Real.sin φ)) * D ^ ((2 * l + 1) ^ 2) *
        Real.exp (c.C * ((2 * l + 1 : ℕ) : ℝ) * s) *
        (4 : ℝ) ^ (2 * l * (l + 1)) * (2 / 9 : ℝ) ^ (m + 1) := by
  have hw0 : w ≠ 0 := by intro he; norm_num [he] at hw
  have hsφ := Real.sin_pos_of_pos_of_lt_pi hφ hπ
  have hDn : 0 ≤ D := (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans hD
  have hUn : 0 ≤ U := (norm_nonneg _).trans hU
  have ha := c.alpha_pos hsc
  have ha4 : (1 / 4 : ℝ) ≤ 1 / 2 - c.K * s := by
    have hk := (mul_le_mul_of_nonneg_left hsc c.K_pos.le).trans c.K_cutoff
    linarith
  have hh4 : ‖h‖ / (2 * (1 / 2 - c.K * s)) ≤ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 / 2 - c.K * s))).mpr
    linarith
  have hw9 : (9 : ℝ) ≤ (w : ℝ) ^ 2 := by nlinarith [sq_abs (w : ℝ)]
  have hmass : ((2 * l + 1 : ℕ) : ℝ) * τ /
      ((1 / 2 - c.K * s) * windingMass (2 * l) w) ≤ 2 / 9 :=
    (c.winding_temperature_ratio_le hsc hτup hw0).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw9)
  rw [c.beta_majorant_model_identity hl m hsc hτ hB1 hb1 hh hφ hπ hw0]
  have hA := c.A_pos
  have hm := windingMass_pos (2 * l) hw0
  gcongr

end PhysicalWindingResidueControl
end
end IsingBulk.AnisoF002.NegativeHT
