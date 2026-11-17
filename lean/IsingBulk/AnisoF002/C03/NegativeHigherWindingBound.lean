import IsingBulk.AnisoF002.C03.NegativeHigherWindingScalar

/-!
# Complete actual higher-winding suppression

Every odd winding other than plus/minus one is included.  All constants
are constructed from the original local physical data before the
particle number and derivative order.  The comparison is with the
literal frozen model and the same complete physical sector coefficients.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology BigOperators Classical

def higherWindingSectorIndices (n : ℕ) : Finset ℤ :=
  (windingSectorIndices n).filter (fun w => w ≠ 1 ∧ w ≠ -1)

theorem higherWindingSectorIndices_subset (n : ℕ) :
    higherWindingSectorIndices n ⊆ windingSectorIndices n := Finset.filter_subset _ _

theorem higherWindingSectorIndices_abs_ge_three {n : ℕ} {w : ℤ}
    (hw : w ∈ higherWindingSectorIndices n) : (3 : ℝ) ≤ |(w : ℝ)| := by
  obtain ⟨hwS, hw1, hwneg⟩ := Finset.mem_filter.mp hw
  obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hwS).2
  have hwa : (3 : ℤ) ≤ |w| := by
    have hpos := le_abs_self w
    have hneg := neg_le_abs w
    omega
  exact_mod_cast hwa

theorem higherWindingSectorIndices_card_le (n : ℕ) :
    (higherWindingSectorIndices n).card ≤ 2 * (n + 1) + 1 :=
  (Finset.card_le_card (higherWindingSectorIndices_subset n)).trans (windingSectorIndices_card_le n)

theorem eventually_actual_winding_model_factors {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hBi : (B 0).im < 0) (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ U : ℝ, 0 < U ∧ ∀ᶠ N : ℕ in atTop,
      ‖b (windingTau N : ℂ)‖ ≤ U ∧
      ‖b 0‖ / ‖b (windingTau N : ℂ)‖ ≤ 2 ∧
      B (windingTau N : ℂ) ≠ 0 ∧
      0 < (firstWindingCurvature N (B (windingTau N : ℂ)) (Real.cos φ) (Real.sin φ)).re ∧
      ‖firstWindingCurvature N (B (windingTau N : ℂ)) (Real.cos φ) (Real.sin φ)‖ ≤ 2 := by
  have hb0 : b 0 ≠ 0 := by
    intro he
    have h := hbsq 0
    rw [he, zero_pow two_ne_zero] at h
    rw [← h, Complex.zero_im] at hBi
    exact (lt_irrefl 0) hBi
  have hbn0 : 0 < ‖b 0‖ := norm_pos_iff.mpr hb0
  let U := ‖b 0‖ + 1
  have hU : 0 < U := by dsimp [U]; positivity
  refine ⟨U, hU, ?_⟩
  have hbseq := (tendsto_anisotropy_at_centers b hb.continuousAt).norm
  have hc := tendsto_firstWindingCurvature_one B hB.continuousAt (Real.cos φ) (Real.sin φ)
  have hcre := (Complex.continuous_re.tendsto 1).comp hc
  filter_upwards [hbseq.eventually (Ioi_mem_nhds (half_lt_self hbn0)),
    hbseq.eventually (Iio_mem_nhds (show ‖b 0‖ < U by dsimp [U]; linarith)),
    hcre.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re)),
    hc.norm.eventually (Iio_mem_nhds (by norm_num : ‖(1 : ℂ)‖ < (2 : ℝ)))] with N hlo hhi hre hnorm
  have hbNp : 0 < ‖b (windingTau N : ℂ)‖ := (half_pos hbn0).trans hlo
  refine ⟨hhi.le, (div_le_iff₀ hbNp).mpr (by linarith), ?_, hre, hnorm.le⟩
  rw [← hbsq]
  exact pow_ne_zero 2 (norm_pos_iff.mp hbNp)

namespace PhysicalWindingResidueControl
variable {b B : ℂ → ℂ} {φ : ℝ} (c : PhysicalWindingResidueControl b B φ)

theorem all_higher_sector_model_bound {l : ℕ} (hl : 0 < l) (m : ℕ)
    {r s Mi ki U : ℝ} (d : InnerRemainderFamily b B φ (2 * l + 1) r s Mi ki)
    (hs : 0 < s) (hsc : s ≤ c.cutoff) (hr : r / (4 * (2 * l + 1 : ℕ)) ≤ c.radius)
    (hU : 0 < U) (hbU : ‖b (windingTau (2 * l + 1) : ℂ)‖ ≤ U)
    (hbD : ‖b 0‖ / ‖b (windingTau (2 * l + 1) : ℂ)‖ ≤ 2)
    (hB : B (windingTau (2 * l + 1) : ℂ) ≠ 0)
    (hbsq : b (windingTau (2 * l + 1) : ℂ) ^ 2 = B (windingTau (2 * l + 1) : ℂ))
    (hh : 0 < (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re)
    (hhup : ‖firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)‖ ≤ 2) (hφ : 0 < φ) (hπ : φ < Real.pi) :
    let j := 2 * l * (l + 1) + m
    let model := modelCoefficient (2 * l + 1) j (B (windingTau (2 * l + 1) : ℂ))
      (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))
    (∑ w ∈ higherWindingSectorIndices (2 * l), ‖physicalWindingSectorCoefficient d j w‖) ≤
      ‖model‖ * Real.exp ((U ^ 2 / (2 * c.A * Real.sin φ) + c.C + 10) *
        ((2 * l + 1 : ℕ) : ℝ) ^ 2) * (2 / 9 : ℝ) ^ (m + 1) := by
  dsimp only
  let j := 2 * l * (l + 1) + m
  let model := modelCoefficient (2 * l + 1) j (B (windingTau (2 * l + 1) : ℂ))
    (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))
  let K := U ^ 2 / (2 * c.A * Real.sin φ)
  have hsφ := Real.sin_pos_of_pos_of_lt_pi hφ hπ
  have hA := c.A_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hα : 2 * l * (l + 1) ≤ (2 * l + 1) ^ 2 := by nlinarith
  have hsingle : ∀ w ∈ higherWindingSectorIndices (2 * l),
      ‖physicalWindingSectorCoefficient d j w‖ ≤ ‖model‖ * K *
        (2 : ℝ) ^ ((2 * l + 1) ^ 2) * Real.exp (c.C * ((2 * l + 1 : ℕ) : ℝ) * s) *
        (4 : ℝ) ^ (2 * l * (l + 1)) * (2 / 9 : ℝ) ^ (m + 1) := by
    intro w hw
    have hw3 := higherWindingSectorIndices_abs_ge_three hw
    have hw0 : w ≠ 0 := by intro he; norm_num [he] at hw3
    have htau := windingTau_pos (2 * l + 1) (by omega)
    have hbnd := (c.sector_coefficient_beta_bound d (by omega)
      (radialShape_even_dimension hl) (show 2 * l * (l + 1) < j + 1 by dsimp [j]; omega)
      hs hsc hr hw0).2
    have hmaj := c.beta_majorant_higher_bound hl m hsc htau
      (windingTau_bounds (2 * l + 1) (by omega)).2 hB hbsq hh hhup hbD hbU hφ hπ hw3
    dsimp [j] at hbnd ⊢
    simp only [Nat.add_sub_cancel_left,
      show 2 * l * (l + 1) + m + 1 - 2 * l * (l + 1) = m + 1 by omega] at hbnd
    exact hbnd.trans hmaj
  have hcount : ((higherWindingSectorIndices (2 * l)).card : ℝ) ≤
      2 * ((2 * l + 1 : ℕ) : ℝ) + 1 := by exact_mod_cast higherWindingSectorIndices_card_le (2 * l)
  have hscl := higher_winding_scalar_envelope hK c.C_pos.le (hsc.trans c.cutoff_le_one)
    (show 1 ≤ 2 * l + 1 by omega) hα
  change (∑ w ∈ higherWindingSectorIndices (2 * l), ‖physicalWindingSectorCoefficient d j w‖) ≤ _
  calc
    _ ≤ ∑ _w ∈ higherWindingSectorIndices (2 * l), ‖model‖ * K *
        (2 : ℝ) ^ ((2 * l + 1) ^ 2) * Real.exp (c.C * ((2 * l + 1 : ℕ) : ℝ) * s) *
        (4 : ℝ) ^ (2 * l * (l + 1)) * (2 / 9 : ℝ) ^ (m + 1) := Finset.sum_le_sum hsingle
    _ ≤ (2 * ((2 * l + 1 : ℕ) : ℝ) + 1) * (‖model‖ * K *
        (2 : ℝ) ^ ((2 * l + 1) ^ 2) * Real.exp (c.C * ((2 * l + 1 : ℕ) : ℝ) * s) *
        (4 : ℝ) ^ (2 * l * (l + 1)) * (2 / 9 : ℝ) ^ (m + 1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = ‖model‖ * ((2 * ((2 * l + 1 : ℕ) : ℝ) + 1) * K *
        (2 : ℝ) ^ ((2 * l + 1) ^ 2) * Real.exp (c.C * ((2 * l + 1 : ℕ) : ℝ) * s) *
        (4 : ℝ) ^ (2 * l * (l + 1))) * (2 / 9 : ℝ) ^ (m + 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscl (norm_nonneg model)) (by positivity)

theorem exists_actual_complete_higher_winding_bound
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ M : ℝ, 1 < M ∧ ∀ᶠ l : ℕ in atTop,
      ∀ r s Mi ki : ℝ, ∀ d : InnerRemainderFamily b B φ (2 * l + 1) r s Mi ki,
      0 < s → s ≤ c.cutoff → r / (4 * (2 * l + 1 : ℕ)) ≤ c.radius → ∀ j : ℕ,
      M * ((2 * l + 1 : ℕ) : ℝ) ^ 2 ≤ (j : ℝ) →
      (∑ w ∈ higherWindingSectorIndices (2 * l), ‖physicalWindingSectorCoefficient d j w‖) ≤
        ‖modelCoefficient (2 * l + 1) j (B (windingTau (2 * l + 1) : ℂ))
          (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
            (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))‖ / 32 := by
  obtain ⟨U, hU, hf⟩ := eventually_actual_winding_model_factors (φ := φ) hb hB hBi hbsq
  let D := U ^ 2 / (2 * c.A * Real.sin φ) + c.C + 10
  have hD : 0 < D := by
    have hA := c.A_pos
    have hC := c.C_pos
    have hsφ := Real.sin_pos_of_pos_of_lt_pi hφ hπ
    dsimp [D]
    positivity
  obtain ⟨M, hM, hwindow⟩ := exists_higher_winding_scalar_window hD
  have ht : Tendsto (fun l : ℕ => 2 * l + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    exact eventually_atTop.mpr ⟨n, fun l hl => by omega⟩
  refine ⟨M, hM, ?_⟩
  filter_upwards [ht.eventually hf, eventually_gt_atTop (0 : ℕ)] with l hlf hl
  intro r s Mi ki d hs hsc hr j hj
  have hα : 2 * l * (l + 1) ≤ (2 * l + 1) ^ 2 := by nlinarith
  have hNj : (((2 * l + 1 : ℕ) : ℝ)) ^ 2 ≤ (j : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hM.le (sq_nonneg (((2 * l + 1 : ℕ) : ℝ)))
    simp only [one_mul] at hh
    exact hh.trans hj
  have hαj : 2 * l * (l + 1) ≤ j := by
    have hαR : ((2 * l * (l + 1) : ℕ) : ℝ) ≤ ((2 * l + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hα
    exact_mod_cast hαR.trans hNj
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hαj
  have hbnd := c.all_higher_sector_model_bound hl m d hs hsc hr hU
    hlf.1 hlf.2.1 hlf.2.2.1 (hbsq _) hlf.2.2.2.1 hlf.2.2.2.2 hφ hπ
  dsimp only at hbnd
  apply hbnd.trans
  have hsmall := hwindow (2 * l + 1) (2 * l * (l + 1)) m (by omega) hα hj
  simpa only [D, mul_assoc, mul_one_div] using mul_le_mul_of_nonneg_left hsmall
    (norm_nonneg (modelCoefficient (2 * l + 1) (2 * l * (l + 1) + m)
      (B (windingTau (2 * l + 1) : ℂ))
      (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))))

end PhysicalWindingResidueControl
end
end IsingBulk.AnisoF002.NegativeHT
