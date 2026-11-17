import IsingBulk.AnisoF002.C03.RegularWindingFirstAttachment

/-!
# Uniform physical attachment of the first winding pair

Every local analytic and pole-smallness condition in the literal residue
identity is discharged from the actual phase and the constructed uniform
first-winding data.  The cutoff is fixed before N; its exact integration
radius is allowed to vary with N and stays above sqrt(s/2).
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem windingCutRadius_bounds {n : ℕ} {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ)
    (hsσ : s < σ ^ 2) (hN : Real.pi ^ 2 / (n + 1 : ℕ) ≤ s / 2) :
    Real.sqrt (s / 2) ≤ firstWindingCutRadius n s ∧ firstWindingCutRadius n s < σ := by
  have hc : 0 ≤ Real.pi ^ 2 / ((n + 1 : ℕ) : ℝ) := by positivity
  have hrad : 0 ≤ s - Real.pi ^ 2 / ((n + 1 : ℕ) : ℝ) := by linarith
  unfold firstWindingCutRadius
  constructor
  · exact Real.sqrt_le_sqrt (by linarith)
  · have hh := Real.sq_sqrt hrad
    nlinarith [Real.sqrt_nonneg (s - Real.pi ^ 2 / ((n + 1 : ℕ) : ℝ))]

set_option maxHeartbeats 1000000 in
theorem exists_uniform_first_winding_sector_attachment {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ σ C Kρ Kp s : ℝ,
      0 < σ → 0 ≤ C → 0 < s → s ≤ s0 → s < σ ^ 2 →
      ∀ (b : ℂ → ℂ) (r M kappa : ℝ), ∀ᶠ n : ℕ in atTop,
        ∀ d : InnerRemainderFamily b B φ (n + 1) r s M kappa,
        ∀ p : PhysicalFirstWindingData b B φ (n + 1) σ C Kρ Kp,
          Real.sqrt (s / 2) ≤ firstWindingCutRadius n s ∧ firstWindingCutRadius n s < σ ∧
          ∀ j : ℕ,
            physicalWindingSectorCoefficient d j 1 =
              p.physicalResidueIntegral (j + 1) (firstWindingCutRadius n s) ∧
            physicalWindingSectorCoefficient d j (-1) =
              p.physicalResidueIntegral (j + 1) (firstWindingCutRadius n s) ∧
            physicalWindingSectorCoefficient d j 1 + physicalWindingSectorCoefficient d j (-1) =
              2 * p.physicalResidueIntegral (j + 1) (firstWindingCutRadius n s) := by
  obtain ⟨Ru, su, hRu, hsu, hu⟩ := exists_actual_phase_unique_ball hB hφ hπ hBi
  have hga := negativeGlobalPhase_analyticAt_zero hB hφ hπ
  obtain ⟨ρ, hρ, hgaρ⟩ := Metric.eventually_nhds_iff.mp hga.eventually_analyticAt
  let R : ℝ := min Ru (ρ / 2)
  let s0 : ℝ := min su (ρ ^ 2 / 4)
  have hR : 0 < R := lt_min hRu (half_pos hρ)
  have hs0 : 0 < s0 := lt_min hsu (by positivity)
  refine ⟨s0, hs0, ?_⟩
  intro σ C Kρ Kp s hσ hC hs hss0 hsσ b r M kappa
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hτ : Tendsto (fun n : ℕ => ‖(windingTau n : ℂ)‖) atTop (𝓝 (0 : ℝ)) := by
    have hh := (continuous_fst.continuousAt : ContinuousAt (fun p : ℂ × ℂ => p.1) (0, 0)).tendsto.comp
      tendsto_complex_winding_centers
    simpa only [Function.comp_def, norm_zero] using hh.norm
  have hsum : Tendsto (fun n : ℕ => ‖(windingTau n : ℂ)‖ + C * s / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using hτ.add (tendsto_const_div_atTop_nhds_zero_nat (C * s))
  have hlateT : ∀ᶠ n : ℕ in atTop, ‖(windingTau (n + 1) : ℂ)‖ + C * s / (n + 1 : ℕ) ≤ R :=
    hsucc.eventually (hsum.eventually (eventually_le_nhds hR))
  have hlateR : ∀ᶠ n : ℕ in atTop, r / (4 * (n + 1 : ℕ)) ≤ R := by
    have hh := hsucc.eventually
      ((tendsto_const_div_atTop_nhds_zero_nat (r / 4)).eventually (eventually_le_nhds hR))
    convert hh using 1
    ext n
    ring
  have hlateCut : ∀ᶠ n : ℕ in atTop, Real.pi ^ 2 / (n + 1 : ℕ) ≤ s / 2 :=
    hsucc.eventually ((tendsto_const_div_atTop_nhds_zero_nat (Real.pi ^ 2)).eventually
      (eventually_le_nhds (half_pos hs)))
  filter_upwards [hlateT, hlateR, hlateCut] with n hnT hnR hnCut
  intro d p
  have hssu : s ≤ su := hss0.trans (min_le_left _ _)
  have hsρ : s ≤ ρ ^ 2 / 4 := hss0.trans (min_le_right _ _)
  have hrRu : r / (4 * (n + 1 : ℕ)) ≤ Ru := hnR.trans (min_le_left _ _)
  have hQ (v : constrainedPlane n) (hv : ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s) :
      displacementSquare (n + 1) (complexPlaneEmbedding v) < σ ^ 2 := by
    rw [complexPlaneEmbedding_square]
    have hc : 0 ≤ Real.pi ^ 2 / ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hpR (v : constrainedPlane n) (hv : ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s) :
      ‖p.pole (complexPlaneEmbedding v)‖ ≤ R := by
    have hc : 0 ≤ Real.pi ^ 2 / ((n + 1 : ℕ) : ℝ) := by positivity
    have hvs : ‖v‖ ^ 2 ≤ s := by linarith
    have hbnd := p.pole_coarse (complexPlaneEmbedding v) (hQ v hv)
    rw [complexPlaneEmbedding_square] at hbnd
    calc
      _ ≤ ‖p.pole (complexPlaneEmbedding v) - (windingTau (n + 1) : ℂ)‖ +
          ‖(windingTau (n + 1) : ℂ)‖ := norm_le_norm_sub_add _ _
      _ ≤ C * ‖v‖ ^ 2 / (n + 1 : ℕ) + ‖(windingTau (n + 1) : ℂ)‖ :=
        add_le_add hbnd le_rfl
      _ ≤ C * s / (n + 1 : ℕ) + ‖(windingTau (n + 1) : ℂ)‖ :=
        add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvs hC) (by positivity)) le_rfl
      _ ≤ R := by linarith
  have hg (v : constrainedPlane n) (hv : ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s) (i : Fin (n + 1)) :
      DifferentiableAt ℂ (negativeGlobalPhase B φ)
        (p.pole (complexPlaneEmbedding v),
          ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) + (complexPlaneEmbedding v : Fin (n + 1) → ℂ) i) := by
    have hi : centeredWindingAngles 1 v i ^ 2 ≤ s := by
      have hh := Finset.single_le_sum (fun j _ => sq_nonneg (centeredWindingAngles 1 v j)) (Finset.mem_univ i)
      rw [centeredWindingAngles_square] at hh
      simp only [Int.cast_one, one_pow, one_mul] at hh
      exact hh.trans hv
    have hqi : |centeredWindingAngles 1 v i| < ρ := by
      have hsqr := sq_abs (centeredWindingAngles 1 v i)
      nlinarith [abs_nonneg (centeredWindingAngles 1 v i)]
    have htρ : ‖p.pole (complexPlaneEmbedding v)‖ < ρ :=
      ((hpR v hv).trans (min_le_right _ _)).trans_lt (by linarith)
    have hpair : dist (p.pole (complexPlaneEmbedding v), (centeredWindingAngles 1 v i : ℂ)) (0, 0) < ρ := by
      simpa only [Prod.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using
        max_lt_iff.mpr ⟨htρ, hqi⟩
    rw [← centeredWindingAngles_one_cast]
    exact (hgaρ hpair).differentiableAt
  have hrad := windingCutRadius_bounds hs hσ hsσ hnCut
  refine ⟨hrad.1, hrad.2, ?_⟩
  intro j
  have hfirst := physicalWindingSectorCoefficient_first d p hu hrRu hssu hsσ
    (hnCut.trans (by linarith))
    (fun v hv => (hpR v hv).trans (min_le_left _ _)) hg j
  have hminus : physicalWindingSectorCoefficient d j (-1) =
      p.physicalResidueIntegral (j + 1) (firstWindingCutRadius n s) := by
    rw [physicalWindingSectorCoefficient_neg_winding d hu hrRu hssu j 1, hfirst]
  refine ⟨hfirst, hminus, ?_⟩
  rw [hfirst, hminus]
  ring

end
end IsingBulk.AnisoF002.NegativeHT
