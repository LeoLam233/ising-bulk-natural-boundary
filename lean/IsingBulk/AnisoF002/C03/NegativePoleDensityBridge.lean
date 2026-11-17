import IsingBulk.AnisoF002.C03.NegativeUniformDensityLog

/-!
# One uniform moving pole and its complete analytic residue density

The pole and density constructions use the same phase and the same exact
winding centers.  Their radii are intersected once, before n.  This
provides the full density factorization on the genuine zero-sum plane,
with the coarse pole estimate and its nonzero phase derivative retained.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem zeroSumDisplacements_mem_ball_of_square_lt {n : ℕ}
    (v : zeroSumDisplacements n) {σ : ℝ} (hσ : 0 < σ)
    (hv : displacementSquare n (v : Fin n → ℂ) < σ ^ 2) :
    v ∈ Metric.ball 0 σ := by
  rw [Metric.mem_ball, dist_zero_right]
  change ‖(v : Fin n → ℂ)‖ < σ
  rw [pi_norm_lt_iff hσ]
  intro i
  have hi : ‖(v : Fin n → ℂ) i‖ ^ 2 ≤ displacementSquare n (v : Fin n → ℂ) :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖(v : Fin n → ℂ) j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg ((v : Fin n → ℂ) i)]

set_option maxHeartbeats 2000000 in
theorem exists_uniform_poles_and_complete_density {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {γ : ℂ}
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 ≠ 0)
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : phaseTemperatureDerivative g (0, 0) ≠ 0)
    (hcenter : ∀ δ : ℂ, g (1 - Complex.cos δ, δ) = γ)
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d))
    (hγ : Complex.sinh γ ≠ 0) :
    ∃ σ C K : ℝ, 0 < σ ∧ 0 < C ∧ 0 < K ∧
      ∀ᶠ n : ℕ in atTop, ∃ T ell : zeroSumDisplacements n → ℂ,
        AnalyticOnNhd ℂ T (Metric.ball 0 σ) ∧ T 0 = (windingTau n : ℂ) ∧
        ∀ v : zeroSumDisplacements n, displacementSquare n (v : Fin n → ℂ) < σ ^ 2 →
          (∑ i, g (T v, ((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i)) = (n : ℂ) * γ ∧
          ‖T v - (windingTau n : ℂ)‖ ≤ C * displacementSquare n (v : Fin n → ℂ) / (n : ℝ) ∧
          deriv (centeredPhaseAverage n g γ ((Real.pi / (n : ℝ) : ℝ) : ℂ)
            (v : Fin n → ℂ)) (T v) ≠ 0 ∧
          AnalyticAt ℂ ell v ∧
          filledNegativeDensityAt n b g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (windingTau n : ℂ) 0 ≠ 0 ∧
          -(2 * completeNegativeNumerator n b g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (T v) (v : Fin n → ℂ)) /
            phaseTemperatureSum n g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (T v) (v : Fin n → ℂ) =
            filledNegativeDensityAt n b g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (windingTau n : ℂ) 0 *
              complexVandermondeSquared n (v : Fin n → ℂ) * Complex.exp (ell v) ∧
          ‖ell v‖ ≤ K * (Real.sqrt ((n : ℝ) * displacementSquare n (v : Fin n → ℂ)) +
            (n : ℝ) * displacementSquare n (v : Fin n → ℂ)) := by
  obtain ⟨r, σp, C, hr, hσp, hC, hPoles⟩ := exists_uniform_analytic_zero_sum_poles hg hc
  have hg0 : g (0, 0) = γ := by simpa using hcenter 0
  obtain ⟨L, σd, K, hσd, hK, hDensity⟩ :=
    exists_uniform_complete_density_log hb hb0 hg hg0 hc heven hγ hC
  let σ : ℝ := min σp σd
  have hσ : 0 < σ := lt_min hσp hσd
  have hσp' : σ ≤ σp := min_le_left _ _
  have hσd' : σ ≤ σd := min_le_right _ _
  have hN : ∀ᶠ n : ℕ in atTop,
      ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) ∈
        Metric.ball (0, 0) (min (r / 4) σd) :=
    tendsto_complex_winding_centers.eventually (Metric.ball_mem_nhds _
      (lt_min (by positivity) hσd))
  refine ⟨σ, C, K, hσ, hC, hK, ?_⟩
  filter_upwards [hN, eventually_gt_atTop (0 : ℕ)] with n hnball hn
  have hnorm : max ‖(windingTau n : ℂ)‖ ‖((Real.pi / (n : ℝ) : ℝ) : ℂ)‖ < min (r / 4) σd := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_def] using hnball
  have hτ := lt_of_le_of_lt (le_max_left _ _) hnorm
  have hd := lt_of_le_of_lt (le_max_right _ _) hnorm
  have hgcenter : g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) = γ := by
    simpa only [windingTau, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos]
      using hcenter ((Real.pi / (n : ℝ) : ℝ) : ℂ)
  obtain ⟨T, hTa, hT0, hTv⟩ := hPoles n hn (windingTau n : ℂ)
    ((Real.pi / (n : ℝ) : ℝ) : ℂ) γ
    (hτ.trans_le (min_le_left _ _)) (hd.trans_le (min_le_left _ _)) hgcenter
  let ell : zeroSumDisplacements n → ℂ := fun v =>
    fullDensityLog n g L.Lb L.Lh L.Ls L.Ld ((Real.pi / (n : ℝ) : ℝ) : ℂ)
      (windingTau n : ℂ) (T v) (v : Fin n → ℂ)
  refine ⟨T, ell, hTa.mono (Metric.ball_subset_ball hσp'), hT0, ?_⟩
  intro v hv
  have hvp := Metric.ball_subset_ball hσp' (zeroSumDisplacements_mem_ball_of_square_lt v hσ hv)
  obtain ⟨hlevel, _, hpole, hderiv, _⟩ := hTv v hvp
  have hvd : displacementSquare n (v : Fin n → ℂ) < σd ^ 2 :=
    hv.trans_le (by nlinarith)
  have hdpi : ‖((Real.pi / (n : ℝ) : ℝ) : ℂ)‖ ≤ Real.pi / (n : ℝ) := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg Real.pi_pos.le (Nat.cast_nonneg n))]
    exact le_rfl
  obtain ⟨hne, heq, hbound, hanalytic⟩ := hDensity n hn (windingTau n : ℂ)
    ((Real.pi / (n : ℝ) : ℝ) : ℂ) (hτ.trans_le (min_le_right _ _))
    (hd.trans_le (min_le_right _ _)) hdpi hgcenter (v : Fin n → ℂ)
    (zeroSumDisplacements_sum v) hvd (T v) hpole
  refine ⟨hlevel, hpole, hderiv, ?_, hne,
    complete_density_eq_vandermonde_center_exp heq, hbound⟩
  exact hanalytic.comp_of_eq ((hTa v hvp).prod ((zeroSumDisplacements n).subtypeL.analyticAt v)) rfl

end
end IsingBulk.AnisoF002.NegativeHT
