import IsingBulk.AnisoF002.C03.NegativeUniformDensityCost

/-!
# Uniform complete residue-density logarithm

This proves the full frozen `rc-density-log` mechanism from one analytic
even phase and the already constructed quadratic pole estimate.  Every
scalar neighborhood and every constant is selected before n.  The
logarithm is jointly analytic in the temperature and all displacements,
including every collision divisor.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology BigOperators

theorem exists_uniform_complete_density_log {b : ℂ → ℂ} {g : ℂ × ℂ → ℂ} {γ : ℂ}
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 ≠ 0)
    (hg : AnalyticAt ℂ g (0, 0)) (hg0 : g (0, 0) = γ)
    (hc : phaseTemperatureDerivative g (0, 0) ≠ 0)
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d))
    (hγ : Complex.sinh γ ≠ 0) {C : ℝ} (hC : 0 < C) :
    ∃ L : CompleteDensityScalarLogs b γ, ∃ σ K : ℝ, 0 < σ ∧ 0 < K ∧
      ∀ n : ℕ, 0 < n → ∀ τ d : ℂ, ‖τ‖ < σ → ‖d‖ < σ →
        ‖d‖ ≤ Real.pi / (n : ℝ) → g (τ, d) = γ →
        ∀ v : Fin n → ℂ, (∑ i, v i) = 0 → displacementSquare n v < σ ^ 2 →
        ∀ t : ℂ, ‖t - τ‖ ≤ C * displacementSquare n v / (n : ℝ) →
        filledNegativeDensityAt n b g d τ 0 ≠ 0 ∧
        filledNegativeDensityAt n b g d t v = filledNegativeDensityAt n b g d τ 0 *
          Complex.exp (fullDensityLog n g L.Lb L.Lh L.Ls L.Ld d τ t v) ∧
        ‖fullDensityLog n g L.Lb L.Lh L.Ls L.Ld d τ t v‖ ≤
          K * (Real.sqrt ((n : ℝ) * displacementSquare n v) + (n : ℝ) * displacementSquare n v) ∧
        AnalyticAt ℂ (fun p : ℂ × (Fin n → ℂ) =>
          fullDensityLog n g L.Lb L.Lh L.Ls L.Ld d τ p.1 p.2) (t, v) := by
  obtain ⟨L⟩ := exists_complete_density_scalar_logs hb hb0 hγ
  obtain ⟨rv, A, hrv, _, hA, hga, hvar⟩ := exists_uniform_even_phase_variation hg hc heven
  obtain ⟨rd, D, hrd, hD, hratio⟩ := exists_phase_derivative_ratio_bound hg hc
  have hgt : Tendsto g (𝓝 (0, 0)) (𝓝 γ) := by simpa only [hg0] using hg.continuousAt.tendsto
  obtain ⟨rg, hrg, hgn⟩ := Metric.eventually_nhds_iff.mp
    (hgt.eventually (Metric.ball_mem_nhds γ L.r_pos))
  let R : ℝ := min rv (min rd (min rg L.r))
  have hR : 0 < R := lt_min hrv (lt_min hrd (lt_min hrg L.r_pos))
  have hRrv : R ≤ rv := min_le_left _ _
  have hRrd : R ≤ rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRrg : R ≤ rg := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRr : R ≤ L.r := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let σ : ℝ := min (R / 4) (min 1 (min (1 / (C + 1)) (L.r / (4 * D * (C + 1)))))
  have hσ : 0 < σ := lt_min (by positivity) (lt_min zero_lt_one
    (lt_min (by positivity) (div_pos L.r_pos (by positivity))))
  have hσR : σ ≤ R / 4 := min_le_left _ _
  have hσ1 : σ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hσC : σ ≤ 1 / (C + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσD : σ ≤ L.r / (4 * D * (C + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have h2σR : 2 * σ < R := by linarith
  have hσR' : σ < R := by linarith
  have hσr : σ < L.r := hσR'.trans_le hRr
  have hCσ : C * σ ^ 2 ≤ σ := by
    have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp hσC
    have hcs : C * σ ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hcs hσ.le
    nlinarith
  have hDσ : D * (C + 1) * σ ^ 2 ≤ L.r / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * D * (C + 1))).mp hσD
    have hs2 : σ ^ 2 ≤ σ := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ D * (C + 1))
    nlinarith
  let K : ℝ := densityLogBoundConstant L.K A D C
  have hK : 0 < K := densityLogBoundConstant_pos L.K_pos.le hA.le hD.le hC.le
  refine ⟨L, σ, K, hσ, hK, ?_⟩
  intro n hn τ d hτ hd hdpi hcenter v hsum hQ t hpole
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ0 := displacementSquare_nonneg n v
  have hQdiv : displacementSquare n v / (n : ℝ) ≤ displacementSquare n v :=
    (div_le_iff₀ hnR).mpr (by nlinarith)
  have hvi (i : Fin n) : ‖v i‖ < σ := by
    have hi : ‖v i‖ ^ 2 ≤ displacementSquare n v :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  have hu : ‖t - τ‖ < σ := by
    calc
      ‖t - τ‖ ≤ C * (displacementSquare n v / (n : ℝ)) := by simpa only [mul_div_assoc] using hpole
      _ ≤ C * displacementSquare n v := mul_le_mul_of_nonneg_left hQdiv hC.le
      _ < C * σ ^ 2 := mul_lt_mul_of_pos_left hQ hC
      _ ≤ σ := hCσ
  have ht : ‖t‖ < 2 * σ := by
    have hh := norm_add_le (t - τ) τ
    rw [sub_add_cancel] at hh
    linarith
  have hdv (i : Fin n) : ‖d + v i‖ < 2 * σ :=
    (norm_add_le _ _).trans_lt (by linarith [hvi i])
  have hcenR : (τ, d) ∈ Metric.ball (0, 0) R := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_def,
      max_lt_iff] using And.intro (hτ.trans hσR') (hd.trans hσR')
  have htdR : (t, d) ∈ Metric.ball (0, 0) R := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_def,
      max_lt_iff] using And.intro (ht.trans h2σR) (hd.trans hσR')
  have hpointR (i : Fin n) : (t, d + v i) ∈ Metric.ball (0, 0) R := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_def,
      max_lt_iff] using And.intro (ht.trans h2σR) ((hdv i).trans h2σR)
  have hphase (i : Fin n) : g (t, d + v i) ∈ Metric.ball γ L.r :=
    hgn (Metric.mem_ball.mp (Metric.ball_subset_ball hRrg (hpointR i)))
  have hτb : τ ∈ Metric.ball 0 L.r := by simpa only [Metric.mem_ball, dist_zero_right] using hτ.trans hσr
  have htb : t ∈ Metric.ball 0 L.r := by simpa only [Metric.mem_ball, dist_zero_right] using (ht.trans h2σR).trans_le hRr
  have hsinc (ij : Fin n × Fin n) (_ : ij ∈ indexPairs n) :
      (v ij.1 - v ij.2) / 2 ∈ Metric.ball (0 : ℂ) L.r := by
    rw [Metric.mem_ball, dist_zero_right, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hh := norm_sub_le (v ij.1) (v ij.2)
    have hi := hvi ij.1
    have hj := hvi ij.2
    linarith
  obtain ⟨hcn, hrat⟩ := hratio n hn τ d t v hsum
    (Metric.ball_subset_ball hRrd hcenR) (Metric.ball_subset_ball hRrd htdR)
    (fun i => Metric.ball_subset_ball hRrd (hpointR i))
  have hratioBall : phaseTemperatureSum n g d t v /
      ((n : ℂ) * phaseTemperatureDerivative g (τ, d)) ∈ Metric.ball 1 L.r := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      _ ≤ D * (‖t - τ‖ + displacementSquare n v / (n : ℝ)) := hrat
      _ ≤ D * ((C + 1) * (displacementSquare n v / (n : ℝ))) := by
        gcongr
        calc
          _ ≤ C * (displacementSquare n v / (n : ℝ)) + displacementSquare n v / (n : ℝ) :=
            add_le_add (by simpa only [mul_div_assoc] using hpole) le_rfl
          _ = _ := by ring
      _ ≤ D * ((C + 1) * σ ^ 2) := by gcongr; exact hQdiv.trans hQ.le
      _ ≤ L.r / 4 := by simpa only [mul_assoc] using hDσ
      _ < L.r := by linarith [L.r_pos]
  obtain ⟨hne, heq⟩ := scalar_logs_full_density_identity L hn hcenter hτb htb hphase hsinc hcn hratioBall
  refine ⟨hne, heq, ?_, ?_⟩
  · have hphaseBound := sum_even_phase_variation hcenter hA.le
      (fun i => hvar τ d t (v i) (Metric.ball_subset_ball hRrv hcenR)
        (Metric.ball_subset_ball hRrv (hpointR i)) (hu.le.trans hσ1))
    have hcost := scalar_logs_full_density_cost L hτb htb hphase hsinc hratioBall
    have hpu : (n : ℝ) * ‖t - τ‖ ≤ C * displacementSquare n v := by
      simpa only [mul_comm] using (le_div_iff₀ hnR).mp hpole
    have hpd : (n : ℝ) * ‖d‖ ≤ Real.pi := by
      simpa only [mul_comm] using (le_div_iff₀ hnR).mp hdpi
    exact complete_density_cost_uniform hn1 hQ0 (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) L.K_pos.le hA.le hD.le hC.le
      hpu hpd hphaseBound hrat hcost
  · have hvA (i : Fin n) : AnalyticAt ℂ (fun p : ℂ × (Fin n → ℂ) => p.2 i) (t, v) := by
      have hproj : AnalyticAt ℂ (fun w : Fin n → ℂ => w i) v :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt v
      exact hproj.comp_of_eq
        (show AnalyticAt ℂ (Prod.snd : ℂ × (Fin n → ℂ) → (Fin n → ℂ)) (t, v) from analyticAt_snd) rfl
    exact fullDensityLog_analyticAt_comp analyticAt_fst hvA
      (fun i => hga _ (Metric.ball_subset_ball hRrv (hpointR i)))
      (L.b_analytic t htb) (fun i => L.h_analytic _ (hphase i))
      (fun ij hij => L.s_analytic _ (hsinc ij hij))
      (fun ij _ => L.h_analytic _ (average_mem_complex_ball (hphase ij.1) (hphase ij.2)))
      (L.d_analytic _ hratioBall)

end
end IsingBulk.AnisoF002.NegativeHT
