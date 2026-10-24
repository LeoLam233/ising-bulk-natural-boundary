import IsingBulk.Anisotropic.NegativeDominance.NegativeChartData
import IsingBulk.Anisotropic.NegativeDominance.PhysicalCompleteBoundaryJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

def negativeScaledHighSeries (lam : ℝ) (zeta : ℂ → ℂ) (u : ℂ) : ℂ :=
  negativeChartRoot lam zeta u * ∑' n : ℕ,
    (spectralProduct lam (zeta u))^n * FormFactors.unscaledFullCoefficient (2*n+1) lam (zeta u)
def negativeScaledParticleGerm (n : ℕ) (lam : ℝ) (zeta : ℂ → ℂ) (u : ℂ) : ℂ :=
  (negativeChartRoot lam zeta u)^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta u)

/-- Complete all-order boundary jets of the actual weighted HT series at an
actual regular negative endpoint. The coordinate, physical side, square root,
finite-term continuations and infinite-series bounds are all constructed. -/
theorem exists_negative_endpoint_complete_jets {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hd : spectralDet lam z<0)
    (hv : spectralV lam z= -1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (-1)) z≠0) :
    ∃ zeta : ℂ → ℂ, ∃ r : ℝ, 0<r ∧ zeta 0=z ∧ AnalyticAt ℂ zeta 0 ∧
      AnalyticAt ℂ (negativeChartRoot lam zeta) 0 ∧ negativeChartRoot lam zeta 0≠0 ∧
      (∀ u, ‖u‖<r → edgeMapV lam (-1) (zeta u)=(spectralU lam z : ℂ)+u) ∧
      ∀ j : ℕ,
        Summable (fun n : ℕ => ‖iteratedDeriv j (negativeScaledParticleGerm n lam zeta) 0‖) ∧
        Tendsto (fun ε : ℝ => iteratedDeriv j (negativeScaledHighSeries lam zeta)
          (Complex.I*(ε : ℂ))) (𝓝[>] 0)
          (𝓝 (∑' n : ℕ, iteratedDeriv j (negativeScaledParticleGerm n lam zeta) 0)) := by
  obtain ⟨zeta,r,hr,hz0,hza,hAa,hdata⟩ := exists_negative_chart_data hlam hz hd hv hu hder
  have h0 : (0 : ℂ)∈ball 0 r := mem_ball_self hr
  have hSa := negativeChartS_analyticAt (hza 0 h0)
  have hS0 := (hdata 0 h0).2.1
  have hP : spectralProduct lam (zeta 0)≠0 := by
    apply mul_ne_zero hS0
    rw [hz0]
    exact spectralT_ne_zero_of_det_ne_zero hd.ne
  have hBa := negativeChartB_analyticAt (lam := lam) (hza 0 h0) hS0
  have hB0 := (hdata 0 h0).1
  have hA0 := (hdata 0 h0).2.2.1
  have hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=
      (spectralU lam z : ℂ)*spectralS (zeta 0) := by
    rw [hz0,spectral_reconstruction hd.ne,hv]
    simp only [Complex.ofReal_neg,Complex.ofReal_one]
    ring
  let U : Set ℂ := ball 0 r ∩ {u : ℂ | 0<u.im}
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hzu : AnalyticOnNhd ℂ zeta U := fun u hu => hza u hu.1
  have hAu : AnalyticOnNhd ℂ (negativeChartRoot lam zeta) U := fun u hu => hAa u hu.1
  have hzH : ∀ u∈U, zeta u∈omegaH lam\{0} := fun u hu => (hdata u hu.1).2.2.2.2 hu.2
  have hSu : ∀ u∈U, spectralS (zeta u)≠0 := fun u hu => (hdata u hu.1).2.1
  have hBu : ∀ u∈U, negativeChartB lam zeta u= -spectralT lam (zeta u)/spectralS (zeta u) := fun _ _ => rfl
  have hSdef : ∀ u∈U, negativeChartS zeta u=spectralS (zeta u) := fun _ _ => rfl
  have he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(spectralU lam z : ℂ)+u :=
    fun u hu => (hdata u hu.1).2.2.2.1
  have hup : ∀ u∈U, 0<u.im := fun _ hu => hu.2
  have hBi : ∀ u∈U, 0<(negativeChartB lam zeta u).im := fun u hu => (hdata u hu.1).1
  have hAne : ∀ u∈U, negativeChartRoot lam zeta u≠0 := fun u hu => (hdata u hu.1).2.2.1
  have hAsq : ∀ u∈U, (negativeChartRoot lam zeta u)^2=spectralProduct lam (zeta u) :=
    fun u _ => negativeChartRoot_sq hP u
  have hzn : ∀ u∈U, zeta u∉spectralSet lam :=
    fun u hu => omegaH_subset_spectral_complement hlam (hzH u hu).1
  have hp : Tendsto (fun ε : ℝ => Complex.I*(ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => Complex.I*(ε : ℂ)) := continuous_const.mul Complex.continuous_ofReal
    simpa only [Complex.ofReal_zero,mul_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hin : ∀ᶠ ε : ℝ in 𝓝[>] 0, Complex.I*(ε : ℂ)∈U := by
    filter_upwards [hp.eventually (ball_mem_nhds (0 : ℂ) hr),self_mem_nhdsWithin] with ε hε hpos
    refine ⟨hε,?_⟩
    simpa using hpos
  refine ⟨zeta,r,hr,hz0,hza 0 h0,hAa 0 h0,hA0,?_,?_⟩
  · intro u hu
    exact (hdata u (by simpa only [mem_ball,dist_zero_right] using hu)).2.2.2.1
  intro j
  constructor
  · exact complete_odd_scaledNegativePeriod_boundary_jets_upper_norm_summable
      hu hB0 hBa hSa hS0 (hAa 0 h0) hA0 (hza 0 h0) hS0 hedge hB0 hU hzu hAu hzn hSu
      hBu hSdef he hup hBi hp hin j
  · exact physical_scaled_high_series_boundary_jets hlam
      hu hB0 hBa hSa hS0 (hAa 0 h0) hA0 (hza 0 h0) hS0 hedge hB0 hU hzu hAu hzH hSu
      hBu hSdef he hup hBi hAsq hAne hp hin j

end
end IsingBulk.Anisotropic.NegativeDominance
