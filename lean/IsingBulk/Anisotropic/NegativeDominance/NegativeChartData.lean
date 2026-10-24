import IsingBulk.Anisotropic.NegativeDominance.NegativePhysicalChart
import IsingBulk.Anisotropic.RegularEdges.LocalParticleRoot
import IsingBulk.Anisotropic.FormFactors.ParticleSeriesJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

def negativeChartB (lam : ℝ) (zeta : ℂ → ℂ) (u : ℂ) : ℂ :=
  -spectralT lam (zeta u)/spectralS (zeta u)
def negativeChartS (zeta : ℂ → ℂ) (u : ℂ) : ℂ := spectralS (zeta u)
def negativeChartRoot (lam : ℝ) (zeta : ℂ → ℂ) : ℂ → ℂ :=
  localParticleRoot (fun u => spectralProduct lam (zeta u))

theorem negativeChartS_analyticAt {zeta : ℂ → ℂ} (ha : AnalyticAt ℂ zeta 0) :
    AnalyticAt ℂ (negativeChartS zeta) 0 := Complex.analyticAt_sinh.comp ha

theorem negativeChartB_analyticAt {lam : ℝ} {zeta : ℂ → ℂ} (ha : AnalyticAt ℂ zeta 0)
    (hS : spectralS (zeta 0)≠0) : AnalyticAt ℂ (negativeChartB lam zeta) 0 := by
  have hT : AnalyticAt ℂ (fun u => spectralT lam (zeta u)) 0 :=
    Complex.analyticAt_sinh.comp (analyticAt_const.mul ha)
  exact hT.neg.div (negativeChartS_analyticAt ha) hS

theorem negativeChartRoot_analyticAt {lam : ℝ} {zeta : ℂ → ℂ}
    (ha : AnalyticAt ℂ zeta 0) (hP : spectralProduct lam (zeta 0)≠0) :
    AnalyticAt ℂ (negativeChartRoot lam zeta) 0 :=
  localParticleRoot_analyticAt ((FormFactors.spectralProduct_analyticAt_ff lam _).comp ha) hP

theorem negativeChartRoot_sq {lam : ℝ} {zeta : ℂ → ℂ}
    (hP : spectralProduct lam (zeta 0)≠0) (u : ℂ) :
    negativeChartRoot lam zeta u^2=spectralProduct lam (zeta u) := localParticleRoot_sq hP u

/-- All local branch data required by the weighted boundary-jet theorem are
constructed from an actual regular negative endpoint and its actual inverse. -/
theorem exists_negative_chart_data {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hd : spectralDet lam z<0)
    (hv : spectralV lam z= -1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (-1)) z≠0) :
    ∃ zeta : ℂ → ℂ, ∃ r : ℝ, 0<r ∧ zeta 0=z ∧
      AnalyticOnNhd ℂ zeta (ball 0 r) ∧
      AnalyticOnNhd ℂ (negativeChartRoot lam zeta) (ball 0 r) ∧
      ∀ u∈ball 0 r,
        0<(negativeChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧
        negativeChartRoot lam zeta u≠0 ∧
        edgeMapV lam (-1) (zeta u)=(spectralU lam z : ℂ)+u ∧
        (0<u.im → zeta u∈omegaH lam\{0}) := by
  obtain ⟨zeta,hza,hz0,r0,hr0,hchart⟩ := exists_negative_physical_chart hlam hz hd hv hu hder
  have hS : spectralS (zeta 0)≠0 := by rw [hz0]; exact spectralS_ne_zero_of_det_ne_zero hd.ne
  have hT : spectralT lam (zeta 0)≠0 := by rw [hz0]; exact spectralT_ne_zero_of_det_ne_zero hd.ne
  have hP : spectralProduct lam (zeta 0)≠0 := mul_ne_zero hS hT
  have hAa := negativeChartRoot_analyticAt hza hP
  have hA0 : negativeChartRoot lam zeta 0≠0 := localParticleRoot_ne_zero hP
  have hB0 : 0<(negativeChartB lam zeta 0).im := by
    change 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im
    rw [hz0]
    exact negative_ratio_im_pos hd
  have hBa := negativeChartB_analyticAt (lam := lam) hza hS
  have hSa := negativeChartS_analyticAt hza
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), AnalyticAt ℂ zeta u ∧
      AnalyticAt ℂ (negativeChartRoot lam zeta) u ∧
      0<(negativeChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧
      negativeChartRoot lam zeta u≠0 ∧ ‖u‖<r0 := by
    filter_upwards [hza.eventually_analyticAt,hAa.eventually_analyticAt,
      (Complex.continuous_im.continuousAt.comp hBa.continuousAt).eventually_const_lt hB0,
      hSa.continuousAt.eventually_ne hS,hAa.continuousAt.eventually_ne hA0,
      (Metric.ball_mem_nhds (0 : ℂ) hr0)] with u hz ha hb hs hroot hu
    exact ⟨hz,ha,hb,hs,hroot,by simpa only [mem_ball,dist_zero_right] using hu⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨zeta,r,hr,hz0,fun u hu => (hrsub hu).1,
    fun u hu => (hrsub hu).2.1,?_⟩
  intro u hurn
  obtain ⟨_,_,hb,hs,hroot,hu0⟩ := hrsub hurn
  obtain ⟨he,hin⟩ := hchart u hu0
  refine ⟨hb,hs,hroot,he,fun hi => ⟨hin hi,?_⟩⟩
  intro hz0'
  have hz0'' : zeta u=0 := Set.mem_singleton_iff.mp hz0'
  apply hs
  simp only [hz0'',spectralS,Complex.sinh_zero]

end
end IsingBulk.Anisotropic.NegativeDominance
