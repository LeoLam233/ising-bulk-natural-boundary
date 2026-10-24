import IsingBulk.Anisotropic.RegularEdges.LeadingPrimeCharts
import IsingBulk.Anisotropic.RegularEdges.LocalFourthRoot
import IsingBulk.Anisotropic.Final.PhysicalEdgeCharts

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter Metric
open scoped Topology

def positiveChartB (lam : ℝ) (zeta : ℂ→ℂ) (u : ℂ) : ℂ := spectralT lam (zeta u)/spectralS (zeta u)
def positiveChartS (zeta : ℂ→ℂ) (u : ℂ) : ℂ := spectralS (zeta u)
def positiveChartRoot (lam : ℝ) (zeta : ℂ→ℂ) : ℂ→ℂ := localParticleRoot (fun u => spectralProduct lam (zeta u))

theorem positive_ratio_im (lam : ℝ) (z : ℂ) :
    (spectralT lam z/spectralS z).im=spectralDet lam z/Complex.normSq (spectralS z) := by
  simp only [Complex.div_im,spectralDet]
  ring

theorem positiveChartS_analyticAt {zeta : ℂ→ℂ} (ha : AnalyticAt ℂ zeta 0) :
    AnalyticAt ℂ (positiveChartS zeta) 0 := Complex.analyticAt_sinh.comp ha

theorem positiveChartB_analyticAt {lam : ℝ} {zeta : ℂ→ℂ} (ha : AnalyticAt ℂ zeta 0)
    (hS : spectralS (zeta 0)≠0) : AnalyticAt ℂ (positiveChartB lam zeta) 0 := by
  exact (Complex.analyticAt_sinh.comp (analyticAt_const.mul ha)).div (positiveChartS_analyticAt ha) hS

theorem positiveChartRoot_analyticAt {lam : ℝ} {zeta : ℂ→ℂ} (ha : AnalyticAt ℂ zeta 0)
    (hP : spectralProduct lam (zeta 0)≠0) : AnalyticAt ℂ (positiveChartRoot lam zeta) 0 :=
  localParticleRoot_analyticAt ((FormFactors.spectralProduct_analyticAt_ff lam _).comp ha) hP

theorem exists_positive_chart_data {lam b : ℝ} {D : Set ℂ} {zeta : ℂ→ℂ} {r₀ : ℝ}
    (hza : AnalyticAt ℂ zeta 0) (hd : 0<spectralDet lam (zeta 0)) (hr₀ : 0<r₀)
    (hchart : ∀u : ℂ,‖u‖<r₀ → edgeMapV lam 1 (zeta u)=(b:ℂ)+u ∧ (0<u.im → zeta u∈D)) :
    ∃r : ℝ,0<r ∧ AnalyticOnNhd ℂ zeta (ball 0 r) ∧
      AnalyticOnNhd ℂ (positiveChartRoot lam zeta) (ball 0 r) ∧
      ∀u∈ball 0 r,0<(positiveChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧
        positiveChartRoot lam zeta u≠0 ∧ edgeMapV lam 1 (zeta u)=(b:ℂ)+u ∧
        (0<u.im → zeta u∈D\{0}) := by
  have hS := spectralS_ne_zero_of_det_ne_zero hd.ne'
  have hT := spectralT_ne_zero_of_det_ne_zero hd.ne'
  have hP : spectralProduct lam (zeta 0)≠0 := mul_ne_zero hS hT
  have hAa := positiveChartRoot_analyticAt hza hP
  have hA0 : positiveChartRoot lam zeta 0≠0 := localParticleRoot_ne_zero hP
  have hB0 : 0<(positiveChartB lam zeta 0).im := by
    rw [positiveChartB,positive_ratio_im]
    exact div_pos hd (Complex.normSq_pos.mpr hS)
  have hBa := positiveChartB_analyticAt (lam := lam) hza hS
  have hSa := positiveChartS_analyticAt hza
  have hev : ∀ᶠ u in 𝓝 (0:ℂ),AnalyticAt ℂ zeta u ∧ AnalyticAt ℂ (positiveChartRoot lam zeta) u ∧
      0<(positiveChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧ positiveChartRoot lam zeta u≠0 ∧ ‖u‖<r₀ := by
    filter_upwards [hza.eventually_analyticAt,hAa.eventually_analyticAt,
      (Complex.continuous_im.continuousAt.comp hBa.continuousAt).eventually_const_lt hB0,
      hSa.continuousAt.eventually_ne hS,hAa.continuousAt.eventually_ne hA0,ball_mem_nhds (0:ℂ) hr₀]
      with u hz ha hb hs hr hu
    exact ⟨hz,ha,hb,hs,hr,by simpa only [mem_ball,dist_zero_right] using hu⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r,hr,fun u hu => (hrsub hu).1,fun u hu => (hrsub hu).2.1,?_⟩
  intro u hu
  obtain ⟨_,_,hb,hs,hA,hur⟩ := hrsub hu
  obtain ⟨he,hin⟩ := hchart u hur
  refine ⟨hb,hs,hA,he,fun hi => ⟨hin hi,?_⟩⟩
  intro hzero
  apply hs
  simp only [Set.mem_singleton_iff.mp hzero,spectralS,Complex.sinh_zero]

theorem upperBall_inward {r : ℝ} (hr : 0<r) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈upperBall r := by
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,htend.eventually (ball_mem_nhds _ hr)] with t ht hb
  refine ⟨hb,?_⟩
  change 0<(Complex.I*(t:ℂ)^2).im
  rw [←Complex.ofReal_pow]
  simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,one_mul,zero_add] using sq_pos_of_pos ht

theorem domain_extension_comp_of_mapsTo {D U : Set ℂ} {f zeta : ℂ→ℂ} {z : ℂ}
    (hza : AnalyticAt ℂ zeta 0) (hz0 : zeta 0=z) (hmap : MapsTo zeta U D)
    (hf : HasDomainExtension D f z) : HasDomainExtension U (f ∘ zeta) 0 := by
  obtain ⟨V,hV,hzV,g,hg,heq⟩ := hf
  have hev := hza.eventually_analyticAt.and (hza.continuousAt.eventually (by rw [hz0]; exact hV.mem_nhds hzV))
  obtain ⟨W,hW,hWo,h0W⟩ := _root_.mem_nhds_iff.mp hev
  refine ⟨W,hWo,h0W,g ∘ zeta,fun u hu => (hg _ (hW hu).2).comp (hW hu).1,?_⟩
  intro u hu
  exact heq ⟨(hW hu.1).2,hmap hu.2⟩

end
end IsingBulk.Anisotropic.RegularEdges
