import IsingBulk.Anisotropic.NegativeDominance.NegativePaperObstruction
import IsingBulk.Anisotropic.NegativeCycles.LocalPhysicalDensity

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter RegularEdges NegativeCycles
open scoped Topology

/-- The manuscript ratio has the opposite sign from the upper-u root chart. -/
def paperModelB (lam : ℝ) (zeta : ℂ→ℂ) (t : ℂ) : ℂ :=
  spectralT lam (zeta t)/spectralS (zeta t)

def paperModelRoot (zeta A : ℂ→ℂ) (t : ℂ) : ℂ := A t/spectralS (zeta t)

def negativePaperParticleCoefficient (lam : ℝ) (zeta A : ℂ→ℂ) (n j : ℕ) : ℂ :=
  iteratedDeriv j (fun t => A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0/(j.factorial : ℂ)

theorem negativePaperCoefficient_eq_particle_tsum (lam : ℝ) (zeta A : ℂ→ℂ) (j : ℕ) :
    negativePaperCoefficient lam zeta A j=∑'n,negativePaperParticleCoefficient lam zeta A n j := by
  simp only [negativePaperCoefficient,negativePaperParticleCoefficient,tsum_div_const]

/-- All scalar branch hypotheses of the exact Gamma model follow from the
actual physical chart; no extra branch choice or sign convention is imposed. -/
theorem paper_model_data {lam : ℝ} {z : ℂ} (hd : spectralDet lam z<0)
    {zeta A : ℂ→ℂ} (hz : zeta 0=z) (hza : AnalyticAt ℂ zeta 0)
    (hAa : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), A t^2=spectralProduct lam (zeta t)) :
    AnalyticAt ℂ (paperModelB lam zeta) 0 ∧ paperModelB lam zeta 0≠0 ∧
    AnalyticAt ℂ (paperModelRoot zeta A) 0 ∧ paperModelRoot zeta A 0≠0 ∧
    ∀ᶠ t in 𝓝 (0 : ℂ),paperModelRoot zeta A t^2=paperModelB lam zeta t := by
  have hS0 : spectralS (zeta 0)≠0 := by rw [hz]; exact spectralS_ne_zero_of_det_ne_zero hd.ne
  have hT0 : spectralT lam (zeta 0)≠0 := by rw [hz]; exact spectralT_ne_zero_of_det_ne_zero hd.ne
  have hSa : AnalyticAt ℂ (fun t => spectralS (zeta t)) 0 := negativeChartS_analyticAt hza
  have hTa : AnalyticAt ℂ (fun t => spectralT lam (zeta t)) 0 :=
    Complex.analyticAt_sinh.comp (analyticAt_const.mul hza)
  refine ⟨hTa.div hSa hS0,div_ne_zero hT0 hS0,hAa.div hSa hS0,div_ne_zero hA0 hS0,?_⟩
  filter_upwards [hsq,hSa.continuousAt.eventually_ne hS0] with t ht hs
  exact paper_rootB_sq hs ht

end
end IsingBulk.Anisotropic.NegativeDominance
