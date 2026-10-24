import IsingBulk.Anisotropic.NegativeCycles.MovingDividedDifference
import IsingBulk.Anisotropic.NegativeCycles.UniformCothSubtraction

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cothPoleRemainder_joint_analytic {F H : E × ℂ → ℂ} {T : E → ℂ}
    {R₀ : ℂ → ℂ} (n : ℕ) {x : E} {t : ℂ}
    (hF : AnalyticAt ℂ F (x,t)) (hFT : AnalyticAt ℂ F (x,T x))
    (hH : AnalyticAt ℂ H (x,t)) (hHT : AnalyticAt ℂ H (x,T x))
    (hT : AnalyticAt ℂ T x)
    (hfactor : dslope (fun s => F (x,s)) (T x) t≠0)
    (hder : deriv (fun s => F (x,s)) (T x)≠0)
    (hR₀ : AnalyticAt ℂ R₀ ((n:ℂ)*F (x,t))) :
    AnalyticAt ℂ (fun p : E × ℂ => cothPoleRemainder n R₀
      (fun s => F (p.1,s)) (fun s => H (p.1,s)) (T p.1) p.2) (x,t) := by
  let A : E × ℂ → ℂ := fun p => dslope (fun s => F (p.1,s)) (T p.1) p.2
  let Q : E × ℂ → ℂ := fun p => H p/A p
  have hA : AnalyticAt ℂ A (x,t) := analyticAt_moving_dslope hF hFT hT
  have hAT : AnalyticAt ℂ A (x,T x) := analyticAt_moving_dslope hFT hFT hT
  have hQ : AnalyticAt ℂ Q (x,t) := hH.div hA hfactor
  have hQT : AnalyticAt ℂ Q (x,T x) := hHT.div hAT (by simpa only [A,dslope_same] using hder)
  have hD := analyticAt_moving_dslope hQ hQT hT
  have hNF : AnalyticAt ℂ (fun p : E × ℂ => (n:ℂ)*F p) (x,t) := analyticAt_const.mul hF
  have hRC := hR₀.comp (f := fun p : E × ℂ => (n:ℂ)*F p) hNF
  exact (hH.mul hRC).add (analyticAt_const.mul hD)

end
end IsingBulk.Anisotropic.NegativeCycles
