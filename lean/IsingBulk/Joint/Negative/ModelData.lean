import IsingBulk.Joint.Negative.CanonicalJets
import IsingBulk.Anisotropic.NegativeDominance.OddCoefficientIndex

/-! Actual complete odd coefficient series for an arbitrary independent-coupling
curve. These are literal Taylor jets of the angular coefficients, not a formal
model or a singularity assumption. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Filter IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators

def paperModelB (curve : ℂ→Coupling) (t : ℂ) : ℂ := transferB (curve t)
def paperModelRoot (curve : ℂ→Coupling) (amp : ℂ→ℂ) (t : ℂ) : ℂ := amp t/S (curve t)
def negativePaperParticleCoefficient (curve : ℂ→Coupling) (amp : ℂ→ℂ) (m j : ℕ) : ℂ :=
  iteratedDeriv j (fun t=>amp t^(2*m+1)*continuedAngularCoefficient (2*m) (curve t)) 0/(j.factorial:ℂ)
def negativePaperCoefficient (curve : ℂ→Coupling) (amp : ℂ→ℂ) (j : ℕ) : ℂ :=
  (∑'m,iteratedDeriv j (fun t=>amp t^(2*m+1)*continuedAngularCoefficient (2*m) (curve t)) 0)/(j.factorial:ℂ)

theorem negativePaperCoefficient_eq_particle_tsum (curve : ℂ→Coupling) (amp : ℂ→ℂ) (j : ℕ) :
    negativePaperCoefficient curve amp j=∑'m,negativePaperParticleCoefficient curve amp m j := by
  simp only [negativePaperCoefficient,negativePaperParticleCoefficient,tsum_div_const]

theorem negativePaperCoefficient_eq_oddLift {curve : ℂ→Coupling} {amp : ℂ→ℂ} {j : ℕ}
    (hs : Summable (fun m=>negativePaperParticleCoefficient curve amp m j)) :
    negativePaperCoefficient curve amp j=
      ∑'N,oddCoefficientLift (fun m=>negativePaperParticleCoefficient curve amp m j) N := by
  rw [negativePaperCoefficient_eq_particle_tsum]
  exact (oddCoefficientLift_hasSum hs).tsum_eq.symm

/-- Scalar model hypotheses follow from the actual curve and its chosen local
physical square root. No sign choice is silently substituted. -/
theorem paper_model_data {curve : ℂ→Coupling} {amp : ℂ→ℂ}
    (hc : AnalyticAt ℂ curve 0) (ha : AnalyticAt ℂ amp 0)
    (hs : S (curve 0)≠0) (ht : T (curve 0)≠0) (ha0 : amp 0≠0)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),amp t^2=p (curve t)) :
    AnalyticAt ℂ (paperModelB curve) 0 ∧ paperModelB curve 0≠0 ∧
    AnalyticAt ℂ (paperModelRoot curve amp) 0 ∧ paperModelRoot curve amp 0≠0 ∧
    ∀ᶠt in 𝓝 (0:ℂ),paperModelRoot curve amp t^2=paperModelB curve t := by
  have hS : AnalyticAt ℂ (fun t=>S (curve t)) 0 := Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)
  have hT : AnalyticAt ℂ (fun t=>T (curve t)) 0 := Complex.analyticAt_sinh.comp (analyticAt_snd.comp hc)
  refine ⟨hT.div hS hs,div_ne_zero ht hs,ha.div hS hs,div_ne_zero ha0 hs,?_⟩
  filter_upwards [hsq,hS.continuousAt.eventually_ne hs] with t hqt hst
  unfold paperModelRoot paperModelB transferB
  rw [div_pow,hqt]
  unfold p
  field_simp

end
end IsingBulk.Joint.Negative
