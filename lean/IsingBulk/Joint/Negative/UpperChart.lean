import IsingBulk.Joint.Negative.CurveCoordinates

/-! Upper-half-plane transfer chart for arbitrary independent-coupling curves.
The sign is the upper-root convention, opposite to the manuscript B. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.RegularEdges

def negativeChartB (curve : ℂ→Coupling) (u : ℂ) : ℂ := -T (curve u)/S (curve u)
def negativeChartS (curve : ℂ→Coupling) (u : ℂ) : ℂ := S (curve u)
def negativeChartRoot (curve : ℂ→Coupling) : ℂ→ℂ := localParticleRoot (fun u=>p (curve u))

theorem negativeChartS_analyticAt {curve : ℂ→Coupling} (ha : AnalyticAt ℂ curve 0) :
    AnalyticAt ℂ (negativeChartS curve) 0 :=
  Complex.analyticAt_sinh.comp (analyticAt_fst.comp ha)

theorem negativeChartB_analyticAt {curve : ℂ→Coupling} (ha : AnalyticAt ℂ curve 0)
    (hS : S (curve 0)≠0) : AnalyticAt ℂ (negativeChartB curve) 0 := by
  have hT : AnalyticAt ℂ (fun u=>T (curve u)) 0 :=
    Complex.analyticAt_sinh.comp (analyticAt_snd.comp ha)
  exact hT.neg.div (negativeChartS_analyticAt ha) hS

theorem negativeChartRoot_analyticAt {curve : ℂ→Coupling}
    (ha : AnalyticAt ℂ curve 0) (hP : p (curve 0)≠0) :
    AnalyticAt ℂ (negativeChartRoot curve) 0 :=
  localParticleRoot_analyticAt
    ((Complex.analyticAt_sinh.comp (analyticAt_fst.comp ha)).mul
      (Complex.analyticAt_sinh.comp (analyticAt_snd.comp ha))) hP

theorem negativeChartRoot_sq {curve : ℂ→Coupling}
    (hP : p (curve 0)≠0) (u : ℂ) : negativeChartRoot curve u^2=p (curve u) :=
  localParticleRoot_sq hP u

end
end IsingBulk.Joint.Negative
