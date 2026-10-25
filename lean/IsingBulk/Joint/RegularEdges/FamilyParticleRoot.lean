import IsingBulk.Joint.RegularEdges.WeightedFullSum
import IsingBulk.Joint.RegularEdges.FamilyTailJets
import IsingBulk.Joint.Transverse.CurveCoordinates

/-! # A single canonical physical particle root over every admissible family -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric
open scoped Topology

/-- The upper-half-plane anisotropy fixes the branch globally on the family,
so no parameter-dependent square-root choices or simply-connectedness are needed. -/
def positiveParticleRoot (K : Coupling) : ℂ := S K*Complex.sqrt (transferB K)

theorem positiveParticleRoot_sq (K : Coupling) : positiveParticleRoot K^2=p K := by
  unfold positiveParticleRoot
  rw [mul_pow,IsingBulk.Branch.sqrt_sq]
  unfold transferB p
  by_cases hs : S K=0
  · simp [hs]
  · field_simp

theorem positiveParticleRoot_ne_zero {K : Coupling} (hS : S K≠0)
    (hB : 0<(transferB K).im) : positiveParticleRoot K≠0 := by
  apply mul_ne_zero hS
  intro hz
  have hh := IsingBulk.Branch.sqrt_sq (transferB K)
  rw [hz,zero_pow (by decide : 2≠0)] at hh
  rw [←hh,Complex.zero_im] at hB
  exact lt_irrefl _ hB

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem transferB_family_analyticAt {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hS : S (curve x)≠0) :
    AnalyticAt ℂ (fun x=>transferB (curve x)) x :=
  (Complex.analyticAt_sinh.comp (analyticAt_snd.comp hc)).div
    (Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)) hS

theorem positiveParticleRoot_family_analyticAt {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hS : S (curve x)≠0)
    (hB : 0<(transferB (curve x)).im) :
    AnalyticAt ℂ (fun x=>positiveParticleRoot (curve x)) x := by
  have hb : transferB (curve x)∈Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hB))
  exact (Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)).mul
    ((Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane _ hb).comp
      (f := fun x=>transferB (curve x)) (transferB_family_analyticAt (curve := curve) hc hS))

theorem positiveParticleScale_family_analyticAt {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hS : S (curve x)≠0)
    (hB : 0<(transferB (curve x)).im) :
    AnalyticAt ℂ (fun x=>S (curve x)/positiveParticleRoot (curve x)) x :=
  (Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)).div
    (positiveParticleRoot_family_analyticAt hc hS hB) (positiveParticleRoot_ne_zero hS hB)

end
end IsingBulk.Joint.RegularEdges
