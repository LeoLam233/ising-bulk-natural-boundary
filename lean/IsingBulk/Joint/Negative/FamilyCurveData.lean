import IsingBulk.Joint.Negative.FamilyCoefficientRanges
import IsingBulk.Joint.Geometry.TransferChart

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def familyPaperB (curve : ℂ × E→Coupling) (q : ℂ × E) : ℂ := transferB (curve q)
def familyPaperRoot (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) (q : ℂ × E) : ℂ :=
  amp q/S (curve q)

theorem familyPaperB_analyticAt {curve : ℂ × E→Coupling} {eta : E}
    (hc : AnalyticAt ℂ curve (0,eta)) (hS : S (curve (0,eta))≠0) :
    AnalyticAt ℂ (familyPaperB curve) (0,eta) :=
  (transferB_analyticAt hS).comp hc

theorem familyPaperRoot_analyticAt {curve : ℂ × E→Coupling} {amp : ℂ × E→ℂ} {eta : E}
    (hc : AnalyticAt ℂ curve (0,eta)) (ha : AnalyticAt ℂ amp (0,eta))
    (hS : S (curve (0,eta))≠0) :
    AnalyticAt ℂ (familyPaperRoot curve amp) (0,eta) :=
  ha.div (Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)) hS

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- The particle amplitude and both literal model factors are nonzero because
of the actual negative-edge geometry and the physical square identity. -/
theorem familyPaper_nonzero {curve : ℂ × E→Coupling} {amp : ℂ × E→ℂ} {eta : E}
    (hS : S (curve (0,eta))≠0) (hB : (transferB (curve (0,eta))).im<0)
    (hsq : ∀ᶠt : ℂ in 𝓝 0,amp (t,eta)^2=p (curve (t,eta))) :
    amp (0,eta)≠0 ∧ familyPaperB curve (0,eta)≠0 ∧ familyPaperRoot curve amp (0,eta)≠0 := by
  have hBn : transferB (curve (0,eta))≠0 := by
    intro hz
    simp only [hz,Complex.zero_im,lt_self_iff_false] at hB
  have hT : T (curve (0,eta))≠0 := by
    intro hz
    apply hBn
    simp [transferB,hz]
  have hp : p (curve (0,eta))≠0 := mul_ne_zero hS hT
  have han : amp (0,eta)≠0 := by
    intro hz
    have hh := hsq.self_of_nhds
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hh
    exact hp hh.symm
  exact ⟨han,hBn,div_ne_zero han hS⟩

theorem familyPaper_square_germ {curve : ℂ × E→Coupling} {amp : ℂ × E→ℂ} {eta : E}
    (hc : AnalyticAt ℂ curve (0,eta)) (hS : S (curve (0,eta))≠0)
    (hsq : ∀ᶠt : ℂ in 𝓝 0,amp (t,eta)^2=p (curve (t,eta))) :
    ∀ᶠt : ℂ in 𝓝 0, familyPaperRoot curve amp (t,eta)^2=familyPaperB curve (t,eta) := by
  have hsa : AnalyticAt ℂ (fun t : ℂ=>S (curve (t,eta))) 0 :=
    (Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)).comp
      (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  filter_upwards [hsq,hsa.continuousAt.eventually_ne hS] with t hqt hst
  unfold familyPaperRoot familyPaperB transferB
  rw [div_pow,hqt]
  unfold p
  field_simp

end
end IsingBulk.Joint.Negative
