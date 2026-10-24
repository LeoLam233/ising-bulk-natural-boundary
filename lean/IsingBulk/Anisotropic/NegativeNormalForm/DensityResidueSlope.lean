import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueScalar
import IsingBulk.Anisotropic.NegativeNormalForm.UniformPhaseSlope

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators
open IsingBulk.First
set_option maxHeartbeats 800000

def residueSlopeRatio (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (p : ScalarTriple) : ℂ :=
  phaseParameterSlope B phi hphi (p.1,p.2.1+p.2.2)/centralParameterSlope B phi p.2.1

theorem phaseParameterSlope_even (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (t x : ℂ) :
    phaseParameterSlope B phi hphi (t,-x)=phaseParameterSlope B phi hphi (t,x) := by
  simp only [phaseParameterSlope_eq]
  congr 1
  funext u
  exact negativePhase_even B phi hphi u x

theorem residueSlopeRatio_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    AnalyticAt ℂ (residueSlopeRatio B phi hphi) 0 := by
  have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => negativePhase B phi hphi p.1 p.2) (0,0) := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  have hj : AnalyticAt ℂ (phaseParameterSlope B phi hphi) (0,0) := jointParameterJet_analyticAt hg 1
  have ht : AnalyticAt ℂ (fun p : ScalarTriple => p.1) 0 := analyticAt_fst
  have hd : AnalyticAt ℂ (fun p : ScalarTriple => p.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hx : AnalyticAt ℂ (fun p : ScalarTriple => p.2.2) 0 := analyticAt_snd.comp analyticAt_snd
  have hc : AnalyticAt ℂ (fun p : ScalarTriple => 1-Complex.cos p.2.1) 0 :=
    analyticAt_const.sub (Complex.analyticAt_cos.comp hd)
  have hden : AnalyticAt ℂ (fun p : ScalarTriple => centralParameterSlope B phi p.2.1) 0 :=
    analyticAt_const.mul (hB.fun_comp_of_eq hc (by simp))
  exact (hj.fun_comp_of_eq (ht.prod (hd.add hx)) (by simp)).div hden
    (centralParameterSlope_ne_zero B phi hphi 0 (by simpa using hBn))

theorem residueSlopeRatio_center (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d)≠0) :
    residueSlopeRatio B phi hphi (1-Complex.cos d,(d,0))=1 := by
  simp only [residueSlopeRatio,add_zero,phaseParameterSlope_eq]
  rw [(negativePhase_hasDerivAt_center B phi hphi d _ hB.differentiableAt.hasDerivAt).deriv]
  exact div_self (centralParameterSlope_ne_zero B phi hphi d hBn)

theorem residueSlopeRatio_control (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t d x : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r →
      ‖residueSlopeRatio B phi hphi (t,(d,x))-1‖ ≤
        L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖x‖)*‖x‖) := by
  obtain ⟨r,L,hr,hL,h⟩ := analytic_even_axis_moving_center_control _
    (residueSlopeRatio_analyticAt B phi hphi hB hBn)
    (fun t v => by simp only [residueSlopeRatio,zero_add,phaseParameterSlope_even])
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp
    (hB.eventually_analyticAt.and (hB.continuousAt.eventually_ne hBn))
  refine ⟨min r s,L,lt_min hr hs,hL,?_⟩
  intro t d x ht ht₀ hd hx
  have hb := hball (show 1-Complex.cos d∈ball (0:ℂ) s by simpa using ht₀.trans_le (min_le_right _ _))
  have hh := h t (1-Complex.cos d) d x (ht.trans_le (min_le_left _ _))
    (ht₀.trans_le (min_le_left _ _)) (hd.trans_le (min_le_left _ _)) (hx.trans_le (min_le_left _ _))
  rwa [residueSlopeRatio_center B phi hphi d hb.1 hb.2] at hh

/-- The parameter derivative of the original phase sum is the actual sum of
scalar parameter derivatives, not a replacement residue denominator. -/
theorem poleParameterDerivative_eq_sum {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (ha : ∀i,AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d+v i)) :
    poleParameterDerivative B phi hphi d t v=∑i,phaseParameterSlope B phi hphi (t,d+v i) := by
  have hd (i : Fin n) : HasDerivAt (fun u => negativePhase B phi hphi u (d+v i))
      (phaseParameterSlope B phi hphi (t,d+v i)) t := by
    rw [phaseParameterSlope_eq]
    apply DifferentiableAt.hasDerivAt
    exact ((ha i).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl).differentiableAt
  have hh := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hd i).sub_const ((phi:ℂ)*Complex.I))
  have hh' : HasDerivAt (fun u => poleEquation B phi hphi d u v)
      (∑i,phaseParameterSlope B phi hphi (t,d+v i)) t := by
    convert hh using 1
    ext u
    simp only [poleEquation,Finset.sum_apply]
  exact hh'.deriv

end
end IsingBulk.Anisotropic.NegativeNormalForm
