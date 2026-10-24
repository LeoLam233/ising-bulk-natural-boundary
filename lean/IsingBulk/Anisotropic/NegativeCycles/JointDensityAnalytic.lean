import IsingBulk.Anisotropic.NegativeCycles.ComplexNumeratorBound
import IsingBulk.Anisotropic.NegativeNormalForm.ResonantKernel
import IsingBulk.Anisotropic.NegativeNormalForm.DensityAnalytic

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped Topology BigOperators

set_option maxHeartbeats 800000 in
theorem local_density_phase_joint_analytic (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hr : AnalyticAt ℂ rootB 0) :
    ∃r : ℝ,0<r ∧ ∀m : ℕ, ∀d T : ℂ, ∀v : Config (2*m+1),
      ‖T‖<r → (∀i, ‖d+v i‖<r) →
      AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => formFactorNumerator B rootB phi hphi d z.2 z.1) (v,T) ∧
      AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => poleEquation B phi hphi d z.2 z.1) (v,T) := by
  have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => negativePhase B phi hphi p.1 p.2) (0,0) := by
    simpa using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  obtain ⟨r0,hr0,h0⟩ := Metric.eventually_nhds_iff.mp
    (hB.eventually_analyticAt.and hr.eventually_analyticAt)
  obtain ⟨r1,hr1,h1⟩ := Metric.eventually_nhds_iff.mp
    (hg.eventually_analyticAt.and (localOneBody_analyticAt B phi hphi hB).eventually_analyticAt)
  obtain ⟨r2,hr2,h2⟩ := Metric.eventually_nhds_iff.mp
    (localCompletePair_analyticAt B phi hphi hB).eventually_analyticAt
  let r := min r0 (min r1 r2)
  have hrr : 0<r := lt_min hr0 (lt_min hr1 hr2)
  have hle0 : r≤r0 := min_le_left _ _
  have hle1 : r≤r1 := (min_le_right _ _).trans (min_le_left _ _)
  have hle2 : r≤r2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hrr,?_⟩
  intro m d T v hT hv
  have hscalar : AnalyticAt ℂ B T ∧ AnalyticAt ℂ rootB T := h0 (y := T) (by simpa [dist_zero_right] using hT.trans_le hle0)
  have hphase (i : Fin (2*m+1)) : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => negativePhase B phi hphi z.2 (d+z.1 i)) (v,T) := by
    have hd : dist (T,d+v i) (0,0)<r1 := by
      change dist (T,d+v i) (0 : ℂ × ℂ)<r1
      simpa [dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro (hT.trans_le hle1) ((hv i).trans_le hle1)
    exact (h1 (y := (T,d+v i)) hd).1.comp_of_eq (f := fun z : Config (2*m+1) × ℂ => (z.2,d+z.1 i)) (analyticAt_snd.prod (analyticAt_const.add ((ContinuousLinearMap.proj i : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst))) rfl
  have hone (i : Fin (2*m+1)) : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => (Complex.sinh (negativePhase B phi hphi z.2 (d+z.1 i)))⁻¹) (v,T) := by
    have hd : dist (T,d+v i) (0,0)<r1 := by
      change dist (T,d+v i) (0 : ℂ × ℂ)<r1
      simpa [dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro (hT.trans_le hle1) ((hv i).trans_le hle1)
    exact (h1 (y := (T,d+v i)) hd).2.comp_of_eq (f := fun z : Config (2*m+1) × ℂ => (z.2,d+z.1 i)) (analyticAt_snd.prod (analyticAt_const.add ((ContinuousLinearMap.proj i : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst))) rfl
  have hpair (i j : Fin (2*m+1)) :
      AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => localCompletePair B phi hphi z.2 (d+z.1 i) (d+z.1 j)) (v,T) := by
    have hd : dist (T,d+v i,d+v j) (0 : ℂ × ℂ × ℂ)<r2 := by
      simpa [dist_zero_right,Prod.norm_def,max_lt_iff] using
        And.intro (hT.trans_le hle2) (And.intro ((hv i).trans_le hle2) ((hv j).trans_le hle2))
    exact (h2 (y := (T,d+v i,d+v j)) hd).comp_of_eq (f := fun z : Config (2*m+1) × ℂ => (z.2,d+z.1 i,d+z.1 j)) (analyticAt_snd.prod ((analyticAt_const.add ((ContinuousLinearMap.proj i : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst)).prod (analyticAt_const.add ((ContinuousLinearMap.proj j : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst)))) rfl
  constructor
  · have hpre : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => rootB z.2*B z.2^m / (((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))) (v,T) :=
      ((hscalar.2.comp (f := fun z : Config (2*m+1) × ℂ => z.2) analyticAt_snd).mul ((hscalar.1.comp (f := fun z : Config (2*m+1) × ℂ => z.2) analyticAt_snd).pow m)).div_const
    have ha := hpre.mul
      (Finset.univ.analyticAt_fun_prod (fun i _ => hone i))
    have hh := ha.mul ((firstStrictPairs (2*m+1)).analyticAt_fun_prod (fun p _ => hpair p.1 p.2))
    apply hh.congr
    exact Filter.Eventually.of_forall (fun z => (formFactorNumerator_odd_complete_pairs m B rootB phi hphi d z.2 z.1).symm)
  · unfold poleEquation
    exact Finset.univ.analyticAt_fun_sum (fun i _ => (hphase i).sub analyticAt_const)

end IsingBulk.Anisotropic.NegativeCycles
