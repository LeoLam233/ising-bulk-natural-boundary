import IsingBulk.Anisotropic.NegativeNormalForm.AnalyticHadamard

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem coordinateHadamard_axis_translate (f : E × ℂ → ℂ) (a : E) (z : E × ℂ) :
    coordinateHadamard (fun w => f ((a,0)+w)) z=coordinateHadamard f ((a,0)+z) := by
  unfold coordinateHadamard
  congr 1
  funext s
  rw [fderiv_comp_add_left]
  congr 1
  simp only [coordinateContraction_apply,Prod.fst_add,Prod.snd_add,zero_add]
  simp only [Prod.mk_add_mk,zero_add]

 theorem coordinateHadamard_analyticAt_axis {f : E × ℂ → ℂ} (a : E)
    (hf : AnalyticAt ℂ f (a,0)) : AnalyticAt ℂ (coordinateHadamard f) (a,0) := by
  have ht : AnalyticAt ℂ (fun w => f ((a,0)+w)) 0 :=
    hf.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  have hq := coordinateHadamard_analyticAt ht
  have hinner : AnalyticAt ℂ (fun w : E × ℂ => w-(a,0)) (a,0) := analyticAt_id.sub analyticAt_const
  have hh := hq.comp_of_eq hinner (sub_self (a,0))
  convert hh using 1
  funext w
  simp only [Function.comp_apply]
  rw [coordinateHadamard_axis_translate]
  congr 1
  abel

/-- Fundamental theorem of calculus on the actual whole coordinate segment. -/
theorem coordinateHadamard_identity_on_segment {f : E × ℂ → ℂ} (z : E × ℂ)
    (hf : ∀ s : ℝ, s∈Icc 0 1 → AnalyticAt ℂ f (coordinateContraction s z)) :
    f z-f (z.1,0)=z.2*coordinateHadamard f z := by
  let g : E × ℂ → ℂ := fun z => fderiv ℂ f z (0,1)
  let L : ((E × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,1)
  have hg (s : ℝ) (hs : s∈Icc 0 1) : AnalyticAt ℂ g (coordinateContraction s z) := by
    convert! ((L.analyticAt _).comp (hf s hs).fderiv) using 1
  have hcurve : Continuous (fun s : ℝ => coordinateContraction s z) := by
    simp only [coordinateContraction_apply]
    fun_prop
  have hc : ContinuousOn (fun s : ℝ => g (coordinateContraction s z)) (Icc 0 1) := by
    intro s hs
    exact ((hg s hs).continuousAt.comp (f := fun u : ℝ => coordinateContraction u z)
      hcurve.continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (fun s : ℝ => z.2*g (coordinateContraction s z)) volume 0 1 :=
    (hc.const_mul z.2).intervalIntegrable_of_Icc (by norm_num)
  have hd (s : ℝ) (hs : s∈uIcc 0 1) :
      HasDerivAt (fun u : ℝ => f (z.1,(u:ℂ)*z.2)) (z.2*g (coordinateContraction s z)) s := by
    have hs' : s∈Icc 0 1 := by simpa using hs
    have hfa : DifferentiableAt ℂ f (z.1,(s:ℂ)*z.2) := by simpa using (hf s hs').differentiableAt
    have hline : HasDerivAt (fun u : ℂ => (z.1,u*z.2)) (0,z.2) (s:ℂ) := by
      simpa using (hasDerivAt_const (s:ℂ) z.1).prodMk ((hasDerivAt_id (s:ℂ)).mul_const z.2)
    have h := (hfa.hasFDerivAt.comp_hasDerivAt (f := fun u : ℂ => (z.1,u*z.2)) (s:ℂ) hline).comp_ofReal
    have heval : fderiv ℂ f (z.1,(s:ℂ)*z.2) ((0:E),z.2)=z.2*g (coordinateContraction s z) := by
      rw [show ((0:E),z.2)=z.2 • ((0:E),(1:ℂ)) by simp,map_smul]
      simp only [g,coordinateContraction_apply,smul_eq_mul]
    rw [heval] at h
    convert! h using 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← integral_Icc_eq_integral_Ioc] at h
  simpa [coordinateHadamard,g] using h.symm

end
end IsingBulk.Anisotropic.NegativeNormalForm
