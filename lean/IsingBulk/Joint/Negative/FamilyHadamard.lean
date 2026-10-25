import IsingBulk.Joint.Negative.CompactAnalyticBounds
import IsingBulk.Anisotropic.NegativeNormalForm.HadamardFullDomain

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem coordinateHadamard_identity_axis {f : E × ℂ→ℂ} (a : E)
    (hf : AnalyticAt ℂ f (a,0)) :
    ∀ᶠz : E × ℂ in 𝓝 (a,0),f z-f (z.1,0)=z.2*coordinateHadamard f z := by
  have ht : AnalyticAt ℂ (fun w=>f ((a,0)+w)) 0 :=
    hf.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  have hi := coordinateHadamard_identity ht
  have hc : Tendsto (fun w : E × ℂ=>w-(a,0)) (𝓝 (a,0)) (𝓝 0) := by
    have hh : ContinuousAt (fun w : E × ℂ=>w-(a,0)) (a,0) := by fun_prop
    simpa using hh.tendsto
  filter_upwards [hc.eventually hi] with z hz
  rw [coordinateHadamard_axis_translate] at hz
  simpa only [Prod.fst_sub,Prod.snd_sub,sub_zero,Prod.mk_add_mk,add_sub_cancel,zero_add] using hz

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem coordinateHadamard_slice (f : (X × E) × ℂ→ℂ) (x : X) (eta : E) (v : ℂ)
    (hf : ∀s : ℝ,s∈Icc 0 1 → AnalyticAt ℂ f ((x,eta),(s:ℂ)*v)) :
    coordinateHadamard f ((x,eta),v)=
      coordinateHadamard (fun q : X × ℂ=>f ((q.1,eta),q.2)) (x,v) := by
  unfold coordinateHadamard
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp only [coordinateContraction_apply]
  have hfull := ((hf s hs).differentiableAt.hasFDerivAt.comp_hasDerivAt ((s:ℂ)*v)
    ((hasDerivAt_const ((s:ℂ)*v) (x,eta)).prodMk (hasDerivAt_id ((s:ℂ)*v)))).deriv
  have hslice : AnalyticAt ℂ (fun q : X × ℂ=>f ((q.1,eta),q.2)) (x,(s:ℂ)*v) :=
    (hf s hs).comp (f:=fun q : X × ℂ=>((q.1,eta),q.2))
      ((analyticAt_fst.prod analyticAt_const).prod analyticAt_snd)
  have hpart := (hslice.differentiableAt.hasFDerivAt.comp_hasDerivAt ((s:ℂ)*v)
    ((hasDerivAt_const ((s:ℂ)*v) x).prodMk (hasDerivAt_id ((s:ℂ)*v)))).deriv
  exact hfull.symm.trans hpart

/-- The actual scalar-slice Hadamard integral depends holomorphically on the
independent complex family parameter. -/
theorem family_coordinateHadamard_analyticAt (f : (X × E) × ℂ→ℂ) (eta : E)
    (hf : AnalyticAt ℂ f ((0,eta),0)) :
    AnalyticAt ℂ (fun q : (X × ℂ) × E=>
      coordinateHadamard (fun p : X × ℂ=>f ((p.1,q.2),p.2)) q.1) ((0,0),eta) := by
  have hfull : AnalyticAt ℂ (fun q : (X × ℂ) × E=>coordinateHadamard f ((q.1.1,q.2),q.1.2))
      ((0,0),eta) := (coordinateHadamard_analyticAt_axis (0,eta) hf).comp_of_eq
    (f:=fun q : (X × ℂ) × E=>((q.1.1,q.2),q.1.2))
    (((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd).prod
      (analyticAt_snd.comp analyticAt_fst)) rfl
  apply hfull.congr
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  have hc : ContinuousAt (fun q : (X × ℂ) × E=>((q.1.1,q.2),q.1.2)) ((0,0),eta) := by fun_prop
  filter_upwards [hc.tendsto.eventually (ball_mem_nhds ((0,eta),(0:ℂ)) hr)] with q hq
  apply coordinateHadamard_slice
  intro s hs
  apply hball
  simp only [mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero] at hq ⊢
  change max (max ‖q.1.1‖ ‖q.2-eta‖) ‖(s:ℂ)*q.1.2‖<r
  have hnorm : ‖(s:ℂ)*q.1.2‖≤‖q.1.2‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  exact (max_le_max le_rfl hnorm).trans_lt hq

theorem family_coordinateHadamard_identity (f : (X × E) × ℂ→ℂ) (eta : E)
    (hf : AnalyticAt ℂ f ((0,eta),0)) :
    ∀ᶠq : (X × ℂ) × E in 𝓝 ((0,0),eta),
      f ((q.1.1,q.2),q.1.2)-f ((q.1.1,q.2),0)=q.1.2*
        coordinateHadamard (fun p : X × ℂ=>f ((p.1,q.2),p.2)) q.1 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  have hc : ContinuousAt (fun q : (X × ℂ) × E=>((q.1.1,q.2),q.1.2)) ((0,0),eta) := by fun_prop
  filter_upwards [hc.tendsto.eventually (ball_mem_nhds ((0,eta),(0:ℂ)) hr)] with q hq
  apply coordinateHadamard_identity_on_segment (f:=fun p : X × ℂ=>f ((p.1,q.2),p.2)) q.1
  intro s hs
  have hfull : AnalyticAt ℂ f ((q.1.1,q.2),(s:ℂ)*q.1.2) := by
    apply hball
    simp only [mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero] at hq ⊢
    change max (max ‖q.1.1‖ ‖q.2-eta‖) ‖(s:ℂ)*q.1.2‖<r
    have hnorm : ‖(s:ℂ)*q.1.2‖≤‖q.1.2‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    exact (max_le_max le_rfl hnorm).trans_lt hq
  rw [coordinateContraction_apply]
  change AnalyticAt ℂ (fun p : X × ℂ=>f ((p.1,q.2),p.2)) (q.1.1,(s:ℂ)*q.1.2)
  exact hfull.comp (f:=fun p : X × ℂ=>((p.1,q.2),p.2))
    ((analyticAt_fst.prod analyticAt_const).prod analyticAt_snd)

end
end IsingBulk.Joint.Negative