import IsingBulk.Anisotropic.NegativeCycles.CutoffGradient

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set Filter Metric
open scoped Topology

theorem shapeCylinderCutoff_fderiv {n : ℕ} (b : ContDiffBump (0:ℝ))
    (x : ParameterSpace n) (hx : x 0∈Icc (0:ℝ) 1) :
    fderiv ℝ (shapeCylinderCutoff b) x=
      (fderiv ℝ (shapeSpatialCutoff b) (fun i => x i.succ)).comp
        (ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj i.succ)) := by
  have ht : x 0-1/2∈ball (0:ℝ) timeBump.rIn := by
    simp only [mem_ball,Real.dist_eq,sub_zero,timeBump]
    rw [abs_lt]; constructor <;> linarith [hx.1,hx.2]
  have htcont : Continuous (fun y : ParameterSpace n => y 0-1/2) := (continuous_apply 0).sub continuous_const
  have he := (timeBump.eventuallyEq_one_of_mem_ball ht).comp_tendsto (htcont.tendsto x)
  have heq : shapeCylinderCutoff b=ᶠ[𝓝 x] (fun y => shapeSpatialCutoff b (fun i => y i.succ)) := by
    filter_upwards [he] with y hy
    change timeBump (y 0-1/2)*shapeSpatialCutoff b (fun i => y i.succ)=_
    change timeBump (y 0-1/2)=1 at hy
    rw [hy,one_mul]
  rw [heq.fderiv_eq]
  let S : ParameterSpace n→L[ℝ](Fin n→ℝ) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ)
  have hsp : HasFDerivAt (shapeSpatialCutoff b) (fderiv ℝ (shapeSpatialCutoff b) (S x)) (S x) :=
    ((shapeSpatialCutoff_contDiff b 1).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  exact (hsp.comp x (S.hasFDerivAt (x := x))).fderiv

/-- One cutoff-gradient constant works in every particle dimension. -/
theorem shapeCylinderCutoff_uniform_gradient (b : ContDiffBump (0:ℝ)) :
    ∃K : ℝ,0≤K ∧ ∀n : ℕ, ∀x : ParameterSpace n, x 0∈Icc (0:ℝ) 1 →
      constrainedSquaredRadius (fun i => x i.succ)≤b.rOut →
      ∀i : Fin (n+1), ‖fderiv ℝ (shapeCylinderCutoff b) x (Pi.single i 1)‖≤K := by
  obtain ⟨K,hK⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) b.rOut)).exists_bound_of_continuousOn
    (b.contDiff.continuous_deriv_one.continuousOn)
  let M := max K 0
  have hM : 0≤M := le_max_right _ _
  refine ⟨M*(4*Real.sqrt b.rOut),by positivity,?_⟩
  intro n x hx hq i
  rw [shapeCylinderCutoff_fderiv b x hx,ContinuousLinearMap.comp_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · have he : (ContinuousLinearMap.pi (fun j : Fin n => (ContinuousLinearMap.proj j.succ : ParameterSpace n→L[ℝ]ℝ)))
        (Pi.single (0:Fin (n+1)) (1:ℝ))=0 := by ext j; simp
    rw [he,map_zero,norm_zero]
    positivity
  · have he : (ContinuousLinearMap.pi (fun k : Fin n => (ContinuousLinearMap.proj k.succ : ParameterSpace n→L[ℝ]ℝ)))
        (Pi.single j.succ (1:ℝ))=Pi.single j (1:ℝ) := by
      ext k
      by_cases h : k=j
      · subst k; simp
      · simp [h,Fin.succ_inj]
    rw [he]
    apply shapeSpatialCutoff_gradient_bound b (Real.sqrt_nonneg _) hM
    · simpa only [Real.sq_sqrt b.rOut_pos.le] using hq
    · exact (hK _ ⟨constrainedSquaredRadius_nonneg _,hq⟩).trans (le_max_left _ _)

end IsingBulk.Anisotropic.NegativeCycles
