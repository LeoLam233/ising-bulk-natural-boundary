import IsingBulk.Anisotropic.NegativeCycles.SpatialCutoff

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set Filter Metric
open scoped BigOperators Topology

/-- One on the homotopy interval, supported in its fixed enlargement. -/
def timeBump : ContDiffBump (0:ℝ) := ⟨3/4,1,by norm_num,by norm_num⟩
def cylinderCutoff {n : ℕ} (b : ContDiffBump (0:ℝ)) (x : ParameterSpace n) : ℝ :=
  timeBump (x 0-1/2)*spatialCutoff b (fun i => x i.succ)

theorem cylinderCutoff_contDiff {n : ℕ} (b : ContDiffBump (0:ℝ)) (k : ℕ∞) :
    ContDiff ℝ k (@cylinderCutoff n b) := by
  unfold cylinderCutoff
  exact (timeBump.contDiff.comp (by fun_prop)).mul
    ((spatialCutoff_contDiff b k).comp (by fun_prop))

theorem timeBump_one {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : timeBump (t-1/2)=1 := by
  apply timeBump.one_of_mem_closedBall
  simp only [mem_closedBall,Real.dist_eq,sub_zero,timeBump]
  rw [abs_le]
  constructor <;> linarith [ht.1,ht.2]

theorem cylinderCutoff_on_interval {n : ℕ} (b : ContDiffBump (0:ℝ))
    {x : ParameterSpace n} (hx : x 0∈Icc (0:ℝ) 1) :
    cylinderCutoff b x=spatialCutoff b (fun i => x i.succ) := by
  unfold cylinderCutoff
  rw [timeBump_one hx,one_mul]

theorem cylinderCutoff_eventually_one {n : ℕ} (b : ContDiffBump (0:ℝ))
    {x : ParameterSpace n} (hx : x 0∈Icc (0:ℝ) 1)
    (hq : squaredRadius (fun i => x i.succ)<b.rIn) :
    cylinderCutoff b=ᶠ[𝓝 x] 1 := by
  have ht : x 0-1/2∈ball (0:ℝ) timeBump.rIn := by
    simp only [mem_ball,Real.dist_eq,sub_zero,timeBump]
    rw [abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  have htcont : Continuous (fun y : ParameterSpace n => y 0-1/2) := (continuous_apply 0).sub continuous_const
  have hscont : Continuous (fun y : ParameterSpace n => fun i : Fin n => y i.succ) := continuous_pi (fun i => continuous_apply i.succ)
  have he := (timeBump.eventuallyEq_one_of_mem_ball ht).comp_tendsto
    (htcont.tendsto x)
  have hs := (spatialCutoff_eventually_one b hq).comp_tendsto
    (hscont.tendsto x)
  filter_upwards [he,hs] with y hy hsy
  change timeBump (y 0-1/2)*spatialCutoff b (fun i => y i.succ)=1
  change timeBump (y 0-1/2)=1 at hy
  change spatialCutoff b (fun i => y i.succ)=1 at hsy
  rw [hy,hsy,one_mul]

theorem cylinderCutoff_error_inner_zero {n : ℕ} (b : ContDiffBump (0:ℝ))
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    {x : ParameterSpace n} (hx : x 0∈Icc (0:ℝ) 1)
    (hq : squaredRadius (fun i => x i.succ)<b.rIn) :
    cutoffError (cylinderCutoff b) ω x=0 := by
  have hd : fderiv ℝ (cylinderCutoff b) x=0 := by
    rw [(cylinderCutoff_eventually_one b hx hq).fderiv_eq]
    simp
  simp [cutoffError,hd]


/-- The cutoff only asks for analytic control on a fixed enlarged cylinder. -/
theorem cylinderCutoff_tsupport_subset {n : ℕ} (b : ContDiffBump (0:ℝ)) :
    tsupport (@cylinderCutoff n b) ⊆
      {x | x 0∈Icc (-1/2:ℝ) (3/2) ∧ squaredRadius (fun i => x i.succ)≤b.rOut} := by
  apply closure_minimal
  · intro x hx
    have hn : cylinderCutoff b x≠0 := hx
    change timeBump (x 0-1/2)*spatialCutoff b (fun i => x i.succ)≠0 at hn
    have ht : timeBump (x 0-1/2)≠0 := left_ne_zero_of_mul hn
    have hs : spatialCutoff b (fun i => x i.succ)≠0 := right_ne_zero_of_mul hn
    have hbt : x 0-1/2∈ball (0:ℝ) timeBump.rOut := by
      rw [←timeBump.support_eq]
      exact ht
    have ha : |x 0-1/2|<1 := by simpa [Real.dist_eq,timeBump] using hbt
    have hq : squaredRadius (fun i => x i.succ)<b.rOut := by
      by_contra h
      exact hs (spatialCutoff_zero b (le_of_not_gt h))
    rw [abs_lt] at ha
    exact ⟨⟨by linarith [ha.1],by linarith [ha.2]⟩,hq.le⟩
  · exact (isClosed_Icc.preimage (continuous_apply 0)).inter
      (isClosed_le ((squaredRadius_contDiff (n := n) 0).continuous.comp (continuous_pi (fun i : Fin n => continuous_apply i.succ))) continuous_const)

theorem cylinderCutoff_zero_of_coordinate {n : ℕ} (b : ContDiffBump (0:ℝ))
    {x : ParameterSpace n} (i : Fin n) (hi : b.rOut≤(x i.succ)^2) :
    cylinderCutoff b x=0 := by
  have hq : b.rOut≤squaredRadius (fun j => x j.succ) := hi.trans
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j.succ)) (Finset.mem_univ i))
  simp [cylinderCutoff,spatialCutoff_zero b hq]

end IsingBulk.Anisotropic.NegativeCycles
