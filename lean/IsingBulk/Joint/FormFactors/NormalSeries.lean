import IsingBulk.Joint.FormFactors.CompactIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Genuine multivariable Weierstrass theorem and normal derivative estimates.
The proof uses complex-line Cauchy bounds for the full Fréchet derivative. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem norm_fderiv_le_of_ball_bound {f : E → G} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : E} {r C : ℝ} (hr : 0 < r)
    (hball : closedBall x r ⊆ U) (hC : 0 ≤ C)
    (hb : ∀ y ∈ closedBall x r, ‖f y‖ ≤ C) : ‖fderiv ℂ f x‖ ≤ C/r := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC hr.le)
  intro v hv
  let line : ℂ → E := fun t => x+t • v
  have hline : Differentiable ℂ line := (differentiable_const x).add (differentiable_id.smul_const v)
  have hmap : MapsTo line (closedBall (0:ℂ) r) (closedBall x r) := by
    intro t ht
    simpa only [line,mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,hv,mul_one,
      sub_zero] using ht
  have hg : DiffContOnCl ℂ (f ∘ line) (ball (0:ℂ) r) := by
    constructor
    · exact hf.comp (hline.differentiableOn) (fun t ht => hball (hmap (ball_subset_closedBall ht)))
    · exact hf.continuousOn.comp hline.continuous.continuousOn
        (fun t ht => hball (hmap (closure_ball_subset_closedBall ht)))
  have hestimate := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hr hg
    (fun t ht => hb _ (hmap (sphere_subset_closedBall ht)))
  have hx : x ∈ U := hball (mem_closedBall_self hr.le)
  have hdl : HasDerivAt line v 0 := by
    simpa [line] using
      ((hasDerivAt_id (0:ℂ)).smul_const v).const_add x
  have hfx : HasFDerivAt f (fderiv ℂ f x) (line 0) := by
    simpa [line] using (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hd := hfx.comp_hasDerivAt (0:ℂ) hdl
  simpa only [iteratedDeriv_one,hd.deriv,Nat.factorial_one,Nat.cast_one,one_mul,pow_one] using hestimate

theorem normalSeries_local_derivative_bound {f : ℕ → E → G} {U : Set E}
    (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    {M : ℕ → ℝ} (hM : Summable M) (hb : ∀ i x, x ∈ U → ‖f i x‖ ≤ M i)
    {x : E} (hx : x ∈ U) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ IsPreconnected V ∧ V ⊆ U ∧
      ∃ M' : ℕ → ℝ, Summable M' ∧ ∀ i y, y ∈ V → ‖fderiv ℂ (f i) y‖ ≤ M' i := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hε2 : 0 < ε/2 := half_pos hε
  have hhalf : ball x (ε/2) ⊆ U := (ball_subset_ball (by linarith)).trans hεU
  refine ⟨ball x (ε/2),ball_mem_nhds x hε2,isOpen_ball,(convex_ball x _).isPreconnected,
    hhalf,fun i => M i/(ε/2),hM.div_const _,?_⟩
  intro i y hy
  have hball : closedBall y (ε/2) ⊆ U := by
    intro z hz
    apply hεU
    have hdist := dist_triangle z y x
    have hz' : dist z y ≤ ε/2 := hz
    have hy' : dist y x < ε/2 := hy
    change dist z x < ε
    linarith
  exact norm_fderiv_le_of_ball_bound hU (hf i) hε2 hball
    ((norm_nonneg _).trans (hb i x hx)) (fun z hz => hb i z (hball hz))

/-- Uniform summable bounds plus literal joint complex smooth summands imply
joint complex smoothness of their complete infinite sum in every finite order. -/
theorem normalSeries_contDiffAt (n : ℕ) {f : ℕ → E → G} {U : Set E}
    (hU : IsOpen U) (hf : ∀ i (j : ℕ) x, x ∈ U → ContDiffAt ℂ j (f i) x)
    {M : ℕ → ℝ} (hM : Summable M) (hb : ∀ i x, x ∈ U → ‖f i x‖ ≤ M i)
    {x : E} (hx : x ∈ U) : ContDiffAt ℂ n (fun y => ∑' i, f i y) x := by
  induction n generalizing G U M x with
  | zero =>
    exact contDiffAt_zero.mpr ⟨U,hU.mem_nhds hx,
      continuousOn_tsum (fun i y hy => (hf i 0 y hy).continuousAt.continuousWithinAt) hM hb⟩
  | succ n ih =>
    have hdiff : ∀ i, DifferentiableOn ℂ (f i) U :=
      fun i y hy => (hf i 1 y hy).differentiableAt_one.differentiableWithinAt
    obtain ⟨V,hVx,hV,hVc,hVU,M',hM',hbound⟩ := normalSeries_local_derivative_bound hU hdiff hM hb hx
    have hxV : x ∈ V := mem_of_mem_nhds hVx
    have hdf : ∀ i (j : ℕ) y, y ∈ V → ContDiffAt ℂ j (fderiv ℂ (f i)) y := by
      intro i j y hy
      exact (hf i (j+1) y (hVU hy)).fderiv_right_succ
    have hsum : Summable (fun i => f i x) := .of_norm_bounded hM (fun i => hb i x hx)
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 from rfl,
      contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun y => ∑' i, fderiv ℂ (f i) y, ?_, ?_⟩
    · refine ⟨V,hVx,fun y hy => ?_⟩
      exact hasFDerivAt_tsum_of_isPreconnected hM' hV hVc
        (fun i z hz => (hdiff i |>.differentiableAt (hU.mem_nhds (hVU hz))).hasFDerivAt)
        hbound hxV hsum hy
    · exact ih hV hdf hM' hbound hxV

end
end IsingBulk.Joint.FormFactors
