import IsingBulk.Anisotropic.RegularEdges.FullPairBound
import Mathlib.Analysis.Complex.Liouville

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology

def edgeOneBody (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (q : ℝ) : ℂ :=
  2*edgeParamRoot b B u q/(S u*(1-(edgeParamRoot b B u q)^2))
def edgeNumerator (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (qs : List ℝ) : ℂ :=
  radialEdgePairProduct b B u 1 qs*(qs.map (edgeOneBody b B S u)).prod

theorem edgeOneBody_continuousAt_zero {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0)
    (hS : ContinuousAt S 0) (hS0 : S 0≠0) (q : ℝ) :
    ContinuousAt (fun x : ℂ × ℝ => edgeOneBody b B S x.1 x.2) (0,q) := by
  have hroot := edgeParamRoot_continuousAt b hc
    (show edgeParamW b B 0 q ∈ continuedRootDomain by simpa using edgeW_domain hb hB q)
  exact (continuousAt_const.mul hroot).div
    ((hS.comp (x := (0,q)) (f := fun x : ℂ × ℝ => x.1) continuousAt_fst).mul
      (continuousAt_const.sub (hroot.pow 2)))
    (mul_ne_zero hS0 (by simpa only [edgeParamRoot_zero,pow_two] using
      edgeRoot_pair_denominator_ne_zero hb hB q q))

theorem edgeOneBody_uniform {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0)
    (hS : ContinuousAt S 0) (hS0 : S 0≠0) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ u in 𝓝 (0:ℂ), ∀ q ∈ Icc (-Real.pi) Real.pi,
      ‖edgeOneBody b B S u q‖≤M := by
  have hcont : ContinuousOn (edgeOneBody b B S 0) (Icc (-Real.pi) Real.pi) := by
    intro q _
    exact ((edgeOneBody_continuousAt_zero hb hB hc hS hS0 q).comp
      (f := fun q : ℝ => ((0:ℂ),q)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let C := max M 0+1
  refine ⟨C,by dsimp [C]; linarith [le_max_right M 0],?_⟩
  have he : ∀ᶠ u in 𝓝 (0:ℂ), ∀ q ∈ Icc (-Real.pi) Real.pi,
      ‖edgeOneBody b B S u q‖<C := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro q hq
    apply (edgeOneBody_continuousAt_zero hb hB hc hS hS0 q).norm.eventually_lt continuousAt_const
    exact (hM q hq).trans_lt (by dsimp [C]; linarith [le_max_left M 0])
  filter_upwards [he] with u hu q hq
  exact (hu q hq).le

theorem analyticAt_list_product {α : Type*} (f : ℂ → α → ℂ) (xs : List α) {u : ℂ}
    (hf : ∀ a ∈ xs, AnalyticAt ℂ (fun v => f v a) u) :
    AnalyticAt ℂ (fun v => (xs.map (f v)).prod) u := by
  induction xs with
  | nil => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) u)
  | cons a xs ih =>
    exact (hf a (by simp)).mul (ih (fun c hc => hf c (by simp [hc])))

theorem analyticAt_list_pairProduct (K : ℂ → ℂ → ℂ → ℂ) (xs : List ℂ) {u : ℂ}
    (hK : ∀ a ∈ xs, ∀ c ∈ xs, AnalyticAt ℂ (fun v => K v a c) u) :
    AnalyticAt ℂ (fun v => IsingBulk.Schur.pairProduct (K v) xs) u := by
  induction xs with
  | nil => exact analyticAt_const
  | cons a xs ih =>
    exact (analyticAt_list_product (fun v c => K v a c) xs
      (fun c hc => hK a (by simp) c (by simp [hc]))).mul
      (ih (fun c hc d hd => hK c (by simp [hc]) d (by simp [hd])))

theorem edgeNumerator_analyticAt (b : ℝ) {B S : ℂ → ℂ} {u : ℂ}
    (hB : AnalyticAt ℂ B u) (hS : AnalyticAt ℂ S u) (hS0 : S u≠0)
    (qs : List ℝ) (hdom : ∀ q ∈ qs, edgeParamW b B u q ∈ continuedRootDomain)
    (hd : ∀ q ∈ qs, ∀ t ∈ qs, 1-edgeParamRoot b B u q*edgeParamRoot b B u t≠0) :
    AnalyticAt ℂ (fun v => edgeNumerator b B S v qs) u := by
  have hroot (q : ℝ) (hq : q ∈ qs) := edgeParamRoot_analyticAt b hB (hdom q hq)
  apply AnalyticAt.mul
  · unfold radialEdgePairProduct
    apply analyticAt_list_pairProduct
    intro y hy w hw
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw
    have hq0 : limitingAngle q≠0 := Complex.exp_ne_zero _
    have ht0 : limitingAngle t≠0 := Complex.exp_ne_zero _
    have he (v : ℂ) (q : ℝ) : edgeCircleRoot b B v (radialEdgeY 1 q)=edgeParamRoot b B v q := by
      simp [edgeCircleRoot,edgeParamRoot]
    simp only [edgeCircleCanceledKernel,radialEdgeY_one,edgeCircleRoot,edgeCircleW_unit]
    change AnalyticAt ℂ (fun v => B v*canceledPair (limitingAngle q) (limitingAngle t)
      (edgeParamRoot b B v q) (edgeParamRoot b B v t)) u
    unfold canceledPair
    exact hB.mul (((analyticAt_const.mul (hroot q hq)).mul (hroot t ht)).div
      (analyticAt_const.mul ((analyticAt_const.sub ((hroot q hq).mul (hroot t ht))).pow 2))
      (mul_ne_zero (mul_ne_zero hq0 ht0) (pow_ne_zero 2 (hd q hq t ht))))
  · apply analyticAt_list_product
    intro q hq
    exact (analyticAt_const.mul (hroot q hq)).div
      (hS.mul (analyticAt_const.sub ((hroot q hq).pow 2)))
      (mul_ne_zero hS0 (by simpa only [pow_two] using hd q hq q hq))
end
end IsingBulk.Anisotropic.RegularEdges
