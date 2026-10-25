import IsingBulk.Joint.Geometry.Definitions
import IsingBulk.Anisotropic.Final.RealIntervalUniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import IsingBulk.Joint.FormFactors.NormalSeries
import Mathlib.Topology.Connected.Clopen

/-! Several-variable identity from actual complex Fréchet differentiability.
The local propagation is proved on complex lines, so it does not assume the
joint analytic-continuation conclusion under a named predicate. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holomorphic_eqOn_of_germ {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f g : E → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {a : E} (ha : a ∈ U) (he : f =ᶠ[𝓝 a] g) : EqOn f g U := by
  let P : Set E := {x | f =ᶠ[𝓝 x] g}
  have hP : IsOpen P := isOpen_setOfPred_eventually_nhds
  have hprop : closure P ∩ U ⊆ P := by
    rintro x ⟨hxc,hxU⟩
    obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
    have hr : 0 < ε/5 := by positivity
    obtain ⟨b,hbx,hbP⟩ := mem_closure_iff.mp hxc (ball x (ε/5)) isOpen_ball (mem_ball_self hr)
    change f =ᶠ[𝓝 x] g
    filter_upwards [ball_mem_nhds x hr] with y hy
    let l : ℂ → E := fun t => b+t • (y-b)
    have hl : Differentiable ℂ l := (differentiable_const b).add
      (differentiable_id.smul_const (y-b))
    have hmap : MapsTo l (ball (0:ℂ) 2) U := by
      intro t ht
      apply hεU
      have hb : ‖b-x‖ < ε/5 := by simpa only [mem_ball,dist_eq_norm] using hbx
      have hy' : ‖y-x‖ < ε/5 := by simpa only [mem_ball,dist_eq_norm] using hy
      have ht' : ‖t‖ < 2 := by simpa only [mem_ball,dist_eq_norm,sub_zero] using ht
      have hya : ‖y-b‖ < 2*(ε/5) := by
        have hh := dist_triangle y x b
        simp only [dist_eq_norm,norm_sub_rev x b] at hh
        linarith
      have hbound : ‖l t-x‖ ≤ ‖b-x‖+‖t‖*‖y-b‖ := by
        calc
          ‖l t-x‖ = ‖(b-x)+t • (y-b)‖ := by congr 1; dsimp [l]; abel
          _ ≤ ‖b-x‖+‖t • (y-b)‖ := norm_add_le _ _
          _ = _ := by rw [norm_smul]
      change dist (l t) x < ε
      rw [dist_eq_norm]
      have hh : ‖t‖*‖y-b‖ < 2*(2*(ε/5)) :=
        mul_lt_mul_of_nonneg_of_pos ht' hya.le (norm_nonneg _) (by positivity)
      linarith
    have hfa : AnalyticOnNhd ℂ (f ∘ l) (ball (0:ℂ) 2) :=
      (hf.comp hl.differentiableOn hmap).analyticOnNhd isOpen_ball
    have hga : AnalyticOnNhd ℂ (g ∘ l) (ball (0:ℂ) 2) :=
      (hg.comp hl.differentiableOn hmap).analyticOnNhd isOpen_ball
    have h0 : l 0 = b := by simp [l]
    have hge : f ∘ l =ᶠ[𝓝 (0:ℂ)] g ∘ l :=
      (show f =ᶠ[𝓝 b] g from hbP).comp_tendsto (h0 ▸ hl.continuous.continuousAt.tendsto)
    have hid := hfa.eqOn_of_preconnected_of_eventuallyEq hga (convex_ball _ _).isPreconnected
      (mem_ball_self (by norm_num : (0:ℝ)<2)) hge
    have h1 := hid (show (1:ℂ) ∈ ball 0 2 by norm_num [mem_ball,dist_eq_norm])
    simpa [Function.comp_apply,l] using h1
  have hsub : U ⊆ P := hUc.subset_of_closure_inter_subset hP ⟨a,ha,he⟩ hprop
  exact fun x hx => (hsub hx).eq_of_nhds

/-- A real open rectangle is a uniqueness set in a complex product domain.
The two scalar identity-theorem applications are explicit. -/
theorem holomorphic_eqOn_product_of_real_rectangle
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    {f g : Coupling → ℂ} (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (hg : DifferentiableOn ℂ g (U ×ˢ V))
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hu : ∀ x ∈ Ioo a b, (x:ℂ) ∈ U) (hv : ∀ y ∈ Ioo c d, (y:ℂ) ∈ V)
    (he : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, f ((x:ℂ),(y:ℂ))=g ((x:ℂ),(y:ℂ))) :
    EqOn f g (U ×ˢ V) := by
  have hfst (y : ℂ) (hy : y ∈ V) :
      AnalyticOnNhd ℂ (fun z => f (z,y)) U ∧ AnalyticOnNhd ℂ (fun z => g (z,y)) U := by
    have hp : Differentiable ℂ (fun z : ℂ => (z,y)) := differentiable_id.prodMk (differentiable_const y)
    exact ⟨(hf.comp hp.differentiableOn (fun z hz => ⟨hz,hy⟩)).analyticOnNhd hU,
      (hg.comp hp.differentiableOn (fun z hz => ⟨hz,hy⟩)).analyticOnNhd hU⟩
  have hrow (y : ℝ) (hy : y ∈ Ioo c d) : ∀ z ∈ U, f (z,(y:ℂ))=g (z,(y:ℂ)) :=
    Anisotropic.analytic_eqOn_of_real_interval (hfst _ (hv y hy)).1 (hfst _ (hv y hy)).2
      hUc hab hu (fun x hx => he x hx y hy)
  rintro ⟨z,w⟩ ⟨hz,hw⟩
  have hp : Differentiable ℂ (fun w : ℂ => (z,w)) := (differentiable_const z).prodMk differentiable_id
  exact Anisotropic.analytic_eqOn_of_real_interval
    ((hf.comp hp.differentiableOn (fun w hw => ⟨hz,hw⟩)).analyticOnNhd hV)
    ((hg.comp hp.differentiableOn (fun w hw => ⟨hz,hw⟩)).analyticOnNhd hV)
    hVc hcd hv (fun y hy => hrow y hy z hz) hw

end
end IsingBulk.Joint.FormFactors
