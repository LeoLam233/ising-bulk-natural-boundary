import IsingBulk.Joint.Final.HolomorphicExtension
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology

namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Several-variable holomorphic uniqueness on a convex open set, proved by
actual one-complex-variable line restrictions, not a multivariable analytic premise. -/
theorem holomorphic_eqOn_convex {U : Set Coupling} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f g : Coupling → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : Coupling} (hx : x ∈ U) (he : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  intro y hy
  let L : ℂ →ₗ[ℂ] Coupling := (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (y-x)
  let line : ℂ →ᵃ[ℝ] Coupling := AffineMap.const ℝ ℂ x + (L.restrictScalars ℝ).toAffineMap
  have hline : ∀ t : ℂ, line t = x+t•(y-x) := fun _ => rfl
  have hl0 : line 0 = x := by rw [hline]; simp
  have hl1 : line 1 = y := by rw [hline]; simp
  have hld : Differentiable ℂ line := by change Differentiable ℂ (fun t : ℂ => x+t•(y-x)); fun_prop
  have ho : IsOpen (line ⁻¹' U) := hU.preimage hld.continuous
  have hc : IsPreconnected (line ⁻¹' U) := (hconv.affine_preimage line).isPreconnected
  have hfa : AnalyticOnNhd ℂ (f ∘ line) (line ⁻¹' U) :=
    (hf.comp hld.differentiableOn (fun _ h => h)).analyticOnNhd ho
  have hga : AnalyticOnNhd ℂ (g ∘ line) (line ⁻¹' U) :=
    (hg.comp hld.differentiableOn (fun _ h => h)).analyticOnNhd ho
  have hlt : Tendsto line (𝓝 (0 : ℂ)) (𝓝 x) := by
    rw [←hl0]
    exact hld.continuous.tendsto 0
  have hfg : f ∘ line =ᶠ[𝓝 (0 : ℂ)] g ∘ line := hlt.eventually he
  have hh := hfa.eqOn_of_preconnected_of_eventuallyEq hga hc
    (show (0 : ℂ) ∈ line ⁻¹' U by simpa only [mem_preimage,hl0] using hx) hfg
    (show (1 : ℂ) ∈ line ⁻¹' U by simpa only [mem_preimage,hl1] using hy)
  simpa only [Function.comp_apply,hl1] using hh

/-- The ordinary holomorphic identity theorem on connected open subsets of C². -/
theorem holomorphic_eqOn_preconnected {U : Set Coupling} (hU : IsOpen U)
    (hc : IsPreconnected U) {f g : Coupling → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : Coupling} (hx : x ∈ U) (he : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let G : Set Coupling := interior {z | f z = g z}
  have hxG : x ∈ G := mem_interior_iff_mem_nhds.mpr he
  have hsub : U ⊆ G := by
    apply hc.subset_of_closure_inter_subset isOpen_interior ⟨x,hx,hxG⟩
    rintro z ⟨hz,hzU⟩
    obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU z hzU
    obtain ⟨w,hwball,hwG⟩ := mem_closure_iff.mp hz (ball z r) isOpen_ball (mem_ball_self hr)
    have hfg : EqOn f g (ball z r) := holomorphic_eqOn_convex isOpen_ball (convex_ball z r)
      (hf.mono hrU) (hg.mono hrU) hwball (mem_interior_iff_mem_nhds.mp hwG)
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (ball_mem_nhds z hr) hfg)
  intro z hz
  exact (interior_subset (s := {z | f z = g z})) (hsub hz)

end
end IsingBulk.Joint
