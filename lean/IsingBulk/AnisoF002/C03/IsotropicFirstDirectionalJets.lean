import IsingBulk.AnisoF002.C03.IsotropicFirstJointFill
import IsingBulk.AnisoF002.C03.IsotropicFirstPhysicalMargin

/-!
# Uniform bounds for every actual first-chart parameter derivative

The full complex quotient is analytic jointly in the temperature, scale,
weight, and shape direction. Its actual temperature derivatives are
continuous on the compact set of weighted directions. This gives one
bound for each derivative order before the radial scale is chosen.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem parameter_zero_jet_continuous_pullback {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace X]
    {f : ℂ × E → ℂ} {g : X → E} {p : X}
    (hf : AnalyticAt ℂ f (0, g p)) (hg : ContinuousAt g p) (j : ℕ) :
    ContinuousAt (fun x => iteratedDeriv j (fun v => f (v, g x)) 0) p := by
  have hj : AnalyticAt ℂ
      (fun q : ℂ × E => iteratedDeriv j (fun v => f (v, q.2)) q.1) (0, g p) :=
    parameterIteratedDeriv_analyticAt hf j
  exact hj.continuousAt.comp_of_eq (continuousAt_const.prodMk hg) rfl

def isotropicFirstDirectionalJet {N : ℕ} (α : ℝ) (σ : ℂ) (j : ℕ)
    (q : ℝ × (ℝ × (Fin N → ℝ))) : ℂ :=
  iteratedDeriv j (fun v => isotropicFirstDirectionalRatio α σ
    (v, ((q.1 : ℂ), ((q.2.1 : ℂ), fun i => (q.2.2 i : ℂ))))) 0

theorem isotropicFirstDirectionalJet_continuousAt {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (j : ℕ)
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ isotropicFirstDirections N) :
    ContinuousAt (isotropicFirstDirectionalJet α σ j) (0, p) := by
  have hm : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
      ((q.1 : ℂ), ((q.2.1 : ℂ), fun i => (q.2.2 i : ℂ)))) (0, p) := by fun_prop
  change ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
    iteratedDeriv j (fun v => isotropicFirstDirectionalRatio α σ
      (v, ((q.1 : ℂ), ((q.2.1 : ℂ), fun i => (q.2.2 i : ℂ))))) 0) (0, p)
  exact parameter_zero_jet_continuous_pullback
    (g := fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
      ((q.1 : ℂ), ((q.2.1 : ℂ), fun i => (q.2.2 i : ℂ)))) (p := (0, p))
    (isotropicFirstDirectionalRatio_analytic hN hα hhalf σ hp) hm j

theorem exists_uniform_isotropic_first_directional_jets {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (j : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ s : ℝ, |s| < δ →
      ∀ p ∈ isotropicFirstDirections N, ‖isotropicFirstDirectionalJet α σ j (s, p)‖ ≤ C := by
  have hc : ContinuousOn (fun p : ℝ × (Fin N → ℝ) =>
      isotropicFirstDirectionalJet α σ j (0, p)) (isotropicFirstDirections N) := by
    intro p hp
    exact ((isotropicFirstDirectionalJet_continuousAt hN hα hhalf σ j hp).comp_of_eq
      (continuousAt_const.prodMk continuousAt_id) rfl).continuousWithinAt
  obtain ⟨M, hM⟩ := (isotropicFirstDirections_compact N).exists_bound_of_continuousOn hc
  let C := |M| + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, ∀ p ∈ isotropicFirstDirections N,
      ‖isotropicFirstDirectionalJet α σ j (s, p)‖ < C := by
    apply (isotropicFirstDirections_compact N).eventually_forall_of_forall_eventually
    intro p hp
    change ∀ᶠ q : ℝ × (ℝ × (Fin N → ℝ)) in 𝓝 (0, p),
      ‖isotropicFirstDirectionalJet α σ j q‖ < C
    have hb : ‖isotropicFirstDirectionalJet α σ j (0, p)‖ < C := by
      have hh := hM p hp
      dsimp only [C]
      linarith [le_abs_self M]
    exact (isotropicFirstDirectionalJet_continuousAt hN hα hhalf σ j hp).norm.eventually
      (Iio_mem_nhds hb)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro s hs p hp
  exact (hh (by simpa only [Real.dist_eq, sub_zero] using hs) p hp).le

end
end IsingBulk.AnisoF002.Isotropic
