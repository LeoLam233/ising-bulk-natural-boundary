import IsingBulk.Preferred22.SelectedDiscriminant
import IsingBulk.Preferred22.ContourLift

/-! Exact periodic transfer of the selected discriminant estimate to every
real angular configuration, including the unreduced dependent angle. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
set_option maxHeartbeats 800000

lemma preferred_cos_deformed_lift {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin N → ℝ) (i : Fin N) :
    Complex.cos (deformedAngles τ p m (preferredLiftedAngles δ θ) i)=
      Complex.cos (deformedAngles τ p m θ i) := by
  simp only [deformedAngles,Complex.cos_sub,preferred_shift_lift τ δ p m hp hm,
    ←Complex.ofReal_cos,←Complex.ofReal_sin,preferredLiftedAngles,
    preferred_periodic_lift Real.cos Real.cos_periodic,
    preferred_periodic_lift Real.sin Real.sin_periodic]

/-- The c*tau/N discriminant margin holds for every actual constrained or
unconstrained angular representative; there is no range restriction on its
last dependent angle. -/
theorem preferred_selected_discriminant_all_angles (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ i : Fin N,c*τ/(N:ℝ)≤
        ‖(preferredRadialTrace d ε-Complex.cos
          (deformedAngles τ (cappedCanonicalPreferredBump d cap hcap).p
            (cappedCanonicalPreferredBump d cap hcap).m θ i))^2-1‖ := by
  obtain ⟨c,ρ,hc,hρ,hρ1,hbound⟩ := preferred_selected_actual_discriminant d hcap
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw i
  let B := cappedCanonicalPreferredBump d cap hcap
  let θ' := preferredLiftedAngles 0 θ
  have hθ (a : Fin N) : θ' a∈Icc (-Real.pi) Real.pi := by
    have h := toIocMod_mem_Ioc (by positivity : 0<2*Real.pi) (-Real.pi-0) (θ a)
    change θ' a∈Ioc (-Real.pi-0) (-Real.pi-0+2*Real.pi) at h
    constructor <;> linarith [h.1,h.2]
  have hw' : preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ'≠0 := by
    simpa only [θ',preferredFullPopulationWeight,preferred_occupancy_lift B.p B.periodic,
      preferred_occupancy_lift B.m B.m_periodic] using hw
  have hb := hbound N hN ε τ hε hερ hτ hτρ θ' hθ hw' i
  change c*τ/(N:ℝ)≤‖(preferredRadialTrace d ε-Complex.cos
    (deformedAngles τ B.p B.m θ' i))^2-1‖ at hb
  dsimp only [θ'] at hb
  rw [preferred_cos_deformed_lift τ 0 B.p B.m B.periodic B.m_periodic] at hb
  exact hb

end
end IsingBulk.Preferred22
