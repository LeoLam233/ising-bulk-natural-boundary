import IsingBulk.Preferred22.SelectedSourceMajorant
import IsingBulk.Preferred22.SelectedPeriodic

/-! Literal all-angle one-body domination, including unreduced dependent
angles. The envelope depends on one real angle and epsilon alone. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
set_option maxHeartbeats 1000000

theorem preferred_actual_discriminant_profile (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0≤τ → τ<ρ →
      ∀ θ : Fin N → ℝ,∀ i : Fin N,
      c*(|Real.cos d.b-Real.cos (θ i)|+ε)≤
        ‖(preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i))^2-1‖ := by
  obtain ⟨c,ρ,hc,hρ,hρ1,hsource⟩ := preferred_selected_source_discriminant_profile d B
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ i
  let θ' := preferredLiftedAngles 0 θ
  have hθ (a : Fin N) : θ' a∈Icc (-Real.pi) Real.pi := by
    have h := toIocMod_mem_Ioc (by positivity : 0<2*Real.pi) (-Real.pi-0) (θ a)
    change θ' a∈Ioc (-Real.pi-0) (-Real.pi-0+2*Real.pi) at h
    constructor <;> linarith [h.1,h.2]
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ'
  have hb := hsource ε τ (occupancy B.p θ'/(N:ℝ)) (occupancy B.m θ'/(N:ℝ))
    (θ' i) hε hερ hτ hτρ hσ hυ (hθ i)
  rw [←actual_bump_angle d B τ θ' i] at hb
  change c*(|Real.cos d.b-Real.cos (preferredLiftedAngles 0 θ i)|+ε)≤
    ‖(preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m (preferredLiftedAngles 0 θ) i))^2-1‖ at hb
  rw [preferred_cos_deformed_lift τ 0 B.p B.m B.periodic B.m_periodic] at hb
  simpa only [preferredLiftedAngles,preferred_periodic_lift Real.cos Real.cos_periodic] using hb

theorem preferred_actual_oneBody_profile (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ρ : ℝ,0<C ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0≤τ → τ<ρ →
      ∀ θ : Fin N → ℝ,∀ i : Fin N,
      ‖oneBody (physicalRoot (preferredRadialTrace d ε-Complex.cos
        (deformedAngles τ B.p B.m θ i)))‖≤C*preferredSelectedOneBodyProfile d ε (θ i) := by
  obtain ⟨c,ρ,hc,hρ,hρ1,hgap⟩ := preferred_actual_discriminant_profile d B
  refine ⟨(Real.sqrt c)⁻¹,ρ,by positivity,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ i
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW := (mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  exact preferred_oneBody_of_discriminant_margin (Or.inl (ne_of_gt hW)) hc (by positivity)
    (hgap N hN ε τ hε hερ hτ hτρ θ i)

end
end IsingBulk.Preferred22
