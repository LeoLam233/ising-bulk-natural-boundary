import IsingBulk.HT22.Tail.PhysicalSupport

/-! Exact actual signed puncture-current domination by small-equality mass.
The mass is the original full constrained integral, before any dyadic cover. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set MeasureTheory
open scoped BigOperators Topology ENNReal
set_option backward.isDefEq.respectTransparency false

def smallMassIntegrand {n : ℕ} (a : ℝ) (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) (R : ℝ)
    (θ : Fin n → ℝ) : ℝ≥0∞ :=
  let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
  if preferredAngularDiameter w≤R then ENNReal.ofReal
    ‖transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s w‖ else 0

theorem punctureFlux_lintegral_le_smallMass :
    ∃ A : ℝ, 0<A ∧ ∀ n : ℕ, ∀ a : ℝ, ∀ σ : ℂ, ∀ d : PreferredBranchData,
    ∀ B : PreferredCoareaBump d, ∀ δB τ : ℝ, ∀ rcut : ℝ → ℝ,
    PreferredRightCutoffData d B δB rcut → ∀ j : ℕ, ∀ s : ℂ, ∀ R C : ℝ, 0<R → 0<C →
    (∀ θ : Fin (n+1) → ℝ, θ∈preferredRightAngularBox d B.delta δB (n+1) →
      0<preferredAngularDiameter θ → ∀ i, ‖angularField τ B.p B.m s θ i‖≤
        C*((n+1:ℕ):ℝ)^2/preferredAngularDiameter θ) →
    (∫⁻ θ : Fin n → ℝ in angularBox n, ENNReal.ofReal
      ‖punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j s R
        (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖)≤
      ENNReal.ofReal (A*C*((n+1:ℕ):ℝ)^5/R^2)*
        ∫⁻ θ : Fin n → ℝ in angularBox n, smallMassIntegrand a σ d B τ rcut j s R θ := by
  obtain ⟨A,hA,hpoint⟩ := punctureFlux_pointwise
  refine ⟨A,hA,?_⟩
  intro n a σ d B δB τ rcut hcut j s R C hR hC hfield
  let Q := A*C*((n+1:ℕ):ℝ)^5/R^2
  have hQ : 0≤Q := by dsimp [Q]; positivity
  calc
    _ ≤ ∫⁻ θ : Fin n → ℝ in angularBox n,
        ENNReal.ofReal Q*smallMassIntegrand a σ d B τ rcut j s R θ := by
      apply lintegral_mono
      intro θ
      let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
      by_cases hb : w∈preferredRightAngularBox d B.delta δB (n+1)
      · by_cases hd : preferredAngularDiameter w≤R
        · have hh := hpoint (n+1) σ τ R C hR hC preferredPopulationCutoff B.p B.m rcut j s w (hfield w hb)
          change ENNReal.ofReal ‖punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j s R w‖≤_
          simp only [smallMassIntegrand,show preferredAngularDiameter (preferredLiftedAngles B.delta
            (constrainedAtTotal a θ))≤R from hd,ite_true]
          rw [←ENNReal.ofReal_mul hQ]
          exact ENNReal.ofReal_le_ofReal hh
        · have hz := punctureFlux_zero_outside σ τ preferredPopulationCutoff B.p B.m rcut j s hR w (lt_of_not_ge hd)
          change ENNReal.ofReal ‖punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j s R w‖≤_
          rw [hz,norm_zero,ENNReal.ofReal_zero]
          exact bot_le
      · have hp := transportedDensity_right_support σ d B τ rcut hcut j s w
          (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal a θ)) hb
        have hz : punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j s R w=0 := by
          simp only [punctureFlux,hp,mul_zero,Finset.sum_const_zero]
        change ENNReal.ofReal ‖punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j s R w‖≤_
        rw [hz,norm_zero,ENNReal.ofReal_zero]
        exact bot_le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The original full small-equality mass is exactly on the actual right
region; this support restriction happens before the later shell cover. -/
theorem smallMass_lintegral_eq_signedRightRegion {n : ℕ}
    (a : ℝ) (σ : ℂ) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) (R : ℝ) :
    (∫⁻ θ : Fin n → ℝ in angularBox n,smallMassIntegrand a σ d B τ rcut j s R θ)=
      ∫⁻ θ : Fin n → ℝ in signedRightRegion a d B δB,smallMassIntegrand a σ d B τ rcut j s R θ := by
  let f := smallMassIntegrand (n:=n) a σ d B τ rcut j s R
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hsupp : Function.support ((angularBox n).indicator f)⊆signedRightRegion a d B δB := by
    intro θ hθ
    by_contra hn
    by_cases hb : θ∈angularBox n
    · have hz := transportedDensity_right_support σ d B τ rcut hcut j s _
        (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal a θ))
        (by intro hh; exact hn ⟨hb,hh⟩)
      have hf : f θ=0 := by simp only [f,smallMassIntegrand,hz,norm_zero,ENNReal.ofReal_zero,ite_self]
      exact hθ (by rw [Set.indicator_of_mem hb,hf])
    · exact hθ (Set.indicator_of_notMem hb _)
  apply le_antisymm
  · calc
      _ = ∫⁻ θ,(angularBox n).indicator f θ := (lintegral_indicator hbox f).symm
      _ = ∫⁻ θ in signedRightRegion a d B δB,(angularBox n).indicator f θ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)
  · exact lintegral_mono_set (fun θ hθ => hθ.1)

end
end IsingBulk.HT22.Tail
