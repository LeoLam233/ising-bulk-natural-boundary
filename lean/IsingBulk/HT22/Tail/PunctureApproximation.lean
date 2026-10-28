import IsingBulk.HT22.Tail.DensityMeasurable
import IsingBulk.HT22.Tail.PunctureMass
import IsingBulk.Preferred22.VerticalLattice

/-! Exact complex integral approximation from actual full signed mass.
Measurability and punctured integrability are proved, not assumed. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

theorem transported_integrable_of_mass {n : ℕ} (hn : 0<n)
    (a : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x)
    (hmass : (∫⁻ θ : Fin n → ℝ in angularBox n, ENNReal.ofReal
      ‖transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖)<(⊤:ℝ≥0∞)) :
    IntegrableOn (fun θ : Fin n → ℝ =>
      transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAtTotal a θ))) (angularBox n) :=
  ⟨transportedDensity_aestronglyMeasurable hn a σ hσ d B rcut hcut s j hreg,
    (hasFiniteIntegral_iff_norm _).mpr hmass⟩

theorem punctured_integrable {n : ℕ}
    (a : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x) :
    IntegrableOn (fun θ : Fin n → ℝ => puncturedDensity σ d B τ R rcut j s
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ))) (angularBox n) := by
  apply continuous_integrableOn_angularBox
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hh := (puncturedDensity_and_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut
    s R j hreg (constrainedAtTotal a θ)).1
  exact (hh.comp θ (contDiffAt_const.prodMk (constrainedAtTotal_contDiff a).contDiffAt)).continuousAt

/-- Quantitative value error at any positive puncture radius. -/
theorem puncture_value_error_le_smallMass {n : ℕ} (hn : 0<n)
    (a : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (hR : 0<R) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x)
    (hmass : (∫⁻ θ : Fin n → ℝ in angularBox n, ENNReal.ofReal
      ‖transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖)<(⊤:ℝ≥0∞))
    {A : ℝ} (hA : 0≤A)
    (hsmall : (∫⁻ θ : Fin n → ℝ in angularBox n, smallMassIntegrand a σ d B τ rcut j s R θ)≤ENNReal.ofReal A) :
    ‖(∫ θ : Fin n → ℝ in angularBox n, puncturedDensity σ d B τ R rcut j s
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))-
      (∫ θ : Fin n → ℝ in angularBox n, transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))‖≤A := by
  let P := fun θ : Fin n → ℝ => transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s
    (preferredLiftedAngles B.delta (constrainedAtTotal a θ))
  let G := fun θ : Fin n → ℝ => puncturedDensity σ d B τ R rcut j s
    (preferredLiftedAngles B.delta (constrainedAtTotal a θ))
  have hP := transported_integrable_of_mass hn a σ hσ d B rcut hcut s j hreg hmass
  have hG := punctured_integrable a σ hσ d B rcut hcut s R j hreg
  change ‖(∫ θ in angularBox n,G θ)-(∫ θ in angularBox n,P θ)‖≤A
  rw [←integral_sub hG hP]
  have hdom : (∫⁻ θ : Fin n → ℝ in angularBox n,ENNReal.ofReal ‖G θ-P θ‖)≤ENNReal.ofReal A := by
    apply le_trans (lintegral_mono (fun θ => ?_)) hsmall
    let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
    by_cases hd : preferredAngularDiameter w≤R
    · change ENNReal.ofReal ‖(preferredEqualityCutoff R w:ℂ)*P θ-P θ‖≤_
      simp only [smallMassIntegrand,show preferredAngularDiameter (preferredLiftedAngles B.delta
        (constrainedAtTotal a θ))≤R from hd,ite_true]
      apply ENNReal.ofReal_le_ofReal
      rw [show (preferredEqualityCutoff R w:ℂ)*P θ-P θ=((preferredEqualityCutoff R w:ℂ)-1)*P θ by ring,norm_mul]
      have hb : ‖(preferredEqualityCutoff R w:ℂ)-1‖≤1 := by
        have hh := preferredEqualityCutoff_bounds R w
        rw [show (preferredEqualityCutoff R w:ℂ)-1=((preferredEqualityCutoff R w-1:ℝ):ℂ) by push_cast; rfl,
          Complex.norm_real,Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)
    · have he := preferredEqualityCutoff_one_of_diameter_lt hR w (lt_of_not_ge hd)
      change ENNReal.ofReal ‖(preferredEqualityCutoff R w:ℂ)*P θ-P θ‖≤_
      rw [he,Complex.ofReal_one,one_mul,sub_self,norm_zero,ENNReal.ofReal_zero]
      exact bot_le
  exact (norm_integral_le_lintegral_norm _).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hdom).trans_eq (ENNReal.toReal_ofReal hA))

end
end IsingBulk.HT22.Tail

