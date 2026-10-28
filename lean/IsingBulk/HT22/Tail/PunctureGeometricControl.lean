import IsingBulk.HT22.Tail.PunctureApproximation

/-! Actual cutoff-current and value estimates in the common geometric-log
form needed by the independent derivative-limit theorem. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
set_option backward.isDefEq.respectTransparency false

theorem puncture_flux_log_geometric_of_smallMass {n : ℕ}
    (a : ℝ) (σ : ℂ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) {F C : ℝ} (hF : 0<F) (hC : 0<C)
    (hsmall : ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in angularBox n,
        smallMassIntegrand a σ d B τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredDyadicRadius m) θ)≤ENNReal.ofReal (F*(1+|Real.log ε|)*(1/8:ℝ)^m))
    (hfield : ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ θ : Fin (n+1) → ℝ,
      θ∈preferredRightAngularBox d B.delta δB (n+1) → 0<preferredAngularDiameter θ →
      ∀ i, ‖angularField τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖≤
        C*((n+1:ℕ):ℝ)^2/preferredAngularDiameter θ) :
    ∃ L : ℝ, 0<L ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ m : ℕ,
      ‖∫ θ : Fin n → ℝ in angularBox n,
        punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredDyadicRadius m)
          (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖≤
        L*(1+|Real.log ε|)*(1/2:ℝ)^m := by
  obtain ⟨A,hA,hpoint⟩ := punctureFlux_lintegral_le_smallMass
  let L := A*C*((n+1:ℕ):ℝ)^5*F/Real.pi^2
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro ε hε hεr m
  let R := preferredDyadicRadius m
  let Q := A*C*((n+1:ℕ):ℝ)^5/R^2
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hh := hpoint n a σ d B δB τ rcut hcut j (IsingBulk.Branch.radialParameter d.alpha ε)
    R C (preferredDyadicRadius_pos m) hC (hfield ε hε hεr)
  have hm : ENNReal.ofReal Q*(∫⁻ θ : Fin n → ℝ in angularBox n,
      smallMassIntegrand a σ d B τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε) R θ)≤
      ENNReal.ofReal Q*ENNReal.ofReal (F*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
    simpa only [mul_comm] using mul_le_mul_left (hsmall ε hε hεr m) (ENNReal.ofReal Q)
  have hb := hh.trans hm
  rw [←ENNReal.ofReal_mul hQ] at hb
  have hR2 : R^2=Real.pi^2*(1/4:ℝ)^m := by
    have hr : R=Real.pi*(1/2:ℝ)^m := by dsimp [R,preferredDyadicRadius]; rw [pow_succ]; ring
    rw [hr,mul_pow,←pow_mul,show m*2=2*m by omega,pow_mul]
    norm_num
  have he : Q*(F*(1+|Real.log ε|)*(1/8:ℝ)^m)=L*(1+|Real.log ε|)*(1/2:ℝ)^m := by
    dsimp only [Q]
    rw [hR2]
    calc
      _ = (L*(1+|Real.log ε|))*((1/8:ℝ)^m/(1/4:ℝ)^m) := by dsimp [L]; ring
      _ = _ := by rw [←div_pow]; norm_num
  rw [he] at hb
  exact (norm_integral_le_lintegral_norm _).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal (by positivity)))

theorem puncture_value_log_geometric_of_smallMass {n : ℕ} (hn : 0<n)
    (a : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) {F : ℝ} (hF : 0<F)
    (hreg : ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x)
    (hmass : ∀ ε : ℝ, 0<ε → ε<ε₀ →
      (∫⁻ θ : Fin n → ℝ in angularBox n, ENNReal.ofReal
        ‖transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖)<(⊤:ℝ≥0∞))
    (hsmall : ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in angularBox n,
        smallMassIntegrand a σ d B τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredDyadicRadius m) θ)≤ENNReal.ofReal (F*(1+|Real.log ε|)*(1/8:ℝ)^m)) :
    ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ m : ℕ,
    ‖(∫ θ : Fin n → ℝ in angularBox n, puncturedDensity σ d B τ (preferredDyadicRadius m) rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))-
      (∫ θ : Fin n → ℝ in angularBox n, transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))‖≤
      F*(1+|Real.log ε|)*(1/2:ℝ)^m := by
  intro ε hε hεr m
  have hh := puncture_value_error_le_smallMass hn a σ hσ d B rcut hcut
    (IsingBulk.Branch.radialParameter d.alpha ε) (preferredDyadicRadius m) (preferredDyadicRadius_pos m)
    j (hreg ε hε hεr) (hmass ε hε hεr) (by positivity) (hsmall ε hε hεr m)
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num : (1/8:ℝ)≤1/2) m)
    (by positivity))

end
end IsingBulk.HT22.Tail
