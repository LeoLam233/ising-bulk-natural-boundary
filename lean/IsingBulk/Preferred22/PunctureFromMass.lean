import IsingBulk.Preferred22.RightPunctureApproximation

/-! The genuine puncture-to-integral estimates from explicit small-tube
mass. These generic source statements have no large-particle restriction,
so the finite Vandermonde block uses the same actual Stokes exhaustion. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff

/-- Exact norm-mass passage for any positive-dimensional right contour. -/
theorem preferred_right_puncture_error_of_small_mass {n j : ℕ} (hnDim : 0<n)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    {A : ℝ} (hA : 0<A)
    (hnorm : ∀ ε : ℝ,0<ε → ε<ε₀ →
      IntegrableOn (fun θ : Fin n → ℝ =>
        ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖)
        (angularBox n))
    (hcomplex : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      ∀ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∀ i a : Fin (n+1),
      IntegrableOn (fun θ : Fin n → ℝ =>
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))
        (preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a))
    (hsmall : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ)≤
      ENNReal.ofReal (A*(1+|Real.log ε|)*(1/8:ℝ)^m)) :
    ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      IntegrableOn (fun θ : Fin n → ℝ =>
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))
        (angularBox n) ∧
      ∀ m : ℕ,
      IntegrableOn (fun θ : Fin n → ℝ =>
        (preferredEqualityCutoff (preferredDyadicRadius m) (preferredLiftedAngles B.delta (constrainedAngles θ)):ℂ)*
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))
        (angularBox n) ∧
      ‖(∫ θ : Fin n → ℝ in angularBox n,
        (preferredEqualityCutoff (preferredDyadicRadius m) (preferredLiftedAngles B.delta (constrainedAngles θ)):ℂ)*
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))-
        preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|)*(1/8:ℝ)^m := by
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let P := fun θ : Fin n → ℝ => preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
    (preferredLiftedAngles B.delta (constrainedAngles θ))
  have hn := hnorm ε hε hεr
  have hi : IntegrableOn P (angularBox n) := by
    have hh := preferred_right_weighted_integrable_of_shells hnDim d B τ rcut hcut j s
      (hcomplex ε hε hεr) hn (fun _ => 1) continuous_const (by intro θ; simp)
    simpa only [one_mul] using hh
  refine ⟨hi,?_⟩
  intro m
  let R := preferredDyadicRadius m
  let ξ := fun θ : Fin (n+1) → ℝ => (preferredEqualityCutoff R θ:ℂ)
  have hξc : Continuous ξ := Complex.continuous_ofReal.comp (preferredEqualityCutoff_smooth R).continuous
  have hξb (θ : Fin (n+1) → ℝ) : ‖ξ θ‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (preferredEqualityCutoff_bounds R θ).1]
    exact (preferredEqualityCutoff_bounds R θ).2
  have hξi := preferred_right_weighted_integrable_of_shells hnDim d B τ rcut hcut j s
    (hcomplex ε hε hεr) hn ξ hξc hξb
  refine ⟨hξi,?_⟩
  let W := fun θ : Fin n → ℝ => (ξ (preferredLiftedAngles B.delta (constrainedAngles θ))-1)*P θ
  have he : (fun θ : Fin n → ℝ => ξ (preferredLiftedAngles B.delta (constrainedAngles θ))*P θ-P θ)=W := by
    funext θ
    dsimp [W]
    ring
  change ‖(∫ θ in angularBox n,ξ (preferredLiftedAngles B.delta (constrainedAngles θ))*P θ)-
    ∫ θ in angularBox n,P θ‖≤_
  rw [←integral_sub hξi hi,he]
  have hsupp : (∫⁻ θ : Fin n → ℝ in angularBox n,ENNReal.ofReal ‖W θ‖)=
      ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,ENNReal.ofReal ‖W θ‖ :=
    preferred_weighted_right_lintegral_support d B τ rcut hcut j s (fun θ => ξ θ-1)
  have hdom : (∫⁻ θ : Fin n → ℝ in angularBox n,ENNReal.ofReal ‖W θ‖)≤
      ENNReal.ofReal (A*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
    rw [hsupp]
    apply le_trans (lintegral_mono (fun θ => ?_)) (hsmall ε hε hεr m)
    let w := preferredLiftedAngles B.delta (constrainedAngles θ)
    by_cases hd : preferredAngularDiameter w≤R
    · unfold preferredRightSmallMassIntegrand
      rw [ite_eq_left hd]
      apply ENNReal.ofReal_le_ofReal
      change ‖(ξ w-1)*P θ‖≤‖P θ‖
      rw [norm_mul]
      have hb : ‖ξ w-1‖≤1 := by
        have hh := preferredEqualityCutoff_bounds R w
        rw [show ξ w-1=((preferredEqualityCutoff R w-1:ℝ):ℂ) by simp only [ξ,Complex.ofReal_sub,Complex.ofReal_one],
          Complex.norm_real,Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)
    · have hx := preferredEqualityCutoff_one_of_diameter_lt (preferredDyadicRadius_pos m) w (lt_of_not_ge hd)
      have hz : W θ=0 := by
        change ((preferredEqualityCutoff (preferredDyadicRadius m) w:ℂ)-1)*P θ=0
        rw [hx,Complex.ofReal_one,sub_self,zero_mul]
      rw [hz,norm_zero,ENNReal.ofReal_zero]
      exact bot_le
  have hnA : 0≤A*(1+|Real.log ε|)*(1/8:ℝ)^m := by positivity
  exact (norm_integral_le_lintegral_norm W).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hdom).trans_eq (ENNReal.toReal_ofReal hnA))


/-- Actual physical flux from genuine small-tube mass at any particle order. -/
theorem preferred_right_puncture_flux_bound_of_small_mass {n j : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    {F : ℝ} (hF : 0<F)
    (hsmall : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ)≤
      ENNReal.ofReal (F*(1+|Real.log ε|)*(1/8:ℝ)^m))
    {C : ℝ} (hC : 0<C)
    (hfield : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ θ : Fin (n+1) → ℝ,
      θ∈preferredRightAngularBox d B.delta δB (n+1) → 0<preferredAngularDiameter θ → ∀ i,
      ‖preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖≤
        C*((n+1:ℕ):ℝ)^2/preferredAngularDiameter θ) :
    ∃ L : ℝ,0<L ∧ ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
    (∫⁻ θ : Fin n → ℝ in angularBox n,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε (preferredDyadicRadius m)
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal (L*(1+|Real.log ε|)*(1/2:ℝ)^m) := by
  obtain ⟨A,hA,hpoint⟩ := preferredRightPunctureFlux_pointwise d B
  let L := A*C*((n+1:ℕ):ℝ)^5*F/Real.pi^2
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  intro ε hε hεr m
  let H := 1+|Real.log ε|
  let K := F*H
  have hK : 0≤K := by dsimp [K,H]; positivity
  let R := preferredDyadicRadius m
  let Q := A*C*((n+1:ℕ):ℝ)^5/R^2
  have hR : 0<R := preferredDyadicRadius_pos m
  have hQ : 0≤Q := by dsimp [Q]; positivity
  rw [preferredRightPunctureFlux_lintegral_support d B τ rcut hcut j ε R]
  have hdom : (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε R
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal Q*(∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ) := by
    calc
      _ ≤ ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
          ENNReal.ofReal Q*preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ := by
        apply setLIntegral_mono' (preferredRightRegion_measurable d B hcut.2.1)
        intro θ hθ
        let w := preferredLiftedAngles B.delta (constrainedAngles θ)
        by_cases hd : preferredAngularDiameter w≤R
        · have hh := hpoint (n+1) τ ε R C hR hC rcut j w (hfield ε hε hεr w hθ.2)
          unfold preferredRightSmallMassIntegrand
          rw [ite_eq_left hd,←ENNReal.ofReal_mul hQ]
          exact ENNReal.ofReal_le_ofReal hh
        · have hz := preferredRightPunctureFlux_zero_outside d B τ rcut j ε hR w (lt_of_not_ge hd)
          rw [hz,norm_zero,ENNReal.ofReal_zero]
          exact bot_le
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hmul : ENNReal.ofReal Q*(∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ)≤
      ENNReal.ofReal Q*ENNReal.ofReal
        (F*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
    simpa only [mul_comm] using mul_le_mul_left (hsmall ε hε hεr m) (ENNReal.ofReal Q)
  have hh := hdom.trans hmul
  rw [←ENNReal.ofReal_mul hQ] at hh
  apply hh.trans_eq
  congr 1
  have hR2 : R^2=Real.pi^2*(1/4:ℝ)^m := by
    have hRad : R=Real.pi*(1/2:ℝ)^m := by
      dsimp [R,preferredDyadicRadius]
      rw [pow_succ]
      ring
    rw [hRad,mul_pow,←pow_mul,show m*2=2*m by omega,pow_mul]
    norm_num
  change (A*C*((n+1:ℕ):ℝ)^5/R^2)*(K*(1/8:ℝ)^m)=L*H*(1/2:ℝ)^m
  rw [hR2]
  calc
    _ = (L*H)*((1/8:ℝ)^m/(1/4:ℝ)^m) := by dsimp [L,K]; ring
    _ = _ := by rw [←div_pow]; norm_num



end
end IsingBulk.Preferred22
