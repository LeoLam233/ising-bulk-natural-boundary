import IsingBulk.Preferred22.WeightedOuterMass

/-! The actual coarea estimate also integrates every smooth original
multiplier that vanishes in a fixed full-equality neighborhood. This
supports independent local-chart and equality-exclusion radii. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The source pointwise majorant and the exact equality-zero germ imply
an actual integral inequality, including the full one-sided lift. -/
theorem preferredWeightedExcluded_lintegral_bound {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB ε τ ρ C : ℝ}
    (ψ : (Fin (n+1) → ℝ) → ℂ)
    (hψzero : ∀θ : Fin (n+1) → ℝ,preferredAngularDiameter θ<ρ → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (hC : 0≤C) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ)
    (hb : ∀θ∈preferredRightAngularBox d B.delta δB (n+1),
      ρ≤preferredAngularDiameter θ →
      ‖preferredWeightedPhysicalDensity (ψ) τ preferredPopulationCutoff
        B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
        C*preferredJacobianResolvent d B ε τ θ) :
    (∫⁻ θ in angularBox n,ENNReal.ofReal ‖preferredWeightedPhysicalDensity (ψ)
      τ preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
    ENNReal.ofReal C*(∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      preferredAwayJacobian d B ε τ (ρ) θ) := by
  rw [preferredWeightedNorm_lintegral_eq_region d B _ τ rcut hcut]
  calc
    _ ≤ ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        ENNReal.ofReal C*preferredAwayJacobian d B ε τ (ρ) θ := by
      apply setLIntegral_mono' (preferredRightRegion_measurable d B hcut.2.1)
      intro θ hθ
      let w := preferredLiftedAngles B.delta (constrainedAngles θ)
      by_cases hd : ρ≤preferredAngularDiameter w
      · unfold preferredAwayJacobian
        rw [ite_eq_left hd,←ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hb w hθ.2 hd)
      · have hz := (preferredWeightedPhysicalDensity_zero_germ ψ τ preferredPopulationCutoff B.p B.m rcut
          (IsingBulk.Branch.radialParameter d.alpha ε) w (hψzero w (lt_of_not_ge hd)) j).self_of_nhds
        dsimp only at hz
        rw [hz,norm_zero,ENNReal.ofReal_zero]
        exact bot_le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Actual all-order full-Haar mass of the descendants of any smooth
original multiplier with a genuine equality-zero neighborhood. This holds for every positive even particle
number, including N=2, without a relation between N and j. -/
theorem preferred_actual_weighted_excluded_mass (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ n : ℕ,2≤n+1 → Even (n+1) →
      ∀ ψ : (Fin (n+1) → ℝ) → ℂ,ContDiff ℝ ∞ ψ → ∀ ρ : ℝ,0<ρ →
      (∀θ : Fin (n+1) → ℝ,preferredAngularDiameter θ<ρ → ψ=ᶠ[𝓝 θ] fun _ => 0) →
      ∀ j : ℕ,
      ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        (∫⁻ θ in angularBox n,ENNReal.ofReal ‖preferredWeightedPhysicalDensity (ψ)
          τ preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
          ENNReal.ofReal (A*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hs⟩ := preferred_actual_weighted_away_density_bound d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨εs,τs,δs,hεs,hτs,hδs,hδsB,hs'⟩ := hs B hB
  obtain ⟨δm,τm,εm,hδm,_hδmB,hτm,hεm,hm⟩ := preferred_finite_away_jacobian_mass d B
  let δ₀ := min δs δm
  let τ₀ := min τs τm
  let ε₀ := min εs εm
  refine ⟨δ₀,τ₀,ε₀,lt_min hδs hδm,(min_le_left _ _).trans_lt hδsB,
    lt_min hτs hτm,lt_min hεs hεm,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr n hN hEven ψ hψ ρ hρ hψzero j
  have hsb : ∀ N : ℕ,2≤N → Even N → ∀ ψ : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ ψ →
      ∀ j : ℕ,∀ ρ : ℝ,0<ρ → ∃ C : ℝ,0<C ∧
      ∀ ε τ : ℝ,0<ε → ε<εs → 0≤τ → τ<τs → ∀ θ : Fin N → ℝ,
      (∀ i,-δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) → ρ≤preferredAngularDiameter θ →
      ‖preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*preferredJacobianResolvent d B ε τ θ := by
    intro N hN hEven
    obtain ⟨m,rfl⟩ := hEven
    have he : m+m=2*m := by omega
    rw [he]
    exact hs' δB hδB (hδB₀.trans (min_le_left _ _))
      rcut hcut.2.2.1 hcut.2.2.2.1 m (by omega)
  obtain ⟨C,hC,hb⟩ := hsb (n+1) hN hEven (ψ)
    hψ j ρ hρ
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨L,hL,hmass⟩ := hm δB hδB (hδB₀.trans (min_le_right _ _)) n
      ρ hρ
    refine ⟨C*L,mul_pos hC hL,?_⟩
    intro ε hε hεr
    have hpoint (θ : Fin (n+1+1) → ℝ) (hθ : θ∈preferredRightAngularBox d B.delta δB (n+1+1))
        (hd : ρ≤preferredAngularDiameter θ) :
        ‖preferredWeightedPhysicalDensity (ψ) τ preferredPopulationCutoff
          B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C*preferredJacobianResolvent d B ε τ θ :=
      hb ε τ hε (hεr.trans_le (min_le_left _ _)) hτ (hτr.trans_le (min_le_left _ _)) θ
        (fun i => ⟨by linarith [(hθ i).1],by linarith [(hθ i).2]⟩) hd
    have hh := preferredWeightedExcluded_lintegral_bound d B ψ hψzero hC.le rcut hcut j hpoint
    have hm' := hmass ε τ hε (hεr.trans_le (min_le_right _ _)) hτ (hτr.trans_le (min_le_right _ _))
    have hmul : ENNReal.ofReal C*(∫⁻ θ : Fin (n+1) → ℝ in preferredRightRegion d B δB,
        preferredAwayJacobian d B ε τ (ρ) θ)≤
        ENNReal.ofReal C*ENNReal.ofReal (L*(1+|Real.log ε|)) := by
      simpa only [mul_comm] using mul_le_mul_left hm' (ENNReal.ofReal C)
    apply (hh.trans hmul).trans_eq
    rw [←ENNReal.ofReal_mul hC.le,mul_assoc]

end
end IsingBulk.Preferred22
