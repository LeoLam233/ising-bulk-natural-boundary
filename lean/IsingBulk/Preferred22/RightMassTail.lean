import IsingBulk.Preferred22.ShellAggregation
import IsingBulk.Preferred22.ShellIntegrability
import IsingBulk.Preferred22.TransportSupport

/-! The exact q28 shell estimate implies the complete large-order absolute
sum of the actual transported right density. The j=0 source theorem supplies
an unconditional physical instance. No coefficient differentiation identity
or positive-order q28 estimate is assumed implicitly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

/-- Actual full-Haar absolute mass of the genuine right transported density. -/
def preferredRightAbsoluteTransportMass (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (n j : ℕ) (ε : ℝ) : ℝ :=
  ∫ θ in angularBox n,‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖

theorem preferredRightAbsoluteTransportMass_nonneg (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (n j : ℕ) (ε : ℝ) :
    0≤preferredRightAbsoluteTransportMass d B τ rcut n j ε := integral_nonneg (fun _ => norm_nonneg _)

/-- True complete right absolute mass and actual transported integral bound
from the exact shell proposition. Integrability is proved by the real cover. -/
theorem preferred_right_absolute_bound_of_q28 (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut) (k : ℕ)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k) :
    ∀ j : ℕ,j≤k → ∃ C : ℝ,∃ J : ℕ,0<C ∧ ∀ n : ℕ,2*k+4<n+1 → Even (n+1) →
      ∀ ε : ℝ,0<ε → ε<ε₀ →
      IntegrableOn (fun θ : Fin n → ℝ => ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖) (angularBox n) ∧
      preferredRightAbsoluteTransportMass d B τ rcut n j ε≤
        6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope C J (n+1)*(1+|Real.log ε|) ∧
      ‖preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤
        6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope C J (n+1)*(1+|Real.log ε|) := by
  intro j hj
  obtain ⟨C,J,hC,hbound⟩ := preferred_right_region_bound_of_q28 d B hcut.2.1
    preferredPopulationCutoff rcut k hq28 j hj
  refine ⟨C,J,hC,?_⟩
  intro n hN hEven ε hε hεr
  let f := fun θ : Fin n → ℝ => ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖
  let A := 6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope C J (n+1)*(1+|Real.log ε|)
  have hA : 0≤A := by dsimp [A,shellOrderEnvelope]; positivity
  have hb : (∫⁻ θ in preferredRightRegion d B δB,ENNReal.ofReal (f θ))≤ENNReal.ofReal A :=
    hbound n hN hEven ε hε hεr
  have hi : IntegrableOn f (preferredRightRegion d B δB) := by
    apply preferredRightRegion_integrable_of_shells (by omega : 0<n) d B hcut.2.1 f
    · intro m l i a
      obtain ⟨_C,_J,_hC,hh⟩ := hq28 j hj
      exact (hh n (by omega) hEven ε (preferredDyadicRadius m) hε hεr (preferredDyadicRadius_pos m) l.1 i a).1
    · have hf : ∀ θ,‖f θ‖=f θ := fun θ => Real.norm_of_nonneg (norm_nonneg _)
      simp_rw [hf]
      exact hb.trans_lt ENNReal.ofReal_lt_top
  have hzero (θ : Fin n → ℝ) (hθ : θ∈angularBox n \ preferredRightRegion d B δB) : f θ=0 := by
    have hh := preferredTransportedDensity_right_support d B τ rcut hcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) _
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
      (by intro hh; exact hθ.2 ⟨hθ.1,hh⟩)
    dsimp [f]
    rw [hh,norm_zero]
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hib : IntegrableOn f (angularBox n) := hi.of_forall_sdiff_eq_zero hbox hzero
  have hfull : (∫⁻ θ in angularBox n,ENNReal.ofReal (f θ))≤ENNReal.ofReal A := by
    rw [preferredTransportedNorm_lintegral_eq_rightRegion d B τ rcut hcut j]
    exact hb
  have he := ofReal_integral_eq_lintegral_ofReal hib (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  rw [← he] at hfull
  have hmass : preferredRightAbsoluteTransportMass d B τ rcut n j ε≤A :=
    (ENNReal.ofReal_le_ofReal_iff hA).mp hfull
  exact ⟨hib,hmass,(norm_integral_le_integral_norm _).trans hmass⟩

/-- Every positive even order above the large-order cutoff is retained. -/
def preferredRightLargeMassTerms (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (k j : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  if 2*k+4<2*(m+1) then preferredRightAbsoluteTransportMass d B τ rcut (2*m+1) j ε else 0

/-- The complete genuine large-order right absolute sum is logarithmically
bounded once the exact positive-order q28 proposition is proved. -/
theorem preferred_complete_right_mass_tail_of_q28 (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut) (k : ℕ)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k) :
    ∀ j : ℕ,j≤k → ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      Summable (preferredRightLargeMassTerms d B τ rcut k j ε) ∧
      (∑' m,preferredRightLargeMassTerms d B τ rcut k j ε m)≤A*(1+|Real.log ε|) := by
  intro j hj
  obtain ⟨C,J,hC,hbound⟩ := preferred_right_absolute_bound_of_q28 d B rcut hcut k hq28 j hj
  let E := fun m : ℕ => shellOrderEnvelope C (J+3) (2*(m+1))
  have hE : Summable E := even_shell_order_envelope_summable hC.le (J+3)
  have hEn (m : ℕ) : 0≤E m := by dsimp [E,shellOrderEnvelope]; positivity
  let A := max 1 (6*∑' m,E m)
  refine ⟨A,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro ε hε hεr
  let H := 1+|Real.log ε|
  have hH : 0≤H := by dsimp [H]; positivity
  have hterm (m : ℕ) : 0≤preferredRightLargeMassTerms d B τ rcut k j ε m ∧
      preferredRightLargeMassTerms d B τ rcut k j ε m≤6*H*E m := by
    unfold preferredRightLargeMassTerms
    split_ifs with hcutoff
    · have hNeq : 2*m+1+1=2*(m+1) := by omega
      have hN : 2*k+4<2*m+1+1 := by omega
      have hEven : Even (2*m+1+1) := ⟨m+1,by omega⟩
      have hb := (hbound (2*m+1) hN hEven ε hε hεr).2.1
      refine ⟨preferredRightAbsoluteTransportMass_nonneg d B τ rcut (2*m+1) j ε,hb.trans_eq ?_⟩
      rw [hNeq]
      dsimp [H,E,shellOrderEnvelope]
      rw [pow_add]
      ring
    · exact ⟨le_rfl,mul_nonneg (mul_nonneg (by norm_num) hH) (hEn m)⟩
  have hmaj : Summable (fun m : ℕ => 6*H*E m) := hE.mul_left (6*H)
  have hsum : Summable (preferredRightLargeMassTerms d B τ rcut k j ε) :=
    hmaj.of_nonneg_of_le (fun m => (hterm m).1) (fun m => (hterm m).2)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' m : ℕ,6*H*E m := Summable.tsum_le_tsum (fun m => (hterm m).2) hsum hmaj
    _ = (6*∑' m,E m)*H := by rw [tsum_mul_left]; ring
    _ ≤ A*H := mul_le_mul_of_nonneg_right (le_max_right _ _) hH

/-- Unconditional complete large-order right absolute tail at j=0, on the
actual physical seed, genuine contour, and both explicit cutoff choices. -/
theorem preferred_actual_zeroth_right_mass_tail (d : PreferredBranchData) :
    ∃ B : PreferredCoareaBump d,∃ δB τ₀ ε₀ : ℝ,
      0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      PreferredRightCutoffData d B δB (preferredRightCutoff d δB) ∧
      ∀ τ : ℝ,0≤τ → τ<τ₀ → ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        Summable (preferredRightLargeMassTerms d B τ (preferredRightCutoff d δB) 0 0 ε) ∧
        (∑' m,preferredRightLargeMassTerms d B τ (preferredRightCutoff d δB) 0 0 ε m)≤A*(1+|Real.log ε|) := by
  obtain ⟨B,δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,hcut,hq⟩ := preferred_actual_zeroth_all_diameter_shell_bound d
  refine ⟨B,δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,hcut,?_⟩
  intro τ hτ hτr
  exact preferred_complete_right_mass_tail_of_q28 d B (preferredRightCutoff d δB) hcut 0
    (hq τ hτ hτr) 0 le_rfl

end
end IsingBulk.Preferred22
