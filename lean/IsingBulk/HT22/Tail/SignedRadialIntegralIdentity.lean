import IsingBulk.HT22.Tail.SignedRadialIntegralLimit
import IsingBulk.HT22.Tail.ZerothIdentity
import IsingBulk.HT22.Physical.WeightedAnalytic

/-! Actual signed right coefficient derivative identity from the proved
punctured recurrence and quantitative puncture errors. The remaining error
inputs are exposed explicitly for the genuine small-mass/flux producer. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def puncturedIntegral (negative : Bool) (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  signedLiftedIntegral (n:=n) (Physical.constraintAngle negative) B.delta
    (puncturedDensity (Physical.constraintSign negative) d B τ R rcut j) s

def punctureFluxIntegral (negative : Bool) (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  signedLiftedIntegral (n:=n) (Physical.constraintAngle negative) B.delta
    (fun t x => punctureFlux (Physical.constraintSign negative) τ preferredPopulationCutoff
      B.p B.m rcut j t R x) s

/-- This theorem assumes neither the desired derivative identity nor an
integral-derivative estimate. Its approximation hypotheses are the direct
value and flux bounds to be supplied by the actual q25/q27 mass estimates. -/
theorem right_integral_identity_of_puncture_errors (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (hτ : 0≤τ)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (radius : ℕ → ℝ) (k : ℕ) {ρ : ℝ} (hρ : 0≤ρ) (hρ1 : ρ<1)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (2*n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x)
    (hvalue : ∀ j : ℕ,j≤k → ∃ A : ℝ,0≤A ∧ ∀ m ε,ε∈Ioo 0 ε₀ →
      ‖puncturedIntegral negative (2*n) d B τ (radius m) rcut j (IsingBulk.Branch.radialParameter d.alpha ε)-
        transportedIntegral negative (2*n) B.delta τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|)*ρ^m)
    (hflux : ∀ j : ℕ,j<k → ∃ C : ℝ,0≤C ∧ ∀ m ε,ε∈Ioo 0 ε₀ →
      ‖punctureFluxIntegral negative (2*n) d B τ (radius m) rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|)*ρ^m) :
    ∀ j : ℕ,j≤k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      iteratedDeriv j (Physical.rightPopulationIntegral negative (2*n) τ preferredPopulationCutoff B.p B.m rcut)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      transportedIntegral negative (2*n) B.delta τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  let I := fun j => transportedIntegral negative (2*n) B.delta τ preferredPopulationCutoff B.p B.m rcut j
  let P := fun j m ε => puncturedIntegral negative (2*n) d B τ (radius m) rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε)
  let J := fun j m ε => punctureFluxIntegral negative (2*n) d B τ (radius m) rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε)
  apply physical_iteratedDeriv_eq_of_radial_derivatives d.alpha ε₀ _ I k
  · intro ε hε
    exact Physical.rightPopulationIntegral_analyticAt negative (2*n) d B hτ preferredPopulationCutoff rcut
      preferredPopulationCutoff_smooth hcut.2.2.1 (preferredRadialTrace_im_pos d hε.1)
  · intro ε hε
    exact (transportedIntegral_zero negative n d B τ hτ rcut hcut.2.2.2.1 _
      (preferredRadialTrace_im_pos d hε.1)).symm
  · intro j hj ε hε
    obtain ⟨A,hA,hv⟩ := hvalue j (by omega)
    obtain ⟨D,hD,hn⟩ := hvalue (j+1) (by omega)
    obtain ⟨C,hC,hf⟩ := hflux j hj
    apply hasDerivAt_of_puncture_log_errors (P j) (P (j+1)) (J j)
      (fun u => I j (IsingBulk.Branch.radialParameter d.alpha u))
      (fun u => I (j+1) (IsingBulk.Branch.radialParameter d.alpha u))
      (Complex.exp ((d.alpha:ℂ)*Complex.I)) (Complex.norm_exp_ofReal_mul_I d.alpha)
      hρ hρ1 hA hD hC ?_ hv hn hf hε
    intro m u hu
    exact punctured_signed_integral_radial_hasDerivAt (Physical.constraintAngle negative)
      (Physical.constraintSign negative) (by rw [Physical.constraintSign_norm]) d B (radius m) rcut hcut j hreg hu

end
end IsingBulk.HT22.Tail
