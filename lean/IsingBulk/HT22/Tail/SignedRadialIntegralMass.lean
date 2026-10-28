import IsingBulk.HT22.Tail.SignedRadialIntegralIdentity
import IsingBulk.HT22.Tail.PunctureGeometricControl

/-! Actual signed original-coefficient derivative identity with only genuine
absolute mass and primitive field bounds left as quantitative inputs. Value
approximation, puncture flux, local-uniform derivative limits, all Stokes
steps and the original physical zeroth identity are already proved. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

theorem right_integral_identity_of_smallMass (negative : Bool) (n : ℕ) (hn : 0<n)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (hτ : 0≤τ)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut) (k : ℕ)
    (hreg : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ x∈preferredRightAngularBox d B.delta δB (2*n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x)
    (hmass : ∀ j : ℕ,j≤k → ∀ ε : ℝ,0<ε → ε<ε₀ →
      (∫⁻ θ : Fin (2*n) → ℝ in angularBox (2*n),ENNReal.ofReal
        ‖transportedDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ))‖)<(⊤:ℝ≥0∞))
    (hsmall : ∀ j : ℕ,j≤k → ∃ F : ℝ,0<F ∧ ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin (2*n) → ℝ in angularBox (2*n),
        smallMassIntegrand (Physical.constraintAngle negative) (Physical.constraintSign negative)
          d B τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε) (preferredDyadicRadius m) θ)≤
        ENNReal.ofReal (F*(1+|Real.log ε|)*(1/8:ℝ)^m))
    {C : ℝ} (hC : 0<C)
    (hfield : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ θ : Fin (2*n+1) → ℝ,
      θ∈preferredRightAngularBox d B.delta δB (2*n+1) → 0<preferredAngularDiameter θ →
      ∀ i,‖angularField τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖≤
        C*((2*n+1:ℕ):ℝ)^2/preferredAngularDiameter θ) :
    ∀ j : ℕ,j≤k → ∀ ε : ℝ,0<ε → ε<ε₀ →
      iteratedDeriv j (Physical.rightPopulationIntegral negative (2*n) τ preferredPopulationCutoff B.p B.m rcut)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      transportedIntegral negative (2*n) B.delta τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  have hσ : ‖Physical.constraintSign negative‖≤1 := by rw [Physical.constraintSign_norm]
  have hval : ∀ j : ℕ,j≤k → ∃ A : ℝ,0≤A ∧ ∀ m ε,ε∈Ioo 0 ε₀ →
      ‖puncturedIntegral negative (2*n) d B τ (preferredDyadicRadius m) rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε)-
        transportedIntegral negative (2*n) B.delta τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|)*(1/2:ℝ)^m := by
    intro j hj
    obtain ⟨F,hF,hFs⟩ := hsmall j hj
    refine ⟨F,hF.le,?_⟩
    intro m ε hε
    have hv := puncture_value_log_geometric_of_smallMass (by omega : 0<2*n)
      (Physical.constraintAngle negative) (Physical.constraintSign negative) hσ d B rcut hcut j hF
      hreg (hmass j hj) hFs ε hε.1 hε.2 m
    simpa only [puncturedIntegral,signedLiftedIntegral,transportedIntegral,
      Physical.constrainedAngles,constrainedAtTotal] using hv
  have hflux : ∀ j : ℕ,j<k → ∃ L : ℝ,0≤L ∧ ∀ m ε,ε∈Ioo 0 ε₀ →
      ‖punctureFluxIntegral negative (2*n) d B τ (preferredDyadicRadius m) rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤L*(1+|Real.log ε|)*(1/2:ℝ)^m := by
    intro j hj
    obtain ⟨F,hF,hFs⟩ := hsmall j (by omega)
    obtain ⟨L,hL,hLb⟩ := puncture_flux_log_geometric_of_smallMass (Physical.constraintAngle negative)
      (Physical.constraintSign negative) d B rcut hcut j hF hC hFs hfield
    exact ⟨L,hL.le,fun m ε hε => hLb ε hε.1 hε.2 m⟩
  have hi := right_integral_identity_of_puncture_errors negative n d B hτ rcut hcut preferredDyadicRadius k
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
    (fun ε hε => hreg ε hε.1 hε.2) hval hflux
  exact fun j hj ε hε hεr => hi j hj ε ⟨hε,hεr⟩

end
end IsingBulk.HT22.Tail
