import IsingBulk.Preferred22.OuterRightDerivativeLog

/-! Exact decomposition of the physical right integral into an original
fixed smooth multiplier and its complement. Both integrals are genuine
and integrable; complex derivative identities follow from their actual
analytic germs along the physical radial path. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredWeightedRightSeed_continuous (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) :
    Continuous (fun θ : Fin n → ℝ => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff
      B.p B.m rcut 0 (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAngles θ))) := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let w := fun θ : Fin (n+1) → ℝ => ψ (preferredLiftedAngles B.delta θ)*
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut (preferredLiftedAngles B.delta θ):ℂ)
  have hw : Continuous w := preferredWeighted_lifted_weight_continuous d B ψ hψ rcut hr
  have he : (fun θ : Fin n → ℝ => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff
      B.p B.m rcut 0 s (preferredLiftedAngles B.delta (constrainedAngles θ)))=
      fun θ => w (constrainedAngles θ)*preferredBareContourDensity τ B.p B.m s (constrainedAngles θ) := by
    funext θ
    simp only [preferredWeightedPhysicalDensity,preferredPhysicalSeed,preferredBareContourDensity,
      preferred_contourMatrix_lift τ B.delta B.p B.m B.periodic B.m_periodic,
      preferred_deformedDensity_lift τ B.delta B.p B.m B.periodic B.m_periodic,w]
    ring
  change Continuous (fun θ : Fin n → ℝ => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff
    B.p B.m rcut 0 s (preferredLiftedAngles B.delta (constrainedAngles θ)))
  rw [he]
  exact (hw.comp (constrainedAngles_continuous n)).mul
    ((preferredBareContourDensity_continuous (by omega) d B hε hτ).comp (constrainedAngles_continuous n))

theorem preferredWeightedRightIntegral_one (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ) (rcut : ℝ → ℝ) :
    preferredWeightedRightIntegral n d B (fun _ => 1) τ rcut 0=
      preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut 0 := by
  funext s
  unfold preferredWeightedRightIntegral preferredTransportedIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by
    simp only [preferredWeightedPhysicalDensity,preferredTransportedDensity_zero,one_mul])

/-- The actual full right zeroth integral is the sum of the two original
weighted integrals, without omitted lift or Jacobian terms. -/
theorem preferredWeightedRightIntegral_partition (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) :
    preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut 0
      (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredWeightedRightIntegral n d B ψ τ rcut 0 (IsingBulk.Branch.radialParameter d.alpha ε)+
      preferredWeightedRightIntegral n d B (fun θ => 1-ψ θ) τ rcut 0
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  have hi := continuous_integrableOn_angularBox (preferredWeightedRightSeed_continuous n d B hε hτ ψ hψ rcut hr)
  have hj := continuous_integrableOn_angularBox (preferredWeightedRightSeed_continuous n d B hε hτ
    (fun θ => 1-ψ θ) (contDiff_const.sub hψ) rcut hr)
  unfold preferredWeightedRightIntegral
  rw [←integral_add hi hj]
  unfold preferredTransportedIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    simp only [preferredWeightedPhysicalDensity,preferredTransportedDensity_zero]
    ring

/-- Every genuine complex derivative of the physical right integral
splits into the derivatives of the original multiplier and its complement. -/
theorem preferredWeightedRightIntegral_derivative_partition (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (j : ℕ) {ε : ℝ} (hε : 0<ε) :
    iteratedDeriv j (preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff
      B.p B.m rcut 0) (IsingBulk.Branch.radialParameter d.alpha ε)=
      iteratedDeriv j (preferredWeightedRightIntegral n d B ψ τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)+
      iteratedDeriv j (preferredWeightedRightIntegral n d B (fun θ => 1-ψ θ) τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  let F := preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut 0
  let G := preferredWeightedRightIntegral n d B ψ τ rcut 0
  let H := preferredWeightedRightIntegral n d B (fun θ => 1-ψ θ) τ rcut 0
  have hf (t : ℝ) (ht : 0<t) : AnalyticAt ℂ F (IsingBulk.Branch.radialParameter d.alpha t) := by
    dsimp only [F]
    rw [←preferredWeightedRightIntegral_one n d B τ rcut]
    exact preferredWeightedRightIntegral_zero_analyticAt n d B hτ (fun _ => 1) contDiff_const
      rcut hr (preferredRadialTrace_im_pos d ht)
  have hg (t : ℝ) (ht : 0<t) : AnalyticAt ℂ G (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredWeightedRightIntegral_zero_analyticAt n d B hτ ψ hψ rcut hr (preferredRadialTrace_im_pos d ht)
  have hh (t : ℝ) (ht : 0<t) : AnalyticAt ℂ H (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredWeightedRightIntegral_zero_analyticAt n d B hτ _ (contDiff_const.sub hψ)
      rcut hr (preferredRadialTrace_im_pos d ht)
  have hgh (t : ℝ) (ht : 0<t) : AnalyticAt ℂ (fun s => G s+H s)
      (IsingBulk.Branch.radialParameter d.alpha t) := (hg t ht).add (hh t ht)
  have he : ∀ t : ℝ,0<t → F (IsingBulk.Branch.radialParameter d.alpha t)=
      G (IsingBulk.Branch.radialParameter d.alpha t)+H (IsingBulk.Branch.radialParameter d.alpha t) :=
    fun t ht => preferredWeightedRightIntegral_partition n d B ht hτ ψ hψ rcut hr
  have hcongr := preferred_radial_iteratedDeriv_congr
    (F := F) (G := fun s => G s+H s) (Complex.exp_ne_zero ((d.alpha:ℂ)*Complex.I))
    (by simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hf)
    (by simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using
      hgh)
    (by simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using he) j ε hε
  change iteratedDeriv j F _=iteratedDeriv j G _+iteratedDeriv j H _
  have hcongr' : iteratedDeriv j F (IsingBulk.Branch.radialParameter d.alpha ε)=
      iteratedDeriv j (fun s => G s+H s) (IsingBulk.Branch.radialParameter d.alpha ε) := by
    simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hcongr
  rw [hcongr',iteratedDeriv_fun_add (hg ε hε).contDiffAt (hh ε hε).contDiffAt]

end
end IsingBulk.Preferred22
