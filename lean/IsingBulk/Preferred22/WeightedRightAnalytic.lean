import IsingBulk.Preferred22.WeightedEqualitySupport
import IsingBulk.Preferred22.WeightedIntegralAnalytic

/-! The literal smoothly weighted right integral is holomorphic in the
physical parameter. Its genuine lifted multiplier is continuous because
the upper population plateau removes every modular seam. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def preferredWeightedRightIntegral (n : ℕ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  ∫ θ in angularBox n,preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j s
    (preferredLiftedAngles B.delta (constrainedAngles θ))

def preferredWeightedRightRadialIntegral (n : ℕ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (ε : ℝ) : ℂ :=
  preferredWeightedRightIntegral n d B ψ τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε)

theorem preferredBareContourDensity_lift {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredBareContourDensity τ p m s (preferredLiftedAngles δ θ)=
      preferredBareContourDensity τ p m s θ := by
  simp only [preferredBareContourDensity,preferred_contourMatrix_lift τ δ p m hp hm,
    preferred_deformedDensity_lift τ δ p m hp hm]

/-- The multiplier need not be periodic: the actual one-sided lift and the
population zero germ give a continuous weight on the original torus. -/
theorem preferredWeighted_lifted_weight_continuous {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ψ : (Fin N → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) :
    Continuous (fun θ : Fin N → ℝ => ψ (preferredLiftedAngles B.delta θ)*
      (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut (preferredLiftedAngles B.delta θ):ℂ)) := by
  let F := fun z : ℂ × (Fin N → ℝ) => ψ z.2*
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut z.2:ℂ)
  have hF : ContDiff ℝ ∞ F := (hψ.comp contDiff_snd).mul
    (Complex.ofRealCLM.contDiff.comp
      ((preferredCellWeight_contDiff .right preferredPopulationCutoff B.p B.m rcut
        preferredPopulationCutoff_smooth B.smooth B.m_smooth hr).comp contDiff_snd))
  have hzero : ∀ s θ i,1/2<B.p (θ i) → F (s,θ)=0 := by
    intro s θ i hi
    have hP : 1/2≤occupancy B.p θ := hi.le.trans
      (Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun v _ => B.lower_bound (θ v)) (Finset.mem_univ i))
    simp only [F,preferredCellWeight,preferredLowerWeight,lowerWeight,
      preferredPopulationCutoff_one hP,sub_self,zero_mul,zero_div,Complex.ofReal_zero,mul_zero]
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hh := preferredLiftedFunction_contDiffAt d B F hzero 0 θ (fun _ => hF.contDiffAt)
  exact (hh.comp θ (contDiffAt_const.prodMk contDiffAt_id)).continuousAt

/-- Actual complex analyticity of the full weighted zeroth integral,
including normalization and all real cutoffs, without an analytic-bump premise. -/
theorem preferredWeightedRightIntegral_zero_analyticAt (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (preferredWeightedRightIntegral n d B ψ τ rcut 0) s := by
  let w := fun θ : Fin (n+1) → ℝ => ψ (preferredLiftedAngles B.delta θ)*
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut (preferredLiftedAngles B.delta θ):ℂ)
  have hi := preferred_weighted_contour_integral_analyticAt n d B hτ w
    (preferredWeighted_lifted_weight_continuous d B ψ hψ rcut hr) hS
  have he : preferredWeightedRightIntegral n d B ψ τ rcut 0=
      fun t : ℂ => ∫ θ in angularBox n,w (constrainedAngles θ)*
        preferredBareContourDensity τ B.p B.m t (constrainedAngles θ) := by
    funext t
    unfold preferredWeightedRightIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => by
      simp only [preferredWeightedPhysicalDensity,preferredPhysicalSeed,preferredBareContourDensity,
        preferred_contourMatrix_lift τ B.delta B.p B.m B.periodic B.m_periodic,
        preferred_deformedDensity_lift τ B.delta B.p B.m B.periodic B.m_periodic,w]
      ring
  rw [he]
  exact hi

end
end IsingBulk.Preferred22
