import IsingBulk.HT.Contour.SignedSmooth
import IsingBulk.Tail.SelectorIntegration

/-! Signed periodic flux cancellation and actual named current. The real
cutoff and full replacement-minor flux are differentiated in the existing
fixed-torus integration-by-parts theorem. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def signedSelectedIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, ((1-angularSelector f θ:ℝ):ℂ)*signedPulledDensity σ f r τ 1 s θ

def signedOriginalLowerIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (angularSelector f θ:ℂ)*signedPulledDensity σ f r τ 0 s θ

def signedNamedCurrentDensity {N : ℕ} (σ : ℂ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)*signedPulledDensity σ f r τ lam s θ

def signedCurrentIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) : ℂ :=
  ∫ lam : ℝ in 0..1, ∑ q : Fin N, ∫ θ in angleBox N,
    signedNamedCurrentDensity σ f r τ lam s q θ

 theorem signedHomotopyFlux_eq_contour {N : ℕ} (σ : ℂ) (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (q : Fin N) :
    signedHomotopyFlux σ f r τ lam s θ q =
      (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
      (∏ i, deformedPoint f r τ lam θ i)*
      signedCanceledDensity σ (fun i => globalRoot s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ)*
      ((angularJacobian f τ lam θ).updateCol q (complexShift f τ θ)).det := by
  unfold signedHomotopyFlux signedLogDensity
  rw [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
    funext (deformedPoint_exp_log f hr τ lam θ)]

 theorem signedHomotopyFlux_periodic (N : ℕ) (σ : ℂ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (q : Fin N) :
    CoordinatePeriodic N (fun θ => signedHomotopyFlux σ f r τ lam s θ q) := by
  intro θ i
  dsimp only
  rw [signedHomotopyFlux_eq_contour σ f hr,signedHomotopyFlux_eq_contour σ f hr,
    deformedPoint_periodic f hf,angularJacobian_periodic f hf]
  have he : complexShift f τ (Function.update θ i (θ i+2*Real.pi)) = complexShift f τ θ := by
    unfold complexShift
    rw [shiftMap_periodic f hf]
  rw [he]

 theorem signed_source_flux_contDiff (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (q : Fin N) :
    ContDiff ℝ ∞ (fun θ => signedHomotopyFlux σ f r τ lam s θ q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have h := signedHomotopyFlux_joint_contDiffAt σ hσ hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ q
  exact h.comp θ (contDiffAt_const.prodMk contDiffAt_id)

 theorem signed_source_spatial_current (σ : ℂ) (hσ : ‖σ‖ = 1) (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    (∫ θ in angleBox (n+1), (angularSelector f θ:ℂ)*
      deriv (fun u => signedPulledDensity σ f r τ u s θ) lam) =
      ∫ θ in angleBox (n+1), ∑ i, signedNamedCurrentDensity σ f r τ lam s i θ := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := fun θ i => signedHomotopyFlux σ f r τ lam s θ i
  have hF (i : Fin (n+1)) : ContDiff ℝ ∞ (fun θ => F θ i) :=
    signed_source_flux_contDiff σ hσ (by omega) f hf hr hr1 hτ hlam s hmargin i
  have hpoint (θ : Fin (n+1) → ℝ) :
      deriv (fun u => signedPulledDensity σ f r τ u s θ) lam = IsingBulk.Lie.divergence F θ := by
    rw [signed_source_pointwise_conservation σ hσ (by omega) f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero]
    exact (divergence_eq_coords F (fun i => (hF i).differentiable (by simp)) θ).symm
  have hi := periodic_weighted_integration_by_parts (fun θ => (angularSelector f θ:ℂ)) F
    (complexSelector_contDiff f hf) hF
    (fun θ i => congrArg Complex.ofReal (angularSelector_periodic f hf θ i))
    (fun i => signedHomotopyFlux_periodic (n+1) σ f hf hr τ lam s i)
  have hsum (θ : Fin (n+1) → ℝ) : (∑ i, signedNamedCurrentDensity σ f r τ lam s i θ) =
      -(∑ i, coordDeriv (fun x => (angularSelector f x:ℂ)) θ i*F θ i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [coordDeriv_selector f hf]
    by_cases hd : namedSelectorDerivative f i θ = 0
    · simp [signedNamedCurrentDensity,hd]
    · obtain ⟨hp,hp',hm,hm'⟩ := hf.named (θ i) (namedSelectorDerivative_support f θ i hd).1
      dsimp [F]
      rw [signedHomotopyFlux_named σ f hr τ lam s θ i hp hp' hm hm']
      unfold signedNamedCurrentDensity
      ring
  simp_rw [hpoint,hsum,integral_neg]
  exact hi

 theorem signed_source_spatial_unweighted (σ : ℂ) (hσ : ‖σ‖ = 1) (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    (∫ θ in angleBox (n+1), deriv (fun u => signedPulledDensity σ f r τ u s θ) lam) = 0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := fun θ i => signedHomotopyFlux σ f r τ lam s θ i
  have hF (i : Fin (n+1)) : ContDiff ℝ ∞ (fun θ => F θ i) :=
    signed_source_flux_contDiff σ hσ (by omega) f hf hr hr1 hτ hlam s hmargin i
  have hpoint (θ : Fin (n+1) → ℝ) :
      deriv (fun u => signedPulledDensity σ f r τ u s θ) lam = IsingBulk.Lie.divergence F θ := by
    rw [signed_source_pointwise_conservation σ hσ (by omega) f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero]
    exact (divergence_eq_coords F (fun i => (hF i).differentiable (by simp)) θ).symm
  simp_rw [hpoint]
  exact periodic_divergence_integral_zero F hF
    (fun i => signedHomotopyFlux_periodic (n+1) σ f hf hr τ lam s i)

end
end IsingBulk.HT.Contour
