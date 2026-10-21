import IsingBulk.HT.Contour.OnsiteSmooth
import IsingBulk.Tail.SelectorIntegration

/-! Periodic onsite flux cancellation, retaining the exact named multiplier. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

 theorem onsiteHomotopyFlux_eq_contour {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (q : Fin N) :
    onsiteHomotopyFlux f r τ lam s θ q =
      (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
      (∏ i, deformedPoint f r τ lam θ i)*
      onsiteCanceledDensity (fun i => globalRoot s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ)*
      ((angularJacobian f τ lam θ).updateCol q (complexShift f τ θ)).det := by
  unfold onsiteHomotopyFlux onsiteLogDensity
  rw [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
    funext (deformedPoint_exp_log f hr τ lam θ)]

 theorem onsiteHomotopyFlux_periodic (N : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (q : Fin N) :
    CoordinatePeriodic N (fun θ => onsiteHomotopyFlux f r τ lam s θ q) := by
  intro θ i
  dsimp only
  rw [onsiteHomotopyFlux_eq_contour f hr,onsiteHomotopyFlux_eq_contour f hr,
    deformedPoint_periodic f hf,angularJacobian_periodic f hf]
  have he : complexShift f τ (Function.update θ i (θ i+2*Real.pi)) = complexShift f τ θ := by
    unfold complexShift
    rw [shiftMap_periodic f hf]
  rw [he]

 theorem onsite_source_flux_contDiff {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (q : Fin N) :
    ContDiff ℝ ∞ (fun θ => onsiteHomotopyFlux f r τ lam s θ q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have h := onsiteHomotopyFlux_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ q
  exact h.comp θ (contDiffAt_const.prodMk contDiffAt_id)

 theorem onsite_source_spatial_current (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    (∫ θ in angleBox (n+1), (angularSelector f θ:ℂ)*
      deriv (fun u => onsitePulledDensity f r τ u s θ) lam) =
      ∫ θ in angleBox (n+1), ∑ i, onsiteNamedCurrentDensity f r τ lam s i θ := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := fun θ i => onsiteHomotopyFlux f r τ lam s θ i
  have hF (i : Fin (n+1)) : ContDiff ℝ ∞ (fun θ => F θ i) :=
    onsite_source_flux_contDiff (by omega) f hf hr hr1 hτ hlam s hmargin i
  have hpoint (θ : Fin (n+1) → ℝ) :
      deriv (fun u => onsitePulledDensity f r τ u s θ) lam = IsingBulk.Lie.divergence F θ := by
    rw [onsite_source_pointwise_conservation (by omega) f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero]
    exact (divergence_eq_coords F (fun i => (hF i).differentiable (by simp)) θ).symm
  have hi := periodic_weighted_integration_by_parts (fun θ => (angularSelector f θ:ℂ)) F
    (complexSelector_contDiff f hf) hF
    (fun θ i => congrArg Complex.ofReal (angularSelector_periodic f hf θ i))
    (fun i => onsiteHomotopyFlux_periodic (n+1) f hf hr τ lam s i)
  have hsum (θ : Fin (n+1) → ℝ) : (∑ i, onsiteNamedCurrentDensity f r τ lam s i θ) =
      -(∑ i, coordDeriv (fun x => (angularSelector f x:ℂ)) θ i*F θ i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [coordDeriv_selector f hf]
    by_cases hd : namedSelectorDerivative f i θ = 0
    · simp [onsiteNamedCurrentDensity,hd]
    · obtain ⟨hp,hp',hm,hm'⟩ := hf.named (θ i) (namedSelectorDerivative_support f θ i hd).1
      dsimp [F]
      rw [onsiteHomotopyFlux_named f hr τ lam s θ i hp hp' hm hm']
      unfold onsiteNamedCurrentDensity
      ring
  simp_rw [hpoint,hsum,integral_neg]
  exact hi

 theorem onsite_source_spatial_unweighted (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    (∫ θ in angleBox (n+1), deriv (fun u => onsitePulledDensity f r τ u s θ) lam) = 0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := fun θ i => onsiteHomotopyFlux f r τ lam s θ i
  have hF (i : Fin (n+1)) : ContDiff ℝ ∞ (fun θ => F θ i) :=
    onsite_source_flux_contDiff (by omega) f hf hr hr1 hτ hlam s hmargin i
  have hpoint (θ : Fin (n+1) → ℝ) :
      deriv (fun u => onsitePulledDensity f r τ u s θ) lam = IsingBulk.Lie.divergence F θ := by
    rw [onsite_source_pointwise_conservation (by omega) f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero]
    exact (divergence_eq_coords F (fun i => (hF i).differentiable (by simp)) θ).symm
  simp_rw [hpoint]
  exact periodic_divergence_integral_zero F hF
    (fun i => onsiteHomotopyFlux_periodic (n+1) f hf hr τ lam s i)

end
end IsingBulk.HT.Contour
