import IsingBulk.HT.Contour.OnsiteLieSupport
import IsingBulk.Tail.MixedSectorLieIntegral

/-! Actual supported periodic Lie transport for onsite K and every named
current. The full source and the branch-freezing field are proved smooth
and periodic; the support cover is derived from actual contour geometry. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Lie Set Filter MeasureTheory Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem onsite_weighted_lie_stages_smooth {n : ℕ} (J : Finset (Fin (n+1)))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : ContDiff ℝ ∞ w) (k : ℕ) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      ((lieStep (onsiteBranchField J f r τ lam))^[k]
        (fun s θ => w θ*onsitePulledDensity f r τ lam s θ)) := by
  have hΩ := onsiteLieDomain_isOpen J f hr τ lam hp hm
  have hD := onsiteLie_density_smooth J f hr τ lam hp hm
  have hWeight := ParameterSmoothOn.angular (onsiteLieDomain J f r τ lam) w hw
  exact (hWeight.mul hD).iterate_lieStep hΩ (onsiteBranchField J f r τ lam) _
    (fun i => onsiteLie_field_smooth J f hr τ lam hp hm i) k

/-- Local abstract-weight interface with the physical source and field
already discharged. Concrete source support covers occur in the endpoint
below, so no source-domain or integration-by-parts premise remains there. -/
theorem onsite_supported_periodic_lie_integral {n : ℕ} (J : Finset (Fin (n+1)))
    (f : SelectorFunctions) (hf : RegularSelector f) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    {U : Set ℂ} (hU : IsOpen U) (w : (Fin (n+1) → ℝ) → ℂ)
    (hw : ContDiff ℝ ∞ w) (hwper : CoordinatePeriodic (n+1) w)
    (hcover : U ×ˢ tsupport w⊆onsiteLieDomain J f r τ lam) :
    SectorLieIntegralIdentity U (onsiteBranchField J f r τ lam)
      (fun s θ => w θ*onsitePulledDensity f r τ lam s θ) := by
  intro k
  exact supported_periodic_lie_integral
    (onsiteLieDomain_isOpen J f hr τ lam hf.p_smooth hf.m_smooth) hU
    (onsiteBranchField J f r τ lam) (onsitePulledDensity f r τ lam) w hw
    (onsiteLie_density_smooth J f hr τ lam hf.p_smooth hf.m_smooth)
    (fun i => onsiteLie_field_smooth J f hr τ lam hf.p_smooth hf.m_smooth i)
    hcover hwper (fun s => onsitePulledDensity_periodic (n+1) f hf r τ lam s)
    (fun s i => onsiteBranchField_periodic J f hf r τ lam s i) k

/-- All particle orders and every homotopy slice use one actual supported
Lie theorem. Taking lam=0 gives K. The second component includes the literal
named current multiplier and applies for every lam in the fixed interval. -/
theorem onsite_actual_sector_lie_integrals (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ c e t₀ : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α inner : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ hi : 0< inner,inner≤(Real.sin d.thetaB)^2/4 →
      ∀ (n : ℕ) (eps τ lam : ℝ) (q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let U := ball (radialParameter d.theta eps) (c*eps)
      let V := onsiteBranchField (mixedBranchIndexSet sigma) f r τ lam
      SectorLieIntegralIdentity U V (fun s θ =>
        onsiteOriginalSectorWeight f d.thetaB inner hi sigma θ*onsitePulledDensity f r τ lam s θ) ∧
      SectorLieIntegralIdentity U V (fun s θ =>
        onsiteNamedSectorWeight f d.thetaB inner hi q sigma τ θ*onsitePulledDensity f r τ lam s θ) := by
  obtain ⟨c,e,t₀,hc,hcsmall',he,ht,hcover⟩ := onsite_sector_support_covers d hcsmall
  refine ⟨c,e,t₀,hc,hcsmall',he,ht,?_⟩
  intro η α inner hη hηsmall hα hαsmall hi his n eps τ lam q sigma heps hepslt hτ hl0 hl1 htl
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  obtain ⟨hK,hS⟩ := hcover η α inner hη hηsmall hα hαsmall hi his n eps τ lam q sigma
    heps hepslt hτ hl0 hl1 htl
  exact ⟨onsite_supported_periodic_lie_integral (mixedBranchIndexSet sigma) f hf
      (Real.exp_pos _) τ lam isOpen_ball _
      (onsiteOriginalSectorWeight_smooth f hf d.thetaB inner hi sigma)
      (onsiteOriginalSectorWeight_periodic f hf d.thetaB inner hi sigma) hK,
    onsite_supported_periodic_lie_integral (mixedBranchIndexSet sigma) f hf
      (Real.exp_pos _) τ lam isOpen_ball _
      (onsiteNamedSectorWeight_smooth f hf d.thetaB inner hi q sigma τ)
      (onsiteNamedSectorWeight_periodic f hf d.thetaB inner hi q sigma τ) hS⟩

/-- Exact physical named current, with no signed/global-kernel quotient. -/
theorem onsiteNamedSectorWeight_density {N : ℕ} (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    onsiteNamedSectorWeight f b inner hi q sigma τ θ*onsitePulledDensity f r τ lam s θ=
      (sectorAssignmentWeight b inner hi sigma θ:ℂ)*onsiteNamedCurrentDensity f r τ lam s q θ := by
  unfold onsiteNamedSectorWeight onsiteNamedCurrentDensity
  push_cast
  ring

end
end IsingBulk.HT.Contour
