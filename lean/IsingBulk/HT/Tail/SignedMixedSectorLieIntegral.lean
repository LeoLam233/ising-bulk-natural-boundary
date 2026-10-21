import IsingBulk.Tail.MixedSectorLieIntegral
import IsingBulk.HT.Tail.SignedMixedSmooth
import IsingBulk.HT.Tail.SignedCompactSectorIntegralBridge

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set MeasureTheory Metric Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem signed_original_mixed_sector_lie_integral (ζ : ℂ) (hζ : ‖ζ‖ = 1) (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (outer : ℝ) (ho : 0<outer) (cap : ℝ) (hcap : 0<cap) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (n : ℕ) (eps τ : ℝ) (j q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      0<eps → eps<e → 0≤τ → sigma j=2 →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      SectorLieIntegralIdentity (ball (radialParameter d.theta eps) (c*eps))
        (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0)
        (fun s θ => originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*signedPulledDensity ζ f r τ 0 s θ) := by
  obtain ⟨inner₀,hi₀,hicap,hDomain⟩ := mixed_original_sector_domain d hcsmall outer ho cap hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨c,e,hc,hcsmall',he,hDomain⟩ := hDomain inner hi hinner
  refine ⟨c,e,hc,hcsmall',he,?_⟩
  intro η α hη hηsmall hα hαsmall n eps τ j q sigma heps hepslt hτ hσj
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let J := mixedBranchIndexSet sigma
  let Ω := mixedSeparatedDomain J j q f r τ 0
  let U := ball (radialParameter d.theta eps) (c*eps)
  let w := originalMixedWeight f d.thetaB outer inner ho hi q sigma
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hr : 0<r := Real.exp_pos _
  have hΩ : IsOpen Ω := mixedSeparatedDomain_isOpen J j q f hr τ 0 hf.p_smooth hf.m_smooth
  have hcover : U ×ˢ tsupport w⊆Ω := by
    rintro p ⟨hpU,hpw⟩
    apply hDomain η α hη hηsmall hα hαsmall (n+1) eps τ p.2 j q sigma p.1 (by omega)
      heps hepslt hτ hσj (originalMixedWeight_support f d.thetaB outer inner ho hi q sigma hpw)
    exact (show ‖p.1-radialParameter d.theta eps‖<c*eps by simpa only [U,mem_ball,dist_eq_norm] using hpU).le
  dsimp only
  intro k
  exact supported_periodic_lie_integral hΩ isOpen_ball
    (mixedContourVelocity J j q f r τ 0) (signedPulledDensity ζ f r τ 0) w
    (originalMixedWeight_smooth f hf d.thetaB outer inner ho hi q sigma)
    (signed_mixedSeparated_density_smooth ζ hζ (Nat.succ_pos n) J j q f hr τ 0 hf.p_smooth hf.m_smooth
      (fun x => homotopy_y_product_lt_one (Nat.succ_pos n) f hr
        (Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])) hτ le_rfl x hf.p_nonneg hf.m_le_one))
    (fun i => mixedSeparated_velocity_smooth J j q f hr τ 0 hf.p_smooth hf.m_smooth i)
    hcover (originalMixedWeight_periodic f hf d.thetaB outer inner ho hi q sigma)
    (fun s => signedPulledDensity_periodic ζ (n+1) f hf r τ 0 s)
    (fun s i => mixedContourVelocity_periodic J j q f hf r τ 0 s i) k

theorem signed_current_mixed_sector_lie_integral (ζ : ℂ) (hζ : ‖ζ‖ = 1) (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (outer : ℝ) (ho : 0<outer) (n : ℕ) (eps τ lam : ℝ) (j qS a : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → sigma j=2 →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      SectorLieIntegralIdentity (ball (radialParameter d.theta eps) (c*eps))
        (mixedContourVelocity (mixedBranchIndexSet sigma) j qS f r τ lam)
        (fun s θ => currentMixedWeight f d.thetaB outer inner ho hi qS a sigma τ θ*signedPulledDensity ζ f r τ lam s θ) := by
  obtain ⟨inner₀,hi₀,hicap,hDomain⟩ := mixed_current_sector_domain d hcsmall cap hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨c,e,t₀,hc,hcsmall',he,ht,hDomain⟩ := hDomain inner hi hinner
  refine ⟨c,e,t₀,hc,hcsmall',he,ht,?_⟩
  intro η α hη hηsmall hα hαsmall outer ho n eps τ lam j qS a sigma heps hepslt hτ hl0 hl1 htl hσj
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let J := mixedBranchIndexSet sigma
  let Ω := mixedSeparatedDomain J j qS f r τ lam
  let U := ball (radialParameter d.theta eps) (c*eps)
  let w := currentMixedWeight f d.thetaB outer inner ho hi qS a sigma τ
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hr : 0<r := Real.exp_pos _
  have hΩ : IsOpen Ω := mixedSeparatedDomain_isOpen J j qS f hr τ lam hf.p_smooth hf.m_smooth
  have hcover : U ×ˢ tsupport w⊆Ω := by
    rintro p ⟨hpU,hpw⟩
    apply hDomain η α hη hηsmall hα hαsmall (n+1) eps τ lam p.2 j qS sigma p.1 (by omega)
      heps hepslt hτ hl0 hl1 htl hσj (currentMixedWeight_support f d.thetaB outer inner ho hi qS a sigma τ hpw)
    exact (show ‖p.1-radialParameter d.theta eps‖<c*eps by simpa only [U,mem_ball,dist_eq_norm] using hpU).le
  dsimp only
  intro k
  exact supported_periodic_lie_integral hΩ isOpen_ball
    (mixedContourVelocity J j qS f r τ lam) (signedPulledDensity ζ f r τ lam) w
    (currentMixedWeight_smooth f hf d.thetaB outer inner ho hi qS a sigma τ)
    (signed_mixedSeparated_density_smooth ζ hζ (Nat.succ_pos n) J j qS f hr τ lam hf.p_smooth hf.m_smooth
      (fun x => homotopy_y_product_lt_one (Nat.succ_pos n) f hr
        (Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])) hτ hl0 x hf.p_nonneg hf.m_le_one))
    (fun i => mixedSeparated_velocity_smooth J j qS f hr τ lam hf.p_smooth hf.m_smooth i)
    hcover (currentMixedWeight_periodic f hf d.thetaB outer inner ho hi qS a sigma τ)
    (fun s => signedPulledDensity_periodic ζ (n+1) f hf r τ lam s)
    (fun s i => mixedContourVelocity_periodic J j qS f hf r τ lam s i) k


end
end IsingBulk.HT.Tail
