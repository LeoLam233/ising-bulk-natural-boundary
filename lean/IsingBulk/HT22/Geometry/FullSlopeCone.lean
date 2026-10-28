import IsingBulk.HT22.Geometry.OccupancySlope

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter Set IsingBulk.Preferred22

/-- Full right-contour inverse-slope cone, including the negative branch
sliver and every fixed occupancy in [0,1]. No covariance separation is
assumed. The lower bound retains the actual branch displacement τσ. -/
theorem occupancyInverseV_full_cone (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c a ρ ε₀ τ₀ δB : ℝ, 0<c ∧ 0<a ∧ 0<ρ ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ ε τ σ υ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → σ∈Icc 0 1 → υ∈Icc 0 1 →
      let f := occupancyInverseV d B.m B.p ε τ σ υ
      (∀ θ∈Icc (-d.b-δB) B.delta, HasDerivAt f (deriv f θ) θ) ∧
      ContinuousOn (deriv f) (Icc (-d.b-δB) B.delta) ∧
      ∀ θ∈Icc (-d.b-δB) B.delta,
        (1/5:ℝ)*‖deriv f θ‖ ≤ (covarianceDirection*deriv f θ).re ∧
        (if |θ+d.b|<ρ then c/Real.sqrt (|θ+d.b|+ε+τ*σ) else a) ≤ (covarianceDirection*deriv f θ).re := by
  obtain ⟨c,C,r,hc,_hC,hr,hbranch⟩ := sourceInverseV_branch_estimates d
  let ρ := min (r/2) (min (preferredBranchPlateauWidth d B/2) (B.delta/2))
  have hρ : 0<ρ := by dsimp [ρ]; positivity [preferredBranchPlateauWidth_pos d B,B.delta_pos]
  have hρr : ρ<r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρw : ρ<preferredBranchPlateauWidth d B :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
      (by linarith [preferredBranchPlateauWidth_pos d B])
  have hρδ : ρ<B.delta := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_right _ _)) (by linarith [B.delta_pos])
  obtain ⟨a,M,q,ha,_hM,hq,hcompact⟩ := compact_inverse_source_estimate d
    B.m B.p (deriv B.m) (deriv B.p) B.m_smooth.continuous B.smooth.continuous
    (B.m_smooth.continuous_deriv (by simp)) (B.smooth.continuous_deriv (by simp))
    (ρ:=ρ/2) (δR:=B.delta) (by positivity)
    (by linarith [B.delta_b,d.b_pos]) (by linarith [B.delta_alpha,d.alpha_pos])
  obtain ⟨e,he,hregular⟩ := occupancyInverseV_angular_regular d B
  let ε₀ := min r (min q e)
  let τ₀ := min r q
  let δB := ρ/2
  have hε₀ : 0<ε₀ := lt_min hr (lt_min hq he)
  have hτ₀ : 0<τ₀ := lt_min hr hq
  refine ⟨c,a,ρ,ε₀,τ₀,δB,hc,ha,hρ,hε₀,hτ₀,by dsimp [δB]; positivity,
    by dsimp [δB]; linarith,?_⟩
  intro ε τ σ υ hε hεr hτ hτr hσ hυ
  let f := occupancyInverseV d B.m B.p ε τ σ υ
  have hepsr : ε<r := hεr.trans_le (min_le_left _ _)
  have hepsq : ε<q := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepse : ε<e := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htaur : τ<r := hτr.trans_le (min_le_left _ _)
  have htauq : τ<q := hτr.trans_le (min_le_right _ _)
  have hreg (θ : ℝ) (hθ : θ∈Icc (-d.b-δB) B.delta) :
      AngularInverseRegular (preferredRadialTrace d ε) (preferredBumpAngle B.m B.p τ σ υ θ) := by
    apply hregular ε τ σ υ θ hε hepse hτ hσ.1 hυ.1
    exact ⟨by dsimp [δB] at hθ; linarith [hθ.1,d.b_lt],hθ.2⟩
  have hder (θ : ℝ) (hθ : θ∈Icc (-d.b-δB) B.delta) := occupancyInverseV_hasDerivAt d
    ((contDiff_infty_iff_deriv.mp B.m_smooth).1 θ).hasDerivAt
    ((contDiff_infty_iff_deriv.mp B.smooth).1 θ).hasDerivAt (hreg θ hθ)
  refine ⟨fun θ hθ => (hder θ hθ).differentiableAt.hasDerivAt,
    fun θ hθ => (occupancyInverseV_deriv_continuousAt d B (hreg θ hθ)).continuousWithinAt,?_⟩
  intro θ hθ
  by_cases hu : |θ+d.b|<ρ
  · have hδ : 0≤τ*σ := mul_nonneg hτ hσ.1
    have hδr : τ*σ<r := (mul_le_of_le_one_right hτ hσ.2).trans_lt htaur
    obtain ⟨hd,hcone,hlow,_⟩ := hbranch ε (τ*σ) (θ+d.b) hε hepsr hδ hδr (hu.trans hρr)
    have hactual := occupancyInverseV_branch_hasDerivAt d B (υ:=υ) (hu.trans hρw) hd
    have heq : deriv f θ=sourceInverseSlopeDerivative d ε (τ*σ) (θ+d.b) := by
      convert hactual.deriv using 1
      dsimp [f]
      congr 1
      ring
    rw [heq]
    exact ⟨hcone,by simpa [hu] using hlow⟩
  · have hθc : θ∈Icc (-d.b+ρ/2) B.delta := by
      have hneg : -(θ+d.b)<ρ := by dsimp [δB] at hθ; linarith [hθ.1]
      have hpos : ρ≤θ+d.b := by
        by_contra hn
        have habs : |θ+d.b|<ρ := abs_lt.mpr ⟨by linarith,lt_of_not_ge hn⟩
        exact hu habs
      exact ⟨by linarith,hθ.2⟩
    obtain ⟨hcone,hlow,_⟩ := hcompact ε τ σ υ θ
      (by simpa [abs_of_pos hε] using hepsq) (by simpa [abs_of_nonneg hτ] using htauq) hθc hσ hυ
    have heq := (hder θ hθ).deriv
    change deriv f θ = _ at heq
    rw [heq]
    exact ⟨by nlinarith [norm_nonneg (compactInverseSlopeDerivative d B.m B.p (deriv B.m) (deriv B.p) ε τ σ υ θ)],
      by simpa [hu] using hlow⟩

end
end IsingBulk.HT22.Geometry
