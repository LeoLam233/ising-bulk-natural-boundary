import IsingBulk.Preferred22.WeightedTransportFactorization
import IsingBulk.Preferred22.WeightedTransportRegularity

/-! The actual whole-right physical/regular weighted factorization, with
mixed smoothness and every source geometry hypothesis discharged. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferredWeightedPhysicalDensity_factorization {N : ℕ} (hN : 0<N)
    (ψ : (Fin N → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hreg : ∀ z∈Ω, PreferredSourceRegime τ δ p m z)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈Ω, ∀ q∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (z.1,q))
    (hcurv : ∀ z∈Ω, ∀ q∈D, c≤(deriv (preferredSourceUQ z.1) q).re)
    (hq : ∀ z∈Ω, ∀ i, preferredSourceCoordinate τ p m z.1 z.2 i∈D)
    (hR : ∀ z∈Ω, collectiveDenominator (fun i => preferredMovingInverse z.1
      (preferredSourceCoordinate τ p m z.1 z.2 i))≠0)
    (hM : ∀ z∈Ω, (preferredContourMatrix τ p m z.2).det≠0) :
    ∀ j, ∀ z∈Ω, preferredWeightedPhysicalDensity ψ τ η p m r j z.1 z.2=
      preferredCoordinateJacobian τ p m z.1 z.2*preferredSourceResolvent τ p m z.1 z.2*
        preferredWeightedRegularScalar ψ τ η p m r j z.1 z.2 := by
  apply preferredWeightedPhysicalDensity_factorization_of_mixed hN ψ τ δ η p m r hp hm hδ hδπ
    Ω hΩ hreg D c hc hD hU hcurv hq hR hM
  intro j z hz
  obtain ⟨_,hSi,_,_,hW⟩ := hreg z hz
  exact preferredWeightedPhysicalDensity_mixed_regularDomain hN ψ hψ τ η p m r hη hp hm hr j z
    (preferredPhysicalRegularDomain_of_curvature τ p m z.1 z.2 hSi hW D c hc hD
      (hU z hz) (hcurv z hz) (hq z hz) (hR z hz) (hM z hz))


theorem preferredWeightedPhysicalDensity_factorization_at {N : ℕ} (hN : 0<N)
    (ψ : (Fin N → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (s₀ : ℂ) (ρ : ℝ) (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ s, ‖s-s₀‖<ρ → ∀ q∈D,
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q))
    (hcurv : ∀ s, ‖s-s₀‖<ρ → ∀ q∈D, c≤(deriv (preferredSourceUQ s) q).re)
    (s : ℂ) (θ : Fin N → ℝ) (hs : ‖s-s₀‖<ρ)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈interior D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s
      (preferredSourceCoordinate τ p m s θ i))≠0)
    (hM : (preferredContourMatrix τ p m θ).det≠0) (j : ℕ) :
    preferredWeightedPhysicalDensity ψ τ η p m r j s θ=
      preferredCoordinateJacobian τ p m s θ*preferredSourceResolvent τ p m s θ*
        preferredWeightedRegularScalar ψ τ η p m r j s θ := by
  obtain ⟨δ',hδ',hδπ',hreg⟩ := preferred_source_regime_enlarge τ δ p m s θ hδ hδπ hS hSi hSδ hθ hW
  let Ω := preferredTransportDomain (N := N) τ δ' p m s₀ ρ D
  have hΩ : IsOpen Ω := preferredTransportDomain_isOpen τ δ' p m hp hm s₀ ρ D hU
  have hz : (s,θ)∈Ω := ⟨hreg,hs,hq,hR,hM⟩
  exact preferredWeightedPhysicalDensity_factorization hN ψ hψ τ δ' η p m r hη hp hm hr hδ' hδπ'
    Ω hΩ (fun _ hz => hz.1) D c hc hD
    (fun z hz => hU z.1 hz.2.1) (fun z hz => hcurv z.1 hz.2.1)
    (fun _ hz i => interior_subset (hz.2.2.1 i)) (fun _ hz => hz.2.2.2.1)
    (fun _ hz => hz.2.2.2.2) j (s,θ) hz


/-- The actual all-order physical/regular factorization on the complete
right contour. The bump cap and positive geometric radii precede every
particle count and derivative order, and every analytic, R and M premise is
discharged from the source constructions. -/
theorem preferred_actual_weighted_factorization (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δB τ₀ ε₀ : ℝ,0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ N : ℕ,2≤N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,θ∈preferredRightAngularBox d B.delta δB N →
      0<preferredAngularDiameter θ →
      ∀ ψ : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ ψ →
      ∀ η rcut : ℝ → ℝ,ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut → ∀ j : ℕ,
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      preferredWeightedPhysicalDensity ψ τ η B.p B.m rcut j s θ=
        preferredCoordinateJacobian τ B.p B.m s θ*preferredSourceResolvent τ B.p B.m s θ*
          preferredWeightedRegularScalar ψ τ η B.p B.m rcut j s θ := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,_hDc,hDv,_hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨r,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨εs,hεs,hmargin⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos (hBcap.trans hcapa)
  obtain ⟨τR,hτR,hRgeom⟩ := balanced_source_collective_geometry B.p B.m B.smooth B.m_smooth
    B.periodic (PreferredCoareaBump.m_periodic B)
  obtain ⟨τM,hτM,hMrow⟩ := preferredContourMatrix_uniform_half_row B.p B.m B.smooth B.m_smooth
    B.periodic (PreferredCoareaBump.m_periodic B)
    (fun x => by rw [abs_of_nonneg (B.lower_bound x)]; exact B.upper_bound x)
    (fun x => by change |B.p (-x)|≤1; rw [abs_of_nonneg (B.lower_bound (-x))]; exact B.upper_bound (-x))
  let δB := min (r/2) (B.delta/2)
  let τ₀ := min r (min τR τM)
  let ε₀ := min r (min ρ εs)
  have hδB : 0<δB := lt_min (half_pos hr) (half_pos B.delta_pos)
  have hδBδ : δB<B.delta := (min_le_right _ _).trans_lt (half_lt_self B.delta_pos)
  have hτ₀ : 0<τ₀ := lt_min hr (lt_min hτR hτM)
  have hε₀ : 0<ε₀ := lt_min hr (lt_min hρ hεs)
  refine ⟨δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam ψ hψ η rcut hη hrcut j
  have hN0 : 0<N := by omega
  have hεr' : ε<r := hεr.trans_le (min_le_left _ _)
  have hερ : ε<ρ := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεs' : ε<εs := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτr' : τ<r := hτr.trans_le (min_le_left _ _)
  have hτR' : τ≤τR := (hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hτM' : τ≤τM := (hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  obtain ⟨hSr,hSi,hSδ⟩ := hmargin ε hε hεs'
  have hθ' (i : Fin N) : θ i∈Icc (-Real.pi-B.delta) B.delta := by
    have hh := hθ i
    exact ⟨by linarith [hh.1,d.b_lt,hδBδ],hh.2⟩
  have hpunit (x : ℝ) : B.p x∈Icc 0 1 := ⟨B.lower_bound x,B.upper_bound x⟩
  have hmunit (x : ℝ) : B.m x∈Icc 0 1 := ⟨B.lower_bound (-x),B.upper_bound (-x)⟩
  have hW (i : Fin N) : 0<(temperatureTrace s-Complex.cos (deformedAngles τ B.p B.m θ i)).im := by
    have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) B.p B.m θ
      B.lower_bound (fun x => B.lower_bound (-x))
      (fun x hx => B.p_zero_of_sin_nonpos hx) (fun x hx => B.m_zero_of_sin_nonneg hx) i
    simpa only [complexW_homotopyRoot_eq] using hh
  have hsd : ‖s-preferredSelectedPoint d‖<ρ := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hερ
  have hq (i : Fin N) : preferredSourceCoordinate τ B.p B.m s θ i∈interior D := by
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hεr')
      (by simpa only [abs_of_nonneg hτ] using hτr')
      (preferred_occupancy_mean_mem hN0 B.p hpunit θ)
      (preferred_occupancy_mean_mem hN0 B.m hmunit θ)
      (by have hv := (hθ i).1; have hδ : δB≤r := (min_le_left _ _).trans (by linarith); linarith)
      ((hθ i).2.trans hBcap.le)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  have hU (t : ℂ) (ht : ‖t-preferredSelectedPoint d‖<ρ) (q : ℂ) (hq : q∈D) :
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (t,q) :=
    (hgood t q q ht hq hq).2.1
  have hcurv (t : ℂ) (ht : ‖t-preferredSelectedPoint d‖<ρ) (q : ℂ) (hq : q∈D) :
      c≤(deriv (preferredSourceUQ t) q).re := by
    have hh := hgood t q q ht hq hq
    change c≤(deriv (deriv (preferredMovingInverse t)) q).re
    rw [← preferredMovingCurvature_eq_deriv t q hh.2.1]
    exact hh.2.2.2.1.le
  have hR := (hRgeom τ hτ hτR' N hN0 θ s B.delta B.delta_pos
    (hBcap.trans (hcapa.trans d.alpha_lt)) hSr hSi hSδ hθ' B.lower_bound
    (fun x => B.lower_bound (-x)) (fun x hx => B.p_zero_of_sin_nonpos hx)
    (fun x hx => B.m_zero_of_sin_nonneg hx)).2.2 hdiam
  have hM : (preferredContourMatrix τ B.p B.m θ).det≠0 :=
    (preferred_matrix_inverse_of_row_three_quarters _
      (fun i => (hMrow τ hτ hτM' N hN0 θ i).trans (by norm_num))).1
  exact preferredWeightedPhysicalDensity_factorization_at hN0 ψ hψ τ B.delta η B.p B.m rcut
    hη B.smooth B.m_smooth hrcut B.delta_pos (hBcap.trans (hcapa.trans d.alpha_lt))
    (preferredSelectedPoint d) ρ D c hc hDv hU hcurv s θ hsd hSr hSi hSδ hθ' hW hq hR hM j


end
end IsingBulk.Preferred22
