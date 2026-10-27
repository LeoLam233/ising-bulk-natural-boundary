import IsingBulk.Preferred22.PhysicalDensityDomain
import IsingBulk.Preferred22.ContourInverseBounds
import IsingBulk.Preferred22.BalancedPairGeometry
import IsingBulk.Preferred22.CoordinateDiameter

/-! Actual whole-right physical regularity and shell integrability at every
transport order. Constants precede particle count and derivative order. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- The concrete open physical regularity set contains every actual right
configuration of positive diameter, uniformly before N and transport order. -/
theorem preferred_actual_regularDomain (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δB τ₀ ε₀ : ℝ,0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ N : ℕ,2≤N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,θ∈preferredRightAngularBox d B.delta δB N →
      0<preferredAngularDiameter θ →
      (IsingBulk.Branch.radialParameter d.alpha ε,θ)∈preferredPhysicalRegularDomain τ B.p B.m := by
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
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam
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
  have hq (i : Fin N) : preferredSourceCoordinate τ B.p B.m s θ i∈D := by
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hεr')
      (by simpa only [abs_of_nonneg hτ] using hτr')
      (preferred_occupancy_mean_mem hN0 B.p hpunit θ)
      (preferred_occupancy_mean_mem hN0 B.m hmunit θ)
      (by have hv := (hθ i).1; have hδ : δB≤r := (min_le_left _ _).trans (by linarith); linarith)
      ((hθ i).2.trans hBcap.le)
    rw [preferredBumpCoordinate_actual] at hh
    exact interior_subset hh
  have hU (q : ℂ) (hq : q∈D) : AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q) :=
    (hgood s q q hsd hq hq).2.1
  have hcurv (q : ℂ) (hq : q∈D) : c≤(deriv (preferredSourceUQ s) q).re := by
    have hh := hgood s q q hsd hq hq
    change c≤(deriv (deriv (preferredMovingInverse s)) q).re
    rw [← preferredMovingCurvature_eq_deriv s q hh.2.1]
    exact hh.2.2.2.1.le
  have hR := (hRgeom τ hτ hτR' N hN0 θ s B.delta B.delta_pos
    (hBcap.trans (hcapa.trans d.alpha_lt)) hSr hSi hSδ hθ' B.lower_bound
    (fun x => B.lower_bound (-x)) (fun x hx => B.p_zero_of_sin_nonpos hx)
    (fun x hx => B.m_zero_of_sin_nonneg hx)).2.2 hdiam
  have hM : (preferredContourMatrix τ B.p B.m θ).det≠0 :=
    (preferred_matrix_inverse_of_row_three_quarters _
      (fun i => (hMrow τ hτ hτM' N hN0 θ i).trans (by norm_num))).1
  exact preferredPhysicalRegularDomain_of_curvature τ B.p B.m s θ hSi hW D c hc hDv hU hcurv hq hR hM

/-- Every actual physical transported density is genuinely integrable on
all positive-diameter right shells. No pointwise density majorant is used. -/
theorem preferred_actual_all_order_shell_integrable (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δB τ₀ ε₀ : ℝ,0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ n : ℕ,2≤n+1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ η rcut : ℝ → ℝ,ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut →
      ∀ j : ℕ,∀ r : ℝ,0<r → ∀ l : ℤ,∀ i a : Fin (n+1),
      IntegrableOn (fun x : Fin n → ℝ => preferredTransportedDensity .right τ η B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x)))
        (preferredRightShell d B δB r l i a) := by
  obtain ⟨cap,hcap,hcapa,hreg⟩ := preferred_actual_regularDomain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,hmem⟩ := hreg B hBcap
  refine ⟨δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,?_⟩
  intro n hN ε τ hε hεr hτ hτr η rcut hη hrcut j r hr l i a
  rw [preferredRightShell_eq_linear d B hδBδ]
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let F := constrainedAtTotal (n := n) (2*Real.pi*(l:ℝ))
  have hF : Continuous F := by unfold F constrainedAtTotal; fun_prop
  have hc : ContinuousOn (fun x : Fin n → ℝ => preferredTransportedDensity .right τ η B.p B.m rcut j s (F x))
      (preferredLinearRightShell d B δB r l i a) := by
    intro x hx
    have hbox : F x∈preferredRightAngularBox d B.delta δB (n+1) := hx.1
    have hdiam : 0<preferredAngularDiameter (F x) := by
      have hh := preferredAngularDiameter_pair_le (F x) a i
      have hpos : 0<F x a-F x i := hr.trans_le hx.2.2.1
      rw [abs_of_pos hpos] at hh
      exact hpos.trans_le hh
    have hz := hmem (n+1) hN ε τ hε hεr hτ hτr (F x) hbox hdiam
    have hs := (preferredTransportedDensity_mixed_regularDomain (by omega) τ η B.p B.m rcut
      hη B.smooth B.m_smooth hrcut j (s,F x) hz).1.continuousAt
    exact (ContinuousAt.comp (f := fun x : Fin n → ℝ => (s,F x))
      (g := fun z : ℂ × (Fin (n+1) → ℝ) => preferredTransportedDensity .right τ η B.p B.m rcut j z.1 z.2)
      hs (continuousAt_const.prodMk hF.continuousAt)).continuousWithinAt
  have hi := hc.integrableOn_compact (μ := volume) (preferredLinearRightShell_isCompact d B δB r l i a)
  apply hi.congr_fun _ (preferredLinearRightShell_isClosed d B δB r l i a).measurableSet
  intro x hx
  dsimp only
  rw [(preferred_lift_eq_affine_from_right d B hδBδ l x hx.1).2]

end
end IsingBulk.Preferred22
