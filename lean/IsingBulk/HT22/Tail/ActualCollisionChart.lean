import IsingBulk.HT22.Tail.CollisionNeighborhood
import IsingBulk.HT22.Geometry.CovarianceShell

/-! The actual physical shell supplies the open chart required for the new
odd full-collision recursion. No old collective field or even scalar is used. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set Metric
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem actual_collision_source_chart (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ c δ ε₀ τ₀ δB : ℝ, 0<c ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) →
        ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
        ∃ Ω : Set (ℂ × (Fin N → ℝ)), IsOpen Ω ∧
          (IsingBulk.Branch.radialParameter d.alpha ε,θ)∈Ω ∧
          (∀ z∈Ω, PreferredFramePoint τ δ B.p B.m z.1 z.2) ∧
          (∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ B.p B.m z.1 z.2)≠0) ∧
          (∀ z∈Ω, ∀ a b, PreferredRightRegularPoint c z.1
            (preferredSourceCoordinate τ B.p B.m z.1 z.2 a)
            (preferredSourceCoordinate τ B.p B.m z.1 z.2 b)) := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨r₀,hr₀,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨δ,εf,τf,hδ,hδa,hεf,hτf,hframe⟩ := preferred_actual_frame_points d B
  obtain ⟨cR,εR,τR,δR,hcR,hεR,hτR,hδR,hδRB,hcov⟩ := actual_mixed_covariance_shell d B
  let ε₀ := min r₀ (min (ρ/2) (min εf εR))
  let τ₀ := min r₀ (min τf τR)
  let δB := min (B.delta/2) (min (r₀/2) δR)
  have hδB : 0<δB := lt_min (half_pos B.delta_pos) (lt_min (half_pos hr₀) hδR)
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt (by linarith [B.delta_pos])
  refine ⟨c,δ,ε₀,τ₀,δB,hc,lt_min hr₀ (lt_min (half_pos hρ) (lt_min hεf hεR)),
    lt_min hr₀ (lt_min hτf hτR),hδB,hδBB,?_⟩
  intro N hN ε τ μ r hε hεr hτ hτr hr θ hθ hwin i k hext hgap
  have hes : ε<r₀ ∧ ε<ρ/2 ∧ ε<εf ∧ ε<εR := by simpa only [ε₀,lt_min_iff] using hεr
  have hts : τ<r₀ ∧ τ<τf ∧ τ<τR := by simpa only [τ₀,lt_min_iff] using hτr
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hs : ‖s-preferredSelectedPoint d‖<ρ := by
    rw [preferred_radial_distance,abs_of_pos hε]
    linarith [hes.2.1]
  have hq (a : Fin N) : preferredSourceCoordinate τ B.p B.m s θ a∈D := by
    apply interior_subset
    have hpocc := preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ
    have hmocc := preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ a)
      (by simpa only [abs_of_pos hε] using hes.1)
      (by simpa only [abs_of_nonneg hτ] using hts.1) hpocc hmocc
      (by have hh := (hθ a).1; have hd : δB≤r₀/2 := (min_le_right _ _).trans (min_le_left _ _); linarith)
      (by have hh := (hθ a).2; linarith)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε hes.2.2.1 hτ hts.2.1 θ hθ
  have hθR (a : Fin N) : θ a∈Icc (-d.b-δR) B.delta := by
    have hd : δB≤δR := (min_le_right _ _).trans (min_le_right _ _)
    constructor <;> linarith [(hθ a).1,(hθ a).2]
  have hR := (hcov N hN ε τ μ r hε hes.2.2.2 hτ hts.2.2 hr θ hθR hwin i k hext hgap).2.2
  exact collision_source_neighborhood τ δ c B.p B.m B.smooth B.m_smooth s θ hpoint hθstrict hR
    (fun a b => hgood s _ _ hs (hq a) (hq b))

end
end IsingBulk.HT22.Tail
