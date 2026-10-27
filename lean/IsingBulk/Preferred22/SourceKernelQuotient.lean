import IsingBulk.Preferred22.RegularKernelQuotient

/-! Actual source-frame jets of the analytic kernel divided difference.
The common contour geometry precedes every order and particle count. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric Filter
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_kernel_quotient_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        ∀ xs : List (Option (Fin N)), xs.length≤j → ∀ i k,
        ‖preferredFrameJet τ B.p B.m
          (fun t x => preferredKernelQuotient t
            (preferredSourceCoordinate τ B.p B.m t x i)
            (preferredSourceCoordinate τ B.p B.m t x k)) xs
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨r,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨δ,εf,τf,hδ,hδa,hεf,hτf,hframe⟩ := preferred_actual_frame_points d B
  let ε₀ := min r (min (ρ/2) εf)
  let τ₀ := min r τf
  let δB := min (B.delta/2) (r/2)
  have hδB : 0<δB := lt_min (half_pos B.delta_pos) (half_pos hr)
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt (by linarith [B.delta_pos])
  refine ⟨ε₀,τ₀,δB,lt_min hr (lt_min (half_pos hρ) hεf),lt_min hr hτf,hδB,hδBB,?_⟩
  choose C hC hCQ using preferred_kernel_quotient_domain_all_jets d ρ c D hρ hDc hgood
  intro j
  let Cj := 1+∑ k∈Finset.range (j+1), C k
  have hsum : 0≤∑ k∈Finset.range (j+1), C k := Finset.sum_nonneg (fun k _ => (hC k).le)
  have hCj : 0<Cj := by dsimp [Cj]; linarith
  refine ⟨Cj,hCj,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ xs hxs
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hepsr : ε<r := hεr.trans_le (min_le_left _ _)
  have hepsρ : ε<ρ/2 := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsf : ε<εf := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ht : τ<r := hτr.trans_le (min_le_left _ _)
  have htf : τ<τf := hτr.trans_le (min_le_right _ _)
  have hs : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hepsρ.le
  have hq (i : Fin N) : preferredSourceCoordinate τ B.p B.m s θ i∈D := by
    apply interior_subset
    have hpocc := preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ
    have hmocc := preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hepsr)
      (by simpa only [abs_of_nonneg hτ] using ht) hpocc hmocc
      (by have hh := (hθ i).1; have hd : δB≤r/2 := min_le_right _ _; linarith)
      (by have hh := (hθ i).2; linarith)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε hepsf hτ htf θ hθ
  have hCk : C xs.length≤Cj := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (j+1)) => (hC k).le)
      (show xs.length∈Finset.range (j+1) by simp; omega)
    dsimp only [Cj]
    linarith
  intro i k
  have hsρ : ‖s-preferredSelectedPoint d‖<ρ := by linarith
  have hqr := hgood s _ _ hsρ (hq i) (hq k)
  have hrr := hgood s _ _ hsρ (hq k) (hq k)
  have hQa := preferredKernelQuotient_analyticAt s
    (preferredSourceCoordinate τ B.p B.m s θ i) (preferredSourceCoordinate τ B.p B.m s θ k)
    (preferredKernelExtension_analyticAt _ _ _ hqr.2.1 hqr.2.2.1 hqr.1 hqr.2.2.2.2.2.2.2.2.2)
    (preferredKernelExtension_analyticAt _ _ _ hrr.2.1 hrr.2.2.1 hrr.1 hrr.2.2.2.2.2.2.2.2.2)
  exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth
    s θ hpoint hθstrict
    (fun z : ℂ × ℂ × ℂ => preferredKernelQuotient z.1 z.2.1 z.2.2)
    (fun z : ℂ × ℂ × ℂ => preferredKernelQuotient z.1 z.2.1 z.2.2)
    (preferredPairProjection i k) (preferredPairProjection_norm_le i k) hQa
    Filter.EventuallyEq.rfl xs Cj hCj.le
    ((hCQ xs.length s _ _ hs (hq i) (hq k)).trans hCk)

end
end IsingBulk.Preferred22
