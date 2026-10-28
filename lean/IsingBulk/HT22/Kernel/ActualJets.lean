import IsingBulk.HT22.Kernel.SourceBound

/-! All fixed-order jets of the true ordinary odd kernel, with the actual
fixed-v source frame and particle-independent constants. -/
namespace IsingBulk.HT22.Kernel
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem actual_ordinary_kernel_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        ∀ xs : List (Option (Fin N)), xs.length≤j →
        ∀ i k, ‖frameJet τ B.p B.m
          (fun t x => sourceOrdinaryKernel τ B.p B.m t x i k) xs
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
  choose C hC hCK using ordinaryExtension_fixed_domain_jets d ρ c D hρ hDc (interior_subset hzero) hgood
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
  exact ordinary_frame_jets_on_domain d ρ c D hρ hgood τ δ B.p B.m B.smooth B.m_smooth
    s θ hpoint hθstrict hs hq xs Cj hCj.le
    (fun q hq r hr => (hCK xs.length s q r hs hq hr).2.trans hCk)


end
end IsingBulk.HT22.Kernel
