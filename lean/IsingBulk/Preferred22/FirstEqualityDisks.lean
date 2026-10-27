import IsingBulk.Preferred22.FirstBoundaryRegularity
import IsingBulk.Preferred22.LowerEqualityDisks

/-! One common genuine analytic disk for every noncritical constrained
equality mean at the first prime order. The finite set is extracted from
the actual right interval; the unique critical mean is removed explicitly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

theorem preferred_first_noncritical_density_uniform_disks (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) {g δ : ℝ}
    (hg : 0<g) (hδ0 : 0≤δ) (hδb : δ<d.b) (hδα : δ<d.alpha/2) :
    ∃ r M : ℝ,0<r ∧ 1≤M ∧ ∀ l : ℤ,
      IsingBulk.PrimeFamily.angle (2*p) l∈Icc (-d.b+g) δ →
      IsingBulk.PrimeFamily.angle (2*p) l≠ -d.alpha →
      AnalyticOnNhd ℂ (@preferredBoundaryAngularDensity (2*p))
        (closedBall (preferredSelectedPoint d,fun _ : Fin (2*p) => (IsingBulk.PrimeFamily.angle (2*p) l:ℂ)) r) ∧
      ∀ x∈closedBall (preferredSelectedPoint d,fun _ : Fin (2*p) => (IsingBulk.PrimeFamily.angle (2*p) l:ℂ)) r,
        ‖preferredBoundaryAngularDensity x‖≤M := by
  classical
  let L := (Finset.Icc (-(2*p:ℤ)) (2*p:ℤ)).filter
    (fun l => IsingBulk.PrimeFamily.angle (2*p) l∈Icc (-d.b+g) δ ∧
      IsingBulk.PrimeFamily.angle (2*p) l≠ -d.alpha)
  let c := fun l : ℤ => (preferredSelectedPoint d,fun _ : Fin (2*p) => (IsingBulk.PrimeFamily.angle (2*p) l:ℂ))
  let K := c '' (L : Set ℤ)
  have hK : IsCompact K := (L.finite_toSet.image c).isCompact
  have hF : AnalyticOnNhd ℂ (@preferredBoundaryAngularDensity (2*p)) K := by
    rintro x ⟨l,hl,rfl⟩
    obtain ⟨hθ,hcritical⟩ := (Finset.mem_filter.mp hl).2
    exact preferred_first_noncritical_equal_density_analytic d hp hp5 ha hα l hg hδ0 hδb hδα hθ hcritical
  obtain ⟨r,M,hr,hM,hh⟩ := preferred_compact_analytic_balls
    (@preferredBoundaryAngularDensity (2*p)) K hK hF
  refine ⟨r,M,hr,hM,?_⟩
  intro l hl hcritical
  apply hh (c l)
  have hli := preferred_equal_angle_integer_bound d (by omega : 0<2*p) l hg hδb hl
  refine ⟨l,Finset.mem_filter.mpr ⟨?_,hl,hcritical⟩,rfl⟩
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hli

end
end IsingBulk.Preferred22
