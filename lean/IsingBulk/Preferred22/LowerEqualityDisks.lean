import IsingBulk.Preferred22.FiniteBoundaryRegularity
import IsingBulk.Preferred22.FiniteEqualityGeometry
import IsingBulk.Preferred22.AnchorKernel

/-! A common analytic disk and density bound for every constrained lower
equality center in the physical regular arc. The finite integer mean set
is obtained from the actual angular interval; no center is omitted. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem preferred_equal_angle_integer_bound (d : PreferredBranchData)
    {N : ℕ} (hN : 0<N) (l : ℤ) {g δ : ℝ} (hg : 0<g) (hδ : δ<d.b)
    (hθ : IsingBulk.PrimeFamily.angle N l∈Icc (-d.b+g) δ) :
    l∈Finset.Icc (-(N:ℤ)) (N:ℤ) := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have ht : (N:ℝ)*IsingBulk.PrimeFamily.angle N l=2*Real.pi*(l:ℝ) := by
    unfold IsingBulk.PrimeFamily.angle
    field_simp
  have hlo : -Real.pi<IsingBulk.PrimeFamily.angle N l := by linarith [d.b_lt,hθ.1]
  have hup : IsingBulk.PrimeFamily.angle N l<Real.pi := by linarith [d.b_lt,hθ.2]
  have h1 := mul_lt_mul_of_pos_left hlo hNr
  have h2 := mul_lt_mul_of_pos_left hup hNr
  rw [ht] at h1 h2
  have hl : -(N:ℝ)≤(l:ℝ) := by nlinarith [mul_pos hNr Real.pi_pos]
  have hu : (l:ℝ)≤(N:ℝ) := by nlinarith [mul_pos hNr Real.pi_pos]
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem preferred_lower_equal_density_uniform_disks (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) {N : ℕ} (hN : 0<N)
    (hEven : Even N) (hNp : N<2*p) {g δ : ℝ} (hg : 0<g) (hδ : δ<d.b) :
    ∃ r M : ℝ,0<r ∧ 1≤M ∧ ∀ l : ℤ,
      IsingBulk.PrimeFamily.angle N l∈Icc (-d.b+g) δ →
      AnalyticOnNhd ℂ (@preferredBoundaryAngularDensity N)
        (closedBall (preferredSelectedPoint d,fun _ : Fin N => (IsingBulk.PrimeFamily.angle N l:ℂ)) r) ∧
      ∀ x∈closedBall (preferredSelectedPoint d,fun _ : Fin N => (IsingBulk.PrimeFamily.angle N l:ℂ)) r,
        ‖preferredBoundaryAngularDensity x‖≤M := by
  classical
  let L := (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter
    (fun l => IsingBulk.PrimeFamily.angle N l∈Icc (-d.b+g) δ)
  let c := fun l : ℤ => (preferredSelectedPoint d,fun _ : Fin N => (IsingBulk.PrimeFamily.angle N l:ℂ))
  let K := c '' (L : Set ℤ)
  have hK : IsCompact K := (L.finite_toSet.image c).isCompact
  have hF : AnalyticOnNhd ℂ (@preferredBoundaryAngularDensity N) K := by
    rintro x ⟨l,hl,rfl⟩
    have hli := (Finset.mem_filter.mp hl).2
    exact preferred_lower_equal_density_analytic d hp hp5 ha hα hN hEven hNp l hg hδ hli
  obtain ⟨r,M,hr,hM,hh⟩ := preferred_compact_analytic_balls
    (@preferredBoundaryAngularDensity N) K hK hF
  refine ⟨r,M,hr,hM,?_⟩
  intro l hl
  apply hh (c l)
  exact ⟨l,Finset.mem_filter.mpr ⟨preferred_equal_angle_integer_bound d hN l hg hδ hl,hl⟩,rfl⟩

/-- The actual contour displacement from its real angle costs at most tau.
This holds for the coupled occupancies computed at the same configuration. -/
theorem preferred_deformedAngle_distance_real {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (θ : Fin N → ℝ) (i : Fin N) :
    ‖deformedAngles τ B.p B.m θ i-(θ i:ℂ)‖≤τ := by
  have him := preferred_deformedAngles_im_bound hN d B hτ θ i
  have he : deformedAngles τ B.p B.m θ i-(θ i:ℂ)=
      ((deformedAngles τ B.p B.m θ i).im:ℂ)*Complex.I := by
    simp only [deformedAngles]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact him

theorem preferred_deformedAngles_distance_equal {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (θ : Fin N → ℝ) (t : ℝ) {R : ℝ} (hR : 0≤R)
    (hθ : ∀i,|θ i-t|≤R) :
    ‖deformedAngles τ B.p B.m θ-(fun _ => (t:ℂ))‖≤R+τ := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg hR hτ)).mpr
  intro i
  calc
    _ = ‖(deformedAngles τ B.p B.m θ i-(θ i:ℂ))+((θ i:ℂ)-(t:ℂ))‖ := by
      congr 1
      simp only [Pi.sub_apply,sub_add_sub_cancel]
    _ ≤ ‖deformedAngles τ B.p B.m θ i-(θ i:ℂ)‖+‖(θ i:ℂ)-(t:ℂ)‖ := norm_add_le _ _
    _ ≤ τ+R := add_le_add (preferred_deformedAngle_distance_real hN d B hτ θ i)
      (by simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hθ i)
    _ = R+τ := add_comm _ _

end
end IsingBulk.Preferred22
