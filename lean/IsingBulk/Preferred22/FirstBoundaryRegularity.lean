import IsingBulk.Preferred22.FiniteBoundaryRegularity

/-! Genuine analytic germs at all noncritical equality points of the first
prime particle order. The only possible product pole on the actual
one-sided arc is the negative equal-angle chart -alpha. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferred_first_equal_trace_nonresonant {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) (l : ℤ)
    {δ : ℝ} (hδ : 0≤δ) (hδα : δ<IsingBulk.PrimeFamily.angle p a/2)
    (hθ : IsingBulk.PrimeFamily.angle (2*p) l∈Icc (-Real.pi-δ) δ)
    (hcritical : IsingBulk.PrimeFamily.angle (2*p) l≠ -IsingBulk.PrimeFamily.angle p a)
    {z : ℂ} (ht : z+z⁻¹=2*(temperatureTrace (IsingBulk.PrimeFamily.angleRoot p a)-
      (Real.cos (IsingBulk.PrimeFamily.angle (2*p) l):ℂ))) : 1-z^(2*p)≠0 := by
  intro hz
  obtain ⟨m,hm⟩ := preferred_root_of_unity_angle (by omega : 0<2*p) (sub_eq_zero.mp hz).symm
  have ht' := IsingBulk.PrimeFamily.exp_angle_add_inv (IsingBulk.PrimeFamily.angle (2*p) m)
  change IsingBulk.PrimeFamily.angleRoot (2*p) m+(IsingBulk.PrimeFamily.angleRoot (2*p) m)⁻¹=
    2*(Real.cos (IsingBulk.PrimeFamily.angle (2*p) m):ℂ) at ht'
  rw [hm,ht'] at ht
  have hrep : IsingBulk.PrimeFamily.angleRoot p a+(IsingBulk.PrimeFamily.angleRoot p a)⁻¹=
      (Real.cos (IsingBulk.PrimeFamily.angle (2*p) l):ℂ)+
      (Real.cos (IsingBulk.PrimeFamily.angle (2*p) m):ℂ) := by
    unfold temperatureTrace at ht
    linear_combination (-1/2:ℂ)*ht
  have hc := (prime_root_unique_cosine_pair hp hp5 ha l m hrep).1
  exact hcritical (preferred_right_equal_cosine_unique ha.1 ha.2 hδ hδα hθ hc)

/-- Individual and pair one-body poles are absent at every regular real
right reference angle. This statement is independent of particle order. -/
theorem preferredBoundaryRoot_square_ne_one_reference (d : PreferredBranchData)
    {ρ δ θ : ℝ} (hρ : 0<ρ) (hδ : δ<d.b) (hθ : θ∈Icc (-d.b+ρ) δ) :
    1-preferredBoundaryRoot (preferredSelectedPoint d) (θ:ℂ)*
      preferredBoundaryRoot (preferredSelectedPoint d) (θ:ℂ)≠0 := by
  let z := preferredBoundaryRoot (preferredSelectedPoint d) (θ:ℂ)
  obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδ hθ
  have ht := preferredBoundaryRoot_trace (preferredSelectedPoint d) (θ:ℂ)
  have htrace : z+z⁻¹=2*((1+Real.cos d.b-Real.cos θ:ℝ):ℂ) := by
    rw [temperatureTrace_preferredSelectedPoint] at ht
    convert ht using 1
    push_cast
    rfl
  intro he
  have hzz : z^2=1 := by rw [pow_two]; exact (sub_eq_zero.mp he).symm
  have hh : (z-1)*(z+1)=0 := by linear_combination hzz
  rcases mul_eq_zero.mp hh with hz1 | hzm
  · have hz : z=1 := sub_eq_zero.mp hz1
    rw [hz] at htrace
    have hh := congrArg Complex.re htrace
    norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero,inv_one,Complex.one_re,Complex.neg_re,
      inv_neg,←Complex.ofReal_cos] at hh
    change (2:ℝ)=2*(1+Real.cos d.b-Real.cos θ) at hh
    linarith
  · have hz : z= -1 := eq_neg_of_add_eq_zero_left hzm
    rw [hz] at htrace
    have hh := congrArg Complex.re htrace
    norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero,inv_one,Complex.one_re,Complex.neg_re,
      inv_neg,←Complex.ofReal_cos] at hh
    change (-2:ℝ)=2*(1+Real.cos d.b-Real.cos θ) at hh
    linarith

/-- Complete source density analyticity at a regular constrained equality
center follows from its actual product nonvanishing. -/
theorem preferred_equal_density_analytic_of_nonresonant (d : PreferredBranchData)
    {N : ℕ} {ρ δ θ : ℝ} (hρ : 0<ρ) (hδ : δ<d.b) (hθ : θ∈Icc (-d.b+ρ) δ)
    (hprod : 1-(preferredBoundaryRoot (preferredSelectedPoint d) (θ:ℂ))^N≠0) :
    AnalyticAt ℂ (@preferredBoundaryAngularDensity N)
      (preferredSelectedPoint d,fun _ => (θ:ℂ)) := by
  apply preferredBoundaryAngularDensity_analyticAt
  · intro i
    exact preferredBoundaryRoot_analyticAt_reference d hρ hδ hθ
  · intro i j
    exact preferredBoundaryRoot_square_ne_one_reference d hρ hδ hθ
  · simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hprod

/-- At N=2p every equality chart except the actual critical center -alpha
has a genuine jointly analytic continuation of the entire physical density. -/
theorem preferred_first_noncritical_equal_density_analytic (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (l : ℤ) {ρ δ : ℝ}
    (hρ : 0<ρ) (hδ0 : 0≤δ) (hδb : δ<d.b) (hδα : δ<d.alpha/2)
    (hθ : IsingBulk.PrimeFamily.angle (2*p) l∈Icc (-d.b+ρ) δ)
    (hcritical : IsingBulk.PrimeFamily.angle (2*p) l≠ -d.alpha) :
    AnalyticAt ℂ (@preferredBoundaryAngularDensity (2*p))
      (preferredSelectedPoint d,fun _ => (IsingBulk.PrimeFamily.angle (2*p) l:ℂ)) := by
  apply preferred_equal_density_analytic_of_nonresonant d hρ hδb hθ
  have hζ : preferredSelectedPoint d=IsingBulk.PrimeFamily.angleRoot p a := by
    simp [preferredSelectedPoint,IsingBulk.Branch.radialParameter,hα,IsingBulk.PrimeFamily.angleRoot]
  apply preferred_first_equal_trace_nonresonant hp hp5 ha l hδ0
    (by simpa only [←hα] using hδα)
    (show IsingBulk.PrimeFamily.angle (2*p) l∈Icc (-Real.pi-δ) δ from
      ⟨by linarith [hθ.1,d.b_lt],hθ.2⟩)
    (by simpa only [←hα] using hcritical)
  simpa only [←hζ,←Complex.ofReal_cos] using
    preferredBoundaryRoot_trace (preferredSelectedPoint d) (IsingBulk.PrimeFamily.angle (2*p) l:ℂ)

/-- One fixed genuine neighborhood controls every mixed jet at each
noncritical first-order equality point; the radius precedes j. -/
theorem preferred_first_noncritical_equal_density_uniform_jets (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (l : ℤ) {ρ δ : ℝ}
    (hρ : 0<ρ) (hδ0 : 0≤δ) (hδb : δ<d.b) (hδα : δ<d.alpha/2)
    (hθ : IsingBulk.PrimeFamily.angle (2*p) l∈Icc (-d.b+ρ) δ)
    (hcritical : IsingBulk.PrimeFamily.angle (2*p) l≠ -d.alpha) :
    ∃r : ℝ,0<r ∧ ∀j : ℕ,∃C : ℝ,0<C ∧
      ∀x∈Metric.closedBall (preferredSelectedPoint d,
        fun _ : Fin (2*p) => (IsingBulk.PrimeFamily.angle (2*p) l:ℂ)) r,
      ‖iteratedFDeriv ℂ j (@preferredBoundaryAngularDensity (2*p)) x‖≤C := by
  have hg := preferred_first_noncritical_equal_density_analytic d hp hp5 ha hα l hρ hδ0 hδb hδα hθ hcritical
  obtain ⟨r,hr,hball⟩ := hg.exists_ball_analyticOnNhd
  refine ⟨r/2,half_pos hr,?_⟩
  intro j
  let K := Metric.closedBall (preferredSelectedPoint d,
    fun _ : Fin (2*p) => (IsingBulk.PrimeFamily.angle (2*p) l:ℂ)) (r/2)
  have hsub : K⊆Metric.ball (preferredSelectedPoint d,
      fun _ : Fin (2*p) => (IsingBulk.PrimeFamily.angle (2*p) l:ℂ)) r :=
    Metric.closedBall_subset_ball (by linarith)
  have hc : ContinuousOn (iteratedFDeriv ℂ j (@preferredBoundaryAngularDensity (2*p))) K :=
    ((hball.mono hsub).iteratedFDeriv j).continuousOn
  obtain ⟨C,hC⟩ := (isCompact_closedBall _ (r/2)).exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro x hx
  exact (hC x hx).trans (by have := le_max_left C 0; linarith)

end
end IsingBulk.Preferred22
