import IsingBulk.Preferred22.FiniteEquality
import IsingBulk.Preferred22.FiniteMeanSeparation
import IsingBulk.Preferred22.FiniteComplementMass
import IsingBulk.Preferred22.PhysicalDensityRegularity

/-! The finite equality charts have actual analytic boundary germs whenever
prime-root arithmetic excludes their product pole. This includes N=2.
The new germs equal the original physical sheet on the upper dispersion domain. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Root-independent arithmetic is needed for an analytic germ crossing the
unit circle, since its continued root need not remain the globally selected one. -/
theorem preferred_equal_trace_nickel {N : ℕ} (hN : 0<N) {ζ z : ℂ}
    (hζ : ‖ζ‖=1) (l : ℤ)
    (ht : z+z⁻¹=2*(temperatureTrace ζ-(Real.cos (IsingBulk.PrimeFamily.angle N l):ℂ)))
    (hz : z^N=1) : IsingBulk.PrimeFamily.NickelAt ζ N := by
  obtain ⟨m,hm⟩ := preferred_root_of_unity_angle hN hz
  have ha := IsingBulk.PrimeFamily.exp_angle_add_inv (IsingBulk.PrimeFamily.angle N m)
  change IsingBulk.PrimeFamily.angleRoot N m+(IsingBulk.PrimeFamily.angleRoot N m)⁻¹=
    2*(Real.cos (IsingBulk.PrimeFamily.angle N m):ℂ) at ha
  rw [hm,ha] at ht
  refine ⟨hζ,l,m,?_⟩
  unfold temperatureTrace at ht
  linear_combination (-1/2:ℂ)*ht

theorem preferred_lower_equal_trace_nonresonant {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) {N : ℕ} (hN : 0<N)
    (hEven : Even N) (hNp : N<2*p) (l : ℤ) {z : ℂ}
    (ht : z+z⁻¹=2*(temperatureTrace (IsingBulk.PrimeFamily.angleRoot p a)-
      (Real.cos (IsingBulk.PrimeFamily.angle N l):ℂ))) : 1-z^N≠0 := by
  intro hz
  have hz' : z^N=1 := (sub_eq_zero.mp hz).symm
  exact (prime_root_first_even hp hp5 ha).2 N hN hEven hNp
    (preferred_equal_trace_nickel hN (Complex.norm_exp_ofReal_mul_I _) l ht hz')

/-- The analytic root that continues the actual upper-half dispersion sheet. -/
def preferredBoundaryRoot (s w : ℂ) : ℂ :=
  Complex.exp (-Complex.I*preferredArccos (temperatureTrace s-Complex.cos w))

theorem preferredBoundaryRoot_trace (s w : ℂ) :
    preferredBoundaryRoot s w+(preferredBoundaryRoot s w)⁻¹=
      2*(temperatureTrace s-Complex.cos w) := by
  unfold preferredBoundaryRoot
  rw [preferred_exp_phase_inverse,inv_inv]
  simpa only [add_comm] using preferredCosineRoot_trace (temperatureTrace s-Complex.cos w)

theorem preferredBoundaryRoot_ne_zero (s w : ℂ) : preferredBoundaryRoot s w≠0 := Complex.exp_ne_zero _

theorem preferredBoundaryRoot_eq_physical {s w : ℂ}
    (hW : 0<(temperatureTrace s-Complex.cos w).im) :
    preferredBoundaryRoot s w=physicalRoot (temperatureTrace s-Complex.cos w) :=
  preferredArccos_physical_upper _ hW

/-- Every real reference angle strictly inside the true branch interval has
a joint analytic germ in the physical parameter and complex angular variable. -/
theorem preferredBoundaryRoot_analyticAt_reference (d : PreferredBranchData)
    {ρ δ θ : ℝ} (hρ : 0<ρ) (hδ : δ<d.b) (hθ : θ∈Icc (-d.b+ρ) δ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredBoundaryRoot z.1 z.2)
      (preferredSelectedPoint d,(θ:ℂ)) := by
  obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδ hθ
  have ha : AnalyticAt ℂ (fun z : ℂ × ℂ => temperatureTrace z.1-Complex.cos z.2)
      (preferredSelectedPoint d,(θ:ℂ)) :=
    (analyticAt_fst.add (analyticAt_fst.inv (preferredSelectedPoint_ne_zero d))).sub
      (Complex.analyticAt_cos.comp analyticAt_snd)
  have he : temperatureTrace (preferredSelectedPoint d)-Complex.cos (θ:ℂ)=
      ((1+Real.cos d.b-Real.cos θ:ℝ):ℂ) := by
    rw [temperatureTrace_preferredSelectedPoint]
    push_cast
    rfl
  have hp := (preferredArccos_analyticAt_real _ hW hW').comp_of_eq ha he
  exact (analyticAt_const.mul hp).cexp

/-- The complete gauge-normalized boundary germ, including every one-body
factor and the actual total product denominator. -/
def preferredBoundaryAngularDensity {N : ℕ} (x : ℂ × (Fin N → ℂ)) : ℂ :=
  let z := fun i => preferredBoundaryRoot x.1 (x.2 i)
  let y := fun i => complexAngleRoot (x.2 i)
  let Z := ∏ i,z i
  (1+Z)/(1-Z)*((-Complex.I)^N*(∏ i,z i/y i)*(rationalKernel y z).det)*
    ∏ i,oneBody (z i)

theorem preferredBoundaryAngularDensity_eq_physical {N : ℕ} (s : ℂ) (w : Fin N → ℂ)
    (hW : ∀i,0<(temperatureTrace s-Complex.cos (w i)).im) :
    preferredBoundaryAngularDensity (s,w)=complexAngularDensity (s,w) := by
  simp only [preferredBoundaryAngularDensity,complexAngularDensity,complexAngularRoots,
    preferredBoundaryRoot_eq_physical (hW _)]
  rfl

/-- The only explicit premises here are individual analytic root germs and
actual algebraic denominator nonvanishing; the following equal-angle theorem
discharges them from the source geometry and prime arithmetic. -/
theorem preferred_analytic_gauge_density {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {N : ℕ} (z y : E → Fin N → ℂ) (c : E)
    (hz : ∀i,AnalyticAt ℂ (fun x => z x i) c)
    (hy : ∀i,AnalyticAt ℂ (fun x => y x i) c)
    (hy0 : ∀i,y c i≠0) (hpair : ∀i j,1-z c i*z c j≠0)
    (hprod : 1-∏i,z c i≠0) :
    AnalyticAt ℂ (fun x => (1+∏i,z x i)/(1-∏i,z x i)*
      ((-Complex.I)^N*(∏i,z x i/y x i)*(rationalKernel (y x) (z x)).det)*
      ∏i,oneBody (z x i)) c := by
  have hZ : AnalyticAt ℂ (fun x => ∏i,z x i) c :=
    Finset.univ.analyticAt_fun_prod (fun i _ => hz i)
  have hR (i j : Fin N) : AnalyticAt ℂ (fun x => rationalKernel (y x) (z x) i j) c :=
    ((hy i).sub (hy j)).div (analyticAt_const.sub ((hz i).mul (hz j))) (hpair i j)
  have hdet : AnalyticAt ℂ (fun x => (rationalKernel (y x) (z x)).det) c := by
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hR (σ i) i)))
  have hratio : AnalyticAt ℂ (fun x => ∏i,z x i/y x i) c :=
    Finset.univ.analyticAt_fun_prod (fun i _ => (hz i).div (hy i) (hy0 i))
  have hbody : AnalyticAt ℂ (fun x => ∏i,oneBody (z x i)) c := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (analyticAt_const.mul (hz i)).div (analyticAt_const.sub ((hz i).pow 2))
    change 1-(z c i)^2≠0
    simpa only [pow_two] using hpair i i
  exact (((analyticAt_const.add hZ).div (analyticAt_const.sub hZ) hprod).mul
    ((analyticAt_const.mul hratio).mul hdet)).mul hbody

theorem preferredBoundaryAngularDensity_analyticAt {N : ℕ} (s : ℂ) (w : Fin N → ℂ)
    (hz : ∀i,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredBoundaryRoot x.1 x.2) (s,w i))
    (hpair : ∀i j,1-preferredBoundaryRoot s (w i)*preferredBoundaryRoot s (w j)≠0)
    (hprod : 1-∏i,preferredBoundaryRoot s (w i)≠0) :
    AnalyticAt ℂ (@preferredBoundaryAngularDensity N) (s,w) := by
  let z := fun x : ℂ × (Fin N → ℂ) => fun i => preferredBoundaryRoot x.1 (x.2 i)
  let y := fun x : ℂ × (Fin N → ℂ) => fun i => complexAngleRoot (x.2 i)
  have hw (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) (s,w) :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (s,w))
  have hy (i : Fin N) : AnalyticAt ℂ (fun x => y x i) (s,w) :=
    (analyticAt_const.mul (hw i)).cexp
  have hzi (i : Fin N) : AnalyticAt ℂ (fun x => z x i) (s,w) := by
    have hmap : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 i)) (s,w) :=
      analyticAt_fst.prod (hw i)
    exact AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 i))
      (g := fun x : ℂ × ℂ => preferredBoundaryRoot x.1 x.2) (hz i) hmap
  exact preferred_analytic_gauge_density z y (s,w) hzi hy
    (fun _ => Complex.exp_ne_zero _) hpair hprod

/-- At every lower even constrained equality point in the right regular
arc the complete actual density has a genuine analytic continuation germ. -/
theorem preferred_lower_equal_density_analytic (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) {N : ℕ} (hN : 0<N)
    (hEven : Even N) (hNp : N<2*p) (l : ℤ) {ρ δ : ℝ}
    (hρ : 0<ρ) (hδ : δ<d.b)
    (hθ : IsingBulk.PrimeFamily.angle N l∈Icc (-d.b+ρ) δ) :
    AnalyticAt ℂ (@preferredBoundaryAngularDensity N)
      (preferredSelectedPoint d,fun _ => (IsingBulk.PrimeFamily.angle N l:ℂ)) := by
  let θ := IsingBulk.PrimeFamily.angle N l
  let z := preferredBoundaryRoot (preferredSelectedPoint d) (θ:ℂ)
  have ht := preferredBoundaryRoot_trace (preferredSelectedPoint d) (θ:ℂ)
  have hζ : preferredSelectedPoint d=IsingBulk.PrimeFamily.angleRoot p a := by
    simp [preferredSelectedPoint,IsingBulk.Branch.radialParameter,hα,IsingBulk.PrimeFamily.angleRoot]
  have hprod : 1-z^N≠0 := preferred_lower_equal_trace_nonresonant hp hp5 ha hN hEven hNp l (by
    simpa only [←hζ,←Complex.ofReal_cos,z,θ] using ht)
  have hpair : 1-z*z≠0 := by
    obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδ hθ
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
      dsimp only [θ] at hh
      linarith
    · have hz : z= -1 := eq_neg_of_add_eq_zero_left hzm
      rw [hz] at htrace
      have hh := congrArg Complex.re htrace
      norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,mul_zero,sub_zero,inv_one,Complex.one_re,Complex.neg_re,
        inv_neg,←Complex.ofReal_cos] at hh
      change (-2:ℝ)=2*(1+Real.cos d.b-Real.cos θ) at hh
      dsimp only [θ] at hh
      linarith
  apply preferredBoundaryAngularDensity_analyticAt
  · intro i
    exact preferredBoundaryRoot_analyticAt_reference d hρ hδ hθ
  · intro i j
    exact hpair
  · simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hprod

/-- Every mixed jet is bounded on one fixed neighborhood of each lower
regular equality chart. The neighborhood is chosen before the derivative order. -/
theorem preferred_lower_equal_density_uniform_jets (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) {N : ℕ} (hN : 0<N)
    (hEven : Even N) (hNp : N<2*p) (l : ℤ) {ρ δ : ℝ}
    (hρ : 0<ρ) (hδ : δ<d.b)
    (hθ : IsingBulk.PrimeFamily.angle N l∈Icc (-d.b+ρ) δ) :
    ∃r : ℝ,0<r ∧ ∀j : ℕ,∃C : ℝ,0<C ∧
      ∀x∈Metric.closedBall (preferredSelectedPoint d,fun _ : Fin N => (IsingBulk.PrimeFamily.angle N l:ℂ)) r,
      ‖iteratedFDeriv ℂ j (@preferredBoundaryAngularDensity N) x‖≤C := by
  have ha := preferred_lower_equal_density_analytic d hp hp5 ha hα hN hEven hNp l hρ hδ hθ
  obtain ⟨r,hr,hball⟩ := ha.exists_ball_analyticOnNhd
  refine ⟨r/2,half_pos hr,?_⟩
  intro j
  let K := Metric.closedBall (preferredSelectedPoint d,fun _ : Fin N => (IsingBulk.PrimeFamily.angle N l:ℂ)) (r/2)
  have hsub : K⊆Metric.ball (preferredSelectedPoint d,fun _ : Fin N => (IsingBulk.PrimeFamily.angle N l:ℂ)) r :=
    Metric.closedBall_subset_ball (by linarith)
  have hc : ContinuousOn (iteratedFDeriv ℂ j (@preferredBoundaryAngularDensity N)) K :=
    ((hball.mono hsub).iteratedFDeriv j).continuousOn
  obtain ⟨C,hC⟩ := (isCompact_closedBall _ (r/2)).exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro x hx
  exact (hC x hx).trans (by have := le_max_left C 0; linarith)

end
end IsingBulk.Preferred22
