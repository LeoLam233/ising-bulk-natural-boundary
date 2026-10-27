import IsingBulk.Preferred22.FullTheorem
import IsingBulk.Preferred22.FirstCoefficientExplicit
import IsingBulk.Preferred22.RadialProductLimit

/-! The ancillary radial conclusions in the last two sections of the
complete frozen manuscript: the explicit leading coefficient for U and X,
finite limits of all lower U derivatives, bounded lower first-coefficient
derivatives, and all-order bounds for every lower positive even coefficient.
Every source estimate used here is already an unconditional Preferred22 proof. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Exact noncancellation preserving a specified coefficient, instead of
forgetting it in an existential nonzero-limit conclusion. -/
theorem preferred_evenSeries_limit_of_explicit_first {ζ L : ℂ} (hζ : ‖ζ‖=1)
    (m k : ℕ)
    (hfirst : Tendsto (fun ε : ℝ => Real.sqrt ε •
      iteratedDeriv k (coefficient (2*(m+1))) ((1+(ε:ℂ))*ζ)) (𝓝[>] 0) (𝓝 L))
    (hlower : PreferredFiniteComplementStatement ζ m k)
    (htail : PreferredAbsoluteTailStatement ζ (2*(m+1)) k) :
    Tendsto (fun ε : ℝ => Real.sqrt ε •
      iteratedDeriv k evenSeries ((1+(ε:ℂ))*ζ)) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨C,rC,_hC,hrC,hC⟩ := hlower
  obtain ⟨D,rD,_hD,hrD,hD⟩ := htail k le_rfl
  let f : ℝ → ℂ := fun ε => iteratedDeriv k evenSeries ((1+(ε:ℂ))*ζ)-
    iteratedDeriv k (coefficient (2*(m+1))) ((1+(ε:ℂ))*ζ)
  have hf : Tendsto (fun ε : ℝ => Real.sqrt ε • f ε) (𝓝[>] 0) (𝓝 0) := by
    apply sqrt_log_bound_tendsto_zero (C := C) (D := D) (lt_min hrC hrD)
    intro ε hε hε0
    have hce := hC ε hε (hε0.trans_le (min_le_left _ _))
    obtain ⟨hsumt,hdt⟩ := hD ε hε (hε0.trans_le (min_le_right _ _))
    have hs := radialPath_exterior hζ hε
    have hsum := (even_coefficient_derivatives_absolutely_summable k hs).comp_injective
      (fun a b h => by change a+(m+1)=b+(m+1) at h; omega :
        Function.Injective (fun n : ℕ => n+(m+1)))
    have hnorm : ‖∑' n : ℕ,iteratedDeriv k (coefficient (2*(n+m+2))) ((1+(ε:ℂ))*ζ)‖ ≤
        actualHigherTail ζ (2*(m+1)) k ε := by
      rw [actualHigherTail_eq_shifted ζ m k ε hsumt]
      apply norm_tsum_le_tsum_norm
      convert hsum using 1
      funext n
      congr 3
    dsimp only [f]
    rw [evenSeries_derivative_split k m hs]
    have heq (a b c : ℂ) : a+b+c-b=a+c := by ring
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add ((norm_sum_le _ _).trans hce) (hnorm.trans hdt))
  have hh := hfirst.add hf
  simp only [add_zero] at hh
  convert hh using 1
  funext ε
  dsimp only [f]
  rw [smul_sub]
  abel

/-- Equation (U-leading), with the manuscript's explicit, nonzero Lambda.
The sum here is the actual complete positive-even infinite series. -/
theorem preferred_prime_evenSeries_explicit_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    preferredLeadingCoefficient (2*p-1) (IsingBulk.PrimeFamily.angle p a)≠0 ∧
      Tendsto (fun ε : ℝ => Real.sqrt ε • iteratedDeriv ((2*p)^2/2-1)
        evenSeries ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a))
        (𝓝[>] 0) (𝓝 (preferredLeadingCoefficient (2*p-1) (IsingBulk.PrimeFamily.angle p a))) := by
  obtain ⟨hL,hfirst⟩ := preferred_prime_first_explicit_limit hp hp5 ha
  obtain ⟨_hf,hl,ht⟩ := preferred_selected_analytic_obligations p hp hp5 a ha
  have hN : 2*(p-1+1)=2*p := by omega
  have hζ : ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 := Complex.norm_exp_ofReal_mul_I _
  refine ⟨hL,preferred_evenSeries_limit_of_explicit_first
    hζ (p-1) ((2*p)^2/2-1) ?_ hl ?_⟩
  · simpa only [hN] using hfirst
  · simpa only [hN] using ht

/-- The lower derivatives of the complete first singular coefficient
actually have finite limits; in particular they are bounded as stated
in Theorem 10.4. -/
theorem preferred_prime_first_lower_derivative_limits {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    ∀ j : ℕ,j<(2*p)^2/2-1 → ∃ L : ℂ,
      Tendsto (fun ε : ℝ => iteratedDeriv j (coefficient (2*p))
        ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)) (𝓝[>] 0) (𝓝 L) := by
  have hζ : ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 := Complex.norm_exp_ofReal_mul_I _
  exact preferred_lower_radial_limits_of_sqrt_limit hζ
    (fun ε hε => coefficient_analyticAt (2*p) (radialPath_exterior hζ hε))
    ((2*p)^2/2-1) (preferred_prime_first_explicit_limit hp hp5 ha).2

theorem preferred_prime_first_lower_derivative_bounds {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    ∀ j : ℕ,j<(2*p)^2/2-1 → ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧
      ∀ ε : ℝ,0<ε → ε≤ε₀ → ‖iteratedDeriv j (coefficient (2*p))
        ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)‖≤C := by
  have hζ : ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 := Complex.norm_exp_ofReal_mul_I _
  exact preferred_lower_radial_bounds_of_sqrt_limit hζ
    (fun ε hε => coefficient_analyticAt (2*p) (radialPath_exterior hζ hε))
    ((2*p)^2/2-1) (preferred_prime_first_explicit_limit hp hp5 ha).2

/-- Every lower complex derivative of U has a finite radial limit. -/
theorem preferred_prime_evenSeries_lower_derivative_limits {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    ∀ j : ℕ,j<(2*p)^2/2-1 → ∃ L : ℂ,
      Tendsto (fun ε : ℝ => iteratedDeriv j evenSeries
        ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)) (𝓝[>] 0) (𝓝 L) := by
  have hζ : ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 := Complex.norm_exp_ofReal_mul_I _
  exact preferred_lower_radial_limits_of_sqrt_limit hζ
    (fun ε hε => evenSeries_analyticAt (radialPath_exterior hζ hε))
    ((2*p)^2/2-1) (preferred_prime_evenSeries_explicit_limit hp hp5 ha).2

/-- Exact conversion of real radial derivatives to complex derivatives.
The identity is local on the positive ray and assumes no boundary extension. -/
theorem preferred_iteratedDeriv_radialPath {R : ℂ → ℂ} (ζ : ℂ)
    (hR : ∀ t : ℝ,0<t → AnalyticAt ℂ R ((1+(t:ℂ))*ζ))
    (j : ℕ) (ε : ℝ) (hε : 0<ε) :
    iteratedDeriv j (fun t : ℝ => R ((1+(t:ℂ))*ζ)) ε =
      ζ^j * iteratedDeriv j R ((1+(ε:ℂ))*ζ) := by
  induction j generalizing ε with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ j ih =>
    have he : iteratedDeriv j (fun t : ℝ => R ((1+(t:ℂ))*ζ)) =ᶠ[𝓝 ε]
        (fun t : ℝ => ζ^j * iteratedDeriv j R ((1+(t:ℂ))*ζ)) := by
      filter_upwards [Ioi_mem_nhds hε] with t ht
      exact ih t ht
    have hd := (preferred_radial_iterated_hasDerivAt ζ ε j (hR ε hε)).const_mul (ζ^j)
    rw [iteratedDeriv_succ]
    exact he.deriv_eq.trans (by
      convert hd.deriv using 1
      rw [pow_succ]
      ring)

/-- The real derivatives of the radial function g also have the finite
limits used in the manuscript's successive integration argument. -/
theorem preferred_prime_radial_evenSeries_lower_limits {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    ∀ j : ℕ,j<(2*p)^2/2-1 → ∃ L : ℂ,
      Tendsto (fun ε : ℝ => iteratedDeriv j (fun t : ℝ => evenSeries
        ((1+(t:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)) ε) (𝓝[>] 0) (𝓝 L) := by
  intro j hj
  let ζ := IsingBulk.PrimeFamily.angleRoot p a
  have hζ : ‖ζ‖=1 := Complex.norm_exp_ofReal_mul_I _
  obtain ⟨L,hL⟩ := preferred_prime_evenSeries_lower_derivative_limits hp hp5 ha j hj
  refine ⟨ζ^j*L,?_⟩
  apply (hL.const_mul (ζ^j)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (preferred_iteratedDeriv_radialPath ζ
    (fun t ht => evenSeries_analyticAt (radialPath_exterior hζ ht)) j ε hε).symm

theorem preferred_prime_root_nonaxis {p : ℕ} {a : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a) :
    (IsingBulk.PrimeFamily.angleRoot p a)^(4:ℕ)≠1 := by
  have hr : 0 < (IsingBulk.PrimeFamily.angleRoot p a).re := by
    simpa [IsingBulk.PrimeFamily.angleRoot,Complex.exp_mul_I,Complex.cos_ofReal_re] using
      Real.cos_pos_of_mem_Ioo ⟨by linarith [ha.1,Real.pi_pos],ha.2⟩
  have hi : 0 < (IsingBulk.PrimeFamily.angleRoot p a).im := by
    simpa [IsingBulk.PrimeFamily.angleRoot,Complex.exp_mul_I,Complex.sin_ofReal_re] using
      Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2,Real.pi_pos])
  exact first_quadrant_pow_four_ne_one hr hi

/-- The exact physical leading coefficient of the complete connected
bulk function X=M² U is M²(zeta)*Lambda, and is nonzero. -/
theorem preferred_prime_bulk_explicit_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    magnetizationSquared (IsingBulk.PrimeFamily.angleRoot p a) *
      preferredLeadingCoefficient (2*p-1) (IsingBulk.PrimeFamily.angle p a)≠0 ∧
      Tendsto (fun ε : ℝ => Real.sqrt ε • iteratedDeriv ((2*p)^2/2-1)
        bulkFunction ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a))
        (𝓝[>] 0) (𝓝 (magnetizationSquared (IsingBulk.PrimeFamily.angleRoot p a) *
          preferredLeadingCoefficient (2*p-1) (IsingBulk.PrimeFamily.angle p a))) := by
  have hζ : ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hfour := preferred_prime_root_nonaxis ha
  obtain ⟨hL,hlim⟩ := preferred_prime_evenSeries_explicit_limit hp hp5 ha
  refine ⟨mul_ne_zero (magnetizationSquared_ne_zero_at_unit_nonaxis hζ hfour) hL,?_⟩
  exact preferred_radial_product_leading_limit hζ
    (magnetizationSquared_analyticAt_unit_nonaxis hζ hfour)
    (fun ε hε => evenSeries_analyticAt (radialPath_exterior hζ hε)) ((2*p)^2/2-1) hlim

/-- Every lower positive even particle coefficient has bounded derivatives
of every fixed order, including the two-particle coefficient. -/
theorem preferred_prime_lower_coefficient_bounds {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (n j : ℕ) (hn : 2*(n+1)<2*p) :
    ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ‖iteratedDeriv j (coefficient (2*(n+1)))
        ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)‖≤C := by
  have hh := preferred_actual_finite_complement (preferredPrimeBranchData ha) hp hp5 ha rfl j
  change PreferredFiniteComplementStatement (IsingBulk.PrimeFamily.angleRoot p a) (p-1) j at hh
  obtain ⟨C,ε₀,hC,hε₀,hb⟩ := hh
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro ε hε hε0
  apply le_trans _ (hb ε hε hε0)
  exact Finset.single_le_sum (f := fun i : ℕ => ‖iteratedDeriv j (coefficient (2*(i+1)))
    ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)‖)
    (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega : n<p-1))

end
end IsingBulk.Preferred22
