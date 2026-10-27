import IsingBulk.Preferred22.KernelBounds
import IsingBulk.Preferred22.Hadamard
import IsingBulk.Preferred22.AbsoluteTail
import IsingBulk.First.DominatedAnalyticIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Thickening

/-! Complete-series convergence on exterior compact sets, for the literal
constrained angular coefficients. This is separate from the boundary tail. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped BigOperators Topology

theorem angularBox_volume (n : ℕ) : volume (angularBox n) = ENNReal.ofReal ((2*Real.pi)^n) := by
  simp only [angularBox,volume_pi_pi,Real.volume_Ioc,sub_neg_eq_add,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]
  congr 2
  ring

theorem angularBox_volume_real (n : ℕ) : volume.real (angularBox n) = (2*Real.pi)^n := by
  rw [Measure.real,angularBox_volume,ENNReal.toReal_ofReal (by positivity)]

theorem fullAngularDensity_norm_bound {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) {s : ℂ}
    (hz : ∀ θ : ℝ, ‖physicalRoot (angularW s θ)‖ ≤ q) (θ : Fin N → ℝ) :
    ‖fullAngularDensity s θ‖ ≤
      resolventEnvelope q * (Real.sqrt N * (kernelEnvelope q)^2)^N := by
  have hC : 0 ≤ kernelEnvelope q := by
    unfold kernelEnvelope
    have : 0 < 1-q^2 := by nlinarith
    positivity
  have hR : 0 ≤ resolventEnvelope q := by unfold resolventEnvelope; positivity
  have hzi : ∀ i, ‖angularRoots s θ i‖ ≤ q := fun i => hz (θ i)
  have hd := determinant_bound hN
    (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)) hC
    (gaugeKernel_norm_bound hq0 hq1 _ _ (fun i => angleRoot_norm (θ i)) hzi)
  have hb : (∏ i, ‖oneBody (angularRoots s θ i)‖) ≤ (kernelEnvelope q)^N := by
    calc
      _ ≤ ∏ _i : Fin N, kernelEnvelope q :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => oneBody_norm_bound hq0 hq1 (hzi i))
      _ = _ := by simp
  have hr := product_resolvent_norm_bound hN hq0 hq1 (angularRoots s θ) hzi
  unfold fullAngularDensity
  simp only [norm_mul,norm_prod]
  calc
    _ ≤ (resolventEnvelope q*(Real.sqrt N*kernelEnvelope q)^N)*(kernelEnvelope q)^N :=
      mul_le_mul (mul_le_mul hr hd (norm_nonneg _) hR) hb
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = _ := by
      rw [mul_assoc,← mul_pow]
      congr 2
      ring

/-- Factorial decay is derived from one term of the exponential series. -/
theorem sqrt_factorial_envelope {N : ℕ} (hN : 0 < N) {B : ℝ} (hB : 0 ≤ B) :
    (Real.sqrt N*B)^N/(N.factorial : ℝ) ≤ (Real.exp 1*B/Real.sqrt N)^N := by
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have he : Real.exp (N : ℝ) = (Real.exp 1)^N := by simp
  have hf := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  rw [he] at hf
  have hid : Real.sqrt N*B = (N : ℝ)*(B/Real.sqrt N) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hsqrt.ne').mpr
    linear_combination B * Real.sq_sqrt (Nat.cast_nonneg N)
  rw [hid,mul_pow]
  calc
    _ = ((N : ℝ)^N/(N.factorial : ℝ))*(B/Real.sqrt N)^N := by ring
    _ ≤ (Real.exp 1)^N*(B/Real.sqrt N)^N := mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem coefficient_norm_bound {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) {s : ℂ}
    (hz : ∀ θ : ℝ, ‖physicalRoot (angularW s θ)‖ ≤ q) :
    ‖coefficient N s‖ ≤ resolventEnvelope q *
      (Real.exp 1*(kernelEnvelope q)^2/Real.sqrt N)^N := by
  cases N with
  | zero => omega
  | succ n =>
    let D : ℝ := resolventEnvelope q * (Real.sqrt (n+1 : ℕ) * (kernelEnvelope q)^2)^(n+1)
    have hR : 0 ≤ resolventEnvelope q := by unfold resolventEnvelope; positivity
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hvol : volume (angularBox n) < ⊤ := by rw [angularBox_volume]; exact ENNReal.ofReal_lt_top
    have hint : ‖∫ θ in angularBox n, fullAngularDensity s (constrainedAngles θ)‖ ≤ D*(2*Real.pi)^n := by
      rw [← angularBox_volume_real]
      apply norm_setIntegral_le_of_norm_le_const_ae hvol
      exact Filter.Eventually.of_forall (fun θ => fullAngularDensity_norm_bound hN hq0 hq1 hz _)
    have hnorm : ‖((Nat.factorial (n+1) : ℂ)*(2*Real.pi : ℂ)^n)⁻¹‖ =
        (((n+1).factorial : ℝ)*(2*Real.pi)^n)⁻¹ := by
      rw [norm_inv,norm_mul,norm_pow]
      norm_num [norm_mul,Complex.norm_real,Real.pi_pos.le]
    simp only [coefficient,norm_mul,hnorm]
    calc
      _ ≤ ((((n+1).factorial : ℝ)*(2*Real.pi)^n)⁻¹)*(D*(2*Real.pi)^n) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
      _ = D/((n+1).factorial : ℝ) := by field_simp
      _ = resolventEnvelope q *
          ((Real.sqrt (n+1 : ℕ)*(kernelEnvelope q)^2)^(n+1)/((n+1).factorial : ℝ)) := by dsimp [D]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_factorial_envelope hN (sq_nonneg _)) hR

/-- A single N-independent summable envelope bounds every actual coefficient
on any compact exterior set. -/
theorem compact_coefficient_envelope {K : Set ℂ} (hK : IsCompact K)
    (hext : ∀ s ∈ K, 1 < ‖s‖) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ N : ℕ, ∀ s ∈ K, ‖coefficient N s‖ ≤ A*(B/Real.sqrt N)^N := by
  obtain ⟨q,hq0,hq1,hq⟩ := compact_physical_root_bound hK hext
  have hD : 0 < 1-q^2 := by nlinarith
  refine ⟨resolventEnvelope q,Real.exp 1*(kernelEnvelope q)^2,?_,?_,?_⟩
  · unfold resolventEnvelope
    positivity
  · unfold kernelEnvelope
    positivity
  · intro N s hs
    by_cases hN : 0 < N
    · exact coefficient_norm_bound hN hq0.le hq1 (hq s hs)
    · have he : N=0 := by omega
      subst N
      simp only [coefficient,norm_zero,pow_zero,mul_one]
      unfold resolventEnvelope
      positivity

theorem even_coefficients_absolutely_summable {s : ℂ} (hs : 1 < ‖s‖) :
    Summable (fun n : ℕ => ‖coefficient (2*(n+1)) s‖) := by
  obtain ⟨A,B,_hA,_hB,hbound⟩ := compact_coefficient_envelope (isCompact_singleton (x := s))
    (by intro t ht; simpa only [mem_singleton_iff.mp ht] using hs)
  apply (((sqrt_order_envelope_summable B).comp_injective
    (fun a b h => by change 2*(a+1)=2*(b+1) at h; omega :
      Function.Injective (fun n : ℕ => 2*(n+1)))).mul_left A).of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    exact hbound _ s (mem_singleton s)

/-- Every fixed differentiated family has an N-independent compact envelope. -/
theorem compact_coefficient_jet_envelope {K : Set ℂ} (hK : IsCompact K)
    (hext : ∀ s ∈ K, 1 < ‖s‖) (j : ℕ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ N : ℕ, ∀ s ∈ K, ‖iteratedDeriv j (coefficient N) s‖ ≤ A*(B/Real.sqrt N)^N := by
  have hU : IsOpen {s : ℂ | 1 < ‖s‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open hU hext
  obtain ⟨A,B,hA,hB,hbound⟩ := compact_coefficient_envelope (hK.cthickening (r := δ))
    (fun s hs => hsub hs)
  refine ⟨(j.factorial : ℝ)*A/δ^j,B,by positivity,hB,?_⟩
  intro N s hs
  have hh := IsingBulk.First.cauchy_bound_on_subdisk (U := cthickening δ K)
    (fun t ht => coefficient_analyticAt N (hsub ht)) (hbound N) hδ
    (closedBall_subset_cthickening hs δ) j
  calc
    _ ≤ (j.factorial : ℝ)*(A*(B/Real.sqrt N)^N)/δ^j := hh
    _ = _ := by ring

theorem even_numerical_envelope_summable (A B : ℝ) :
    Summable (fun n : ℕ => A*(B/Real.sqrt (2*(n+1) : ℕ))^(2*(n+1))) := by
  exact ((sqrt_order_envelope_summable B).comp_injective
    (fun a b h => by change 2*(a+1)=2*(b+1) at h; omega :
      Function.Injective (fun n : ℕ => 2*(n+1)))).mul_left A

/-- Proposition 2.1's compact normal convergence statement for every derivative,
expressed as an actual summable majorant of the actual coefficients. -/
theorem compact_even_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hext : ∀ s ∈ K, 1 < ‖s‖) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ s ∈ K,
      ‖iteratedDeriv j (coefficient (2*(n+1))) s‖ ≤ u n := by
  obtain ⟨A,B,_hA,_hB,hbound⟩ := compact_coefficient_jet_envelope hK hext j
  exact ⟨fun n => A*(B/Real.sqrt (2*(n+1) : ℕ))^(2*(n+1)),
    even_numerical_envelope_summable A B,fun n s hs => hbound _ s hs⟩

theorem exterior_closedBall {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ closedBall s r, 1 < ‖t‖ := by
  refine ⟨(‖s‖-1)/2,by linarith,?_⟩
  intro t ht
  have hd : ‖t-s‖ ≤ (‖s‖-1)/2 := by simpa only [mem_closedBall,dist_eq_norm] using ht
  have hn := norm_sub_norm_le s t
  rw [norm_sub_rev] at hn
  linarith

/-- The complete infinite even-particle sum is holomorphic throughout |s|>1. -/
theorem evenSeries_analyticAt {s : ℂ} (hs : 1 < ‖s‖) : AnalyticAt ℂ evenSeries s := by
  obtain ⟨r,hr,hext⟩ := exterior_closedBall hs
  obtain ⟨u,hu,hbound⟩ := compact_even_derivative_majorant (isCompact_closedBall s r) hext 0
  have hd : DifferentiableOn ℂ evenSeries (ball s r) :=
    Complex.differentiableOn_tsum_of_summable_norm hu
      (fun n t ht => (coefficient_analyticAt (2*(n+1))
        (hext t (ball_subset_closedBall ht))).differentiableAt.differentiableWithinAt)
      isOpen_ball (fun n t ht => by simpa using hbound n t (ball_subset_closedBall ht))
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [ball_mem_nhds s hr] with t ht
  exact hd.differentiableAt (isOpen_ball.mem_nhds ht)

/-- Every derivative of the actual infinite series is the actual infinite sum
of the corresponding coefficient derivatives. -/
theorem iteratedDeriv_evenSeries (j : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    iteratedDeriv j evenSeries s = ∑' n : ℕ, iteratedDeriv j (coefficient (2*(n+1))) s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    obtain ⟨r,hr,hext⟩ := exterior_closedBall hs
    obtain ⟨u,hu,hbound⟩ := compact_even_derivative_majorant (isCompact_closedBall s r) hext j
    have heq : iteratedDeriv j evenSeries =ᶠ[𝓝 s]
        (fun t => ∑' n : ℕ, iteratedDeriv j (coefficient (2*(n+1))) t) := by
      filter_upwards [ball_mem_nhds s hr] with t ht
      exact ih (hext t (ball_subset_closedBall ht))
    have hh := Complex.hasSum_deriv_of_summable_norm hu
      (fun n t ht => (IsingBulk.First.analyticAt_iteratedDeriv
        (coefficient_analyticAt (2*(n+1)) (hext t (ball_subset_closedBall ht))) j).differentiableAt.differentiableWithinAt)
      isOpen_ball (fun n t ht => hbound n t (ball_subset_closedBall ht)) (mem_ball_self hr)
    rw [iteratedDeriv_succ,heq.deriv_eq]
    simpa only [iteratedDeriv_succ] using hh.tsum_eq.symm

end
end IsingBulk.Preferred22
