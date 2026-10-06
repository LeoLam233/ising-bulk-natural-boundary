import IsingBulk.Tail.UpperExteriorSeries
import IsingBulk.First.FirstTheorem
import IsingBulk.Final.LowerEvenSum
import IsingBulk.Final.AbsoluteTail
import IsingBulk.Final.LeibnizLimit
import IsingBulk.Final.MagnetizationBoundary

/-! Actual upper-trace series noncancellation. The sole unproved analytic
hypothesis here is the literal absolute higher-tail assertion of thm:tail;
it is permitted in thm:conditional, never in an unconditional tail endpoint. -/
namespace IsingBulk.Final
noncomputable section
open Filter IsingBulk.First IsingBulk.Branch IsingBulk.Tail
open scoped Topology BigOperators

theorem sourceRadialTrace_pos {theta e : ℝ} (htheta : 0 < Real.sin theta) (he : 0 < e) :
    0 < (sourceS (radialParameter theta e)).im := by
  have h := (radial_trace_components theta e (by linarith)).2
  change (sourceS (radialParameter theta e)).im = _ at h
  rw [h]
  have heq : 2*e-e^2/(1+e) = e*(2+e)/(1+e) := by
    field_simp
    ring
  rw [heq]
  positivity

theorem upperEvenSeries_radial_split {p : ℕ} (hp : 0 < p) (j : ℕ)
    {theta e : ℝ} (htheta : 0 < Real.sin theta) (he : 0 < e) :
    iteratedDeriv j upperEvenSeries (radialParameter theta e) =
      (∑ n ∈ Finset.range (p-1), iteratedDeriv j (upperFormFactor (2*(n+1)))
        (radialParameter theta e)) +
      iteratedDeriv j (upperFormFactor (2*p)) (radialParameter theta e) +
      ∑' n : ℕ, iteratedDeriv j (upperFormFactor (2*(n+p+1))) (radialParameter theta e) := by
  have hs := sourceRadialTrace_pos htheta he
  rw [upperEvenSeries_iteratedDeriv j hs]
  have hsum := (upperEven_derivative_summable j hs).of_norm.sum_add_tsum_nat_add p
  have hpred : p-1+1=p := by omega
  rw [← hpred,Finset.sum_range_succ] at hsum
  simpa only [hpred] using hsum.symm

/-- The exact source higher-even tail, with the absolute sum taken before
any asymptotic limit. No estimate of individual summands can replace it. -/
def AbsoluteUpperTailSmall (p : ℕ) (theta : ℝ) (j : ℕ) : Prop :=
  Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
    (fun e => ∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (2*(n+p+1)))
      (radialParameter theta e)‖)
    (fun e => (Real.sqrt e)⁻¹)

theorem actual_upper_complex_tail_small {p : ℕ} {theta : ℝ} (htheta : 0 < Real.sin theta)
    (j : ℕ) (hTail : AbsoluteUpperTailSmall p theta j) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => ∑' n : ℕ, iteratedDeriv j (upperFormFactor (2*(n+p+1)))
        (radialParameter theta e)) (fun e => (Real.sqrt e:ℂ)⁻¹) := by
  apply complex_tail_isLittleO_of_absolute _ hTail
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (upperEven_derivative_summable j (sourceRadialTrace_pos htheta he)).comp_injective
    (fun a b h => by omega)

theorem selected_upper_top_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b))
    (hTail : AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta ((2*p)^2/2-1)) :
    let k := (2*p)^2/2-1
    let A := selectedOrderedChart ha hb
    let L := localLeadingCoefficient A (2*p-1) k
    L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => iteratedDeriv k upperEvenSeries (radialParameter A.theta e) -
        (Real.sqrt e:ℂ)⁻¹*(2*L)) (fun e => (Real.sqrt e:ℂ)⁻¹) := by
  dsimp only
  obtain ⟨hL,hTop,_⟩ := first_upper_asymptotic hp hp11 ha hb hab
  have hn : 2*p-1+1=2*p := by have := hp.pos; omega
  simp only [hn] at hL hTop
  refine ⟨hL,?_⟩
  have hLow := lower_even_sum_isLittleO hp hp11 ha hb hTW ((2*p)^2/2-1)
  have hT := actual_upper_complex_tail_small (selectedOrderedChart ha hb).sin_theta_pos _ hTail
  apply ((hLow.add hTop).add hT).congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin] with e he
  rw [upperEvenSeries_radial_split hp.pos _ (selectedOrderedChart ha hb).sin_theta_pos he]
  ring

theorem selected_upper_lower_negligible {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b))
    {j : ℕ} (hj : j < (2*p)^2/2-1)
    (hTail : AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => iteratedDeriv j upperEvenSeries (radialParameter (selectedOrderedChart ha hb).theta e))
      (fun e => (Real.sqrt e:ℂ)⁻¹) := by
  obtain ⟨_,_,d,hd,hfirst⟩ := first_upper_asymptotic hp hp11 ha hb hab
  have hn : 2*p-1+1=2*p := by have := hp.pos; omega
  simp only [hn] at hfirst
  obtain ⟨C,_,hbound⟩ := hfirst j hj
  have hF : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => iteratedDeriv j (upperFormFactor (2*p))
        (radialParameter (selectedOrderedChart ha hb).theta e))
      (fun e => (Real.sqrt e:ℂ)⁻¹) := by
    apply IsingBulk.First.bounded_radial_term_isLittleO (show 0 < d/2 by positivity)
    exact fun e he hed => hbound e he (by linarith)
  have hLow := lower_even_sum_isLittleO hp hp11 ha hb hTW j
  have hT := actual_upper_complex_tail_small (selectedOrderedChart ha hb).sin_theta_pos _ hTail
  apply ((hLow.add hF).add hT).congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (upperEvenSeries_radial_split hp.pos j (selectedOrderedChart ha hb).sin_theta_pos he).symm

/-- The internally convergent actual normalized bulk on the upper-trace domain. -/
def normalizedUpperBulk (s : ℂ) : ℂ :=
  1-magnetizationSquared s+2*magnetizationSquared s*upperEvenSeries s

/-- Selected-point bulk noncancellation with exactly the source's all-j
absolute-tail hypothesis. The conclusion forbids a genuine open-neighborhood
extension; there is no assumed global holomorphic continuation. -/
theorem selected_bulk_nonextension_of_absolute_tail {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b))
    (hTail : ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j) :
    ¬ HasExteriorExtension normalizedUpperBulk (PrimeFamily.selectedPoint p a b) := by
  let k := (2*p)^2/2-1
  let A := selectedOrderedChart ha hb
  let L := localLeadingCoefficient A (2*p-1) k
  let z := PrimeFamily.selectedPoint p a b
  obtain ⟨hL,hTop⟩ := selected_upper_top_asymptotic hp hp11 ha hb hab hTW (hTail k le_rfl)
  change L ≠ 0 at hL
  change Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
    (fun e => iteratedDeriv k upperEvenSeries (radialParameter A.theta e) -
      (Real.sqrt e:ℂ)⁻¹*(2*L)) (fun e => (Real.sqrt e:ℂ)⁻¹) at hTop
  have hpath (e : ℝ) : radialParameter A.theta e = (1+(e:ℂ))*z := by
    simp only [radialParameter,A,z,selectedOrderedChart,PrimeFamily.selectedPoint,
      Complex.ofReal_add,Complex.ofReal_one]
  have hlimits : ∀ i : ℕ, i ≤ k → Tendsto
      (fun e : ℝ => Real.sqrt e • iteratedDeriv i upperEvenSeries ((1+(e:ℂ))*z))
      (𝓝[>] 0) (𝓝 (if i=k then 2*L else 0)) := by
    intro i hi
    by_cases hik : i=k
    · subst i
      rw [ite_eq_left rfl]
      simpa only [hpath] using sqrt_limit_of_isLittleO hTop
    · rw [ite_eq_right hik]
      have hlow := selected_upper_lower_negligible hp hp11 ha hb hab hTW
        (lt_of_le_of_ne hi hik) (hTail i hi)
      have hl : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
          (fun e => iteratedDeriv i upperEvenSeries (radialParameter A.theta e) -
            (Real.sqrt e:ℂ)⁻¹*(0:ℂ)) (fun e => (Real.sqrt e:ℂ)⁻¹) := by
        simpa only [mul_zero,sub_zero] using hlow
      simpa only [hpath] using sqrt_limit_of_isLittleO hl
  have hm := selectedPoint_magnetization_regular ha hb
  have hU : ∀ᶠ e : ℝ in 𝓝[>] 0, AnalyticAt ℂ upperEvenSeries ((1+(e:ℂ))*z) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    rw [← hpath]
    exact upperEvenSeries_analyticAt (sourceRadialTrace_pos A.sin_theta_pos he)
  have hbulk := sqrt_radial_bulk_limit k hm.1 hU hlimits
  apply no_extension_of_nonzero_radial_limit (show ‖z‖=1 from Complex.norm_exp_ofReal_mul_I _)
    (show 4*magnetizationSquared z*L ≠ 0 from mul_ne_zero (mul_ne_zero (by norm_num) hm.2) hL) k
  exact hbulk

end
end IsingBulk.Final
