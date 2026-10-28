import IsingBulk.HT22.Physical.ExteriorIdentity
import IsingBulk.HT22.Physical.Symmetries

/-!
# Compact normal convergence of both actual signed odd series

The signed equality is proved from full constrained-torus translations. These
are compact-interior estimates, never the F001 logarithmic boundary tail.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open Set Filter
open scoped Topology BigOperators

def signedOddSeries (negative : Bool) (t : ℂ) : ℂ :=
  ∑' n : ℕ, signedCoefficient negative (2*n+1) t

theorem signedOddSeries_positive (t : ℂ) : signedOddSeries false t = oddSeries t := rfl

theorem negativeCoefficient_eq_neg (n : ℕ) {t : ℂ} (ht : 1 < ‖t‖) :
    signedCoefficient true (2*n+1) t = -coefficient (2*n+1) (-t) := by
  have he := coefficient_odd_neg n ht
  linear_combination he

theorem signedOddSeries_negative {t : ℂ} (ht : 1 < ‖t‖) :
    signedOddSeries true t = -oddSeries (-t) := by
  unfold signedOddSeries oddSeries
  simp_rw [negativeCoefficient_eq_neg _ ht]
  exact tsum_neg

/-- One summable envelope works for both signed families and all odd orders
at each fixed derivative order, on a prescribed compact exterior set. -/
theorem compact_signedOdd_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ {t : ℂ | 1 < ‖t‖}) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ negative : Bool, ∀ n t, t ∈ K →
      ‖iteratedDeriv j (signedCoefficient negative (2*n+1)) t‖ ≤ u n := by
  let L : Set ℂ := K ∪ (Neg.neg '' K)
  have hL : IsCompact L := hK.union (hK.image continuous_neg)
  have hLsub : L ⊆ {t : ℂ | 1 < ‖t‖} := by
    intro t ht
    rcases ht with ht | ⟨z, hz, rfl⟩
    · exact hsub ht
    · simpa only [Set.mem_ofPred_eq, norm_neg] using hsub hz
  obtain ⟨u, hu, hb⟩ := compact_oddCoefficient_derivative_majorant hL hLsub j
  refine ⟨u, hu, ?_⟩
  intro negative n t ht
  cases negative with
  | false => exact hb n t (Or.inl ht)
  | true =>
    rw [negativeCoefficient_iteratedDeriv_norm n j (hsub ht)]
    exact hb n (-t) (Or.inr ⟨t, ht, rfl⟩)

theorem signedOdd_derivative_norm_summable (negative : Bool) (j : ℕ)
    {t : ℂ} (ht : 1 < ‖t‖) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (signedCoefficient negative (2*n+1)) t‖) := by
  cases negative with
  | false => exact oddCoefficient_derivative_norm_summable j ht
  | true =>
    have hn : 1 < ‖-t‖ := by simpa only [norm_neg] using ht
    apply (oddCoefficient_derivative_norm_summable j hn).congr
    intro n
    exact (negativeCoefficient_iteratedDeriv_norm n j ht).symm

theorem signedOddSeries_analyticAt (negative : Bool) {t : ℂ} (ht : 1 < ‖t‖) :
    AnalyticAt ℂ (signedOddSeries negative) t := by
  cases negative with
  | false => exact oddSeries_analyticAt ht
  | true =>
    have hn : 1 < ‖-t‖ := by simpa only [norm_neg] using ht
    have ha := ((oddSeries_analyticAt hn).comp (f := fun z : ℂ => -z) analyticAt_id.neg).neg
    apply ha.congr
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ht] with z hz
    exact (signedOddSeries_negative hz).symm

/-- Parameter differentiation commutes with the entire infinite signed odd sum. -/
theorem signedOddSeries_iteratedDeriv (negative : Bool) (j : ℕ)
    {t : ℂ} (ht : 1 < ‖t‖) :
    iteratedDeriv j (signedOddSeries negative) t =
      ∑' n : ℕ, iteratedDeriv j (signedCoefficient negative (2*n+1)) t := by
  cases negative with
  | false => exact oddSeries_iteratedDeriv j ht
  | true =>
    have he : signedOddSeries true =ᶠ[𝓝 t] (fun z => -oddSeries (-z)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ht] with z hz
      exact signedOddSeries_negative hz
    have hn : 1 < ‖-t‖ := by simpa only [norm_neg] using ht
    rw [he.iteratedDeriv_eq j, iteratedDeriv_fun_neg, iteratedDeriv_comp_neg]
    simp only [smul_eq_mul]
    rw [oddSeries_iteratedDeriv j hn, ← tsum_mul_left, ← tsum_neg]
    apply tsum_congr
    intro n
    exact (negativeCoefficient_iteratedDeriv n j ht).symm

end
end IsingBulk.HT22.Physical
