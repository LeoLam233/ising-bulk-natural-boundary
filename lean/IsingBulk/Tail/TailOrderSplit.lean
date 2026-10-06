import IsingBulk.Tail.UltraHighTheorem
import IsingBulk.Final.UpperNoncancellation

/-! Exact finite/ultra-high partition of the actual absolute tail. This is
assembly algebra only: the finite-order sector estimates remain to be proved. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Final IsingBulk.Branch Filter Set
open scoped Topology BigOperators

def actualSubthresholdTail (p : ℕ) (theta L : ℝ) (j : ℕ) (e : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (ultraHighFactorialThreshold L (Real.log (1/e))-(p+1)),
    ‖iteratedDeriv j (upperFormFactor (2*(n+p+1))) (radialParameter theta e)‖

theorem absolute_tail_split_at_order {p K : ℕ} (hK : p+1 ≤ K)
    {theta e : ℝ} (htheta : 0 < Real.sin theta) (he : 0 < e) (j : ℕ) :
    (∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (2*(n+p+1))) (radialParameter theta e)‖) =
      (∑ n ∈ Finset.range (K-(p+1)),
        ‖iteratedDeriv j (upperFormFactor (2*(n+p+1))) (radialParameter theta e)‖) +
      ∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (2*(K+n))) (radialParameter theta e)‖ := by
  have hs := (upperEven_derivative_summable j (sourceRadialTrace_pos htheta he)).comp_injective
    (show Function.Injective (fun n : ℕ => n+p) from fun _ _ h => by dsimp at h; omega)
  have hh := hs.sum_add_tsum_nat_add (K-(p+1))
  have heq : K-(p+1)+(p+1)=K := Nat.sub_add_cancel hK
  simpa only [Function.comp_def,Nat.add_assoc,heq,Nat.add_comm K] using hh.symm

theorem ultraHigh_threshold_eventually_ge (L : ℝ) (hL : 1 ≤ L) (p : ℕ) :
    ∀ᶠ e : ℝ in 𝓝[>] 0, p+1 ≤ ultraHighFactorialThreshold L (Real.log (1/e)) := by
  filter_upwards [log_inverse_tendsto_atTop.eventually (eventually_ge_atTop ((p:ℝ)+1))]
    with e he
  have hc : L*(Real.log (1/e)+1)^2 ≤
      (ultraHighFactorialThreshold L (Real.log (1/e)):ℝ) := Nat.le_ceil _
  have hpos : 0 ≤ Real.log (1/e) := by linarith [(Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have hscale := mul_le_mul_of_nonneg_right hL (sq_nonneg (Real.log (1/e)+1))
  have hh : (p:ℝ)+1 ≤ (ultraHighFactorialThreshold L (Real.log (1/e)):ℝ) := by nlinarith
  exact_mod_cast hh

theorem absolute_tail_eventually_split {p : ℕ} {theta L : ℝ}
    (htheta : 0 < Real.sin theta) (hL : 1 ≤ L) (j : ℕ) :
    (fun e => ∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (2*(n+p+1)))
      (radialParameter theta e)‖) =ᶠ[𝓝[>] 0]
      (fun e => actualSubthresholdTail p theta L j e + ultraHighActualTail theta L j e) := by
  filter_upwards [self_mem_nhdsWithin,ultraHigh_threshold_eventually_ge L hL p] with e he hK
  exact absolute_tail_split_at_order hK htheta he j

end
end IsingBulk.Tail
