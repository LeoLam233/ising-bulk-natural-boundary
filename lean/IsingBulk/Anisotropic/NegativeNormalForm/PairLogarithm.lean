import IsingBulk.Anisotropic.NegativeNormalForm.PairEnergySum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.First
open scoped BigOperators

def actualPairLog {n : ℕ} (Phi : Config n → Config n) (v : Config n) : ℂ :=
  ∑ p∈firstStrictPairs n, Complex.log (coincidenceFactor Phi p.1 p.2 v)

 theorem norm_log_near_one (z : ℂ) (hz : ‖z-1‖≤1/2) : ‖Complex.log z‖≤2*‖z-1‖ := by
  have h := Complex.norm_log_one_add_half_le_self hz
  rw [add_sub_cancel] at h
  nlinarith [norm_nonneg (z-1)]

 theorem actualPairLog_exp {n : ℕ} (Phi : Config n → Config n) (v : Config n)
    (hn : ∀ i j, i≠j → coincidenceFactor Phi i j v≠0) :
    Complex.exp (actualPairLog Phi v)=actualPairMultiplier Phi v := by
  unfold actualPairLog actualPairMultiplier pairMultiplier
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  exact Complex.exp_log (hn p.1 p.2 (ne_of_lt (mem_firstStrictPairs p |>.mp hp)))

 theorem actualPairLog_norm_bound {n : ℕ} (Phi : Config n → Config n) (v : Config n)
    (hclose : ∀ i j, i≠j → ‖coincidenceFactor Phi i j v-1‖≤1/2) :
    ‖actualPairLog Phi v‖≤2*(∑ p∈firstStrictPairs n, ‖coincidenceFactor Phi p.1 p.2 v-1‖) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  exact norm_log_near_one _ (hclose p.1 p.2 (ne_of_lt (mem_firstStrictPairs p |>.mp hp)))

end
end IsingBulk.Anisotropic.NegativeNormalForm
