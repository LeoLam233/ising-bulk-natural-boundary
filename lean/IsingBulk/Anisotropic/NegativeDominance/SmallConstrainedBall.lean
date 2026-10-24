import IsingBulk.Anisotropic.NegativeDominance.IntegralBallEnvelope

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set
open scoped BigOperators

def smallConstrainedEnergyBall (n : ℕ) (r : ℝ) : Set (Fin n→ℝ) :=
  {x | (∑i : Fin (n+1),(shapeExtend x i)^2)<r^2}

def complexShape {n : ℕ} (x : Fin n→ℝ) : Config (n+1) :=
  fun i => ((shapeExtend x i : ℝ) : ℂ)

theorem complexShape_zeroMean {n : ℕ} (x : Fin n→ℝ) : ZeroMean (complexShape x) := by
  unfold ZeroMean complexShape
  exact_mod_cast sum_shapeExtend x

theorem complexShape_norm_lt {n : ℕ} {r : ℝ} (hr : 0<r) (x : Fin n→ℝ)
    (hx : x∈smallConstrainedEnergyBall n r) : ‖complexShape x‖<r := by
  apply (pi_norm_lt_iff (x := complexShape x) hr).mpr
  intro i
  have hi := Finset.single_le_sum (fun k (_ : k∈Finset.univ) => sq_nonneg (shapeExtend x k))
    (Finset.mem_univ i)
  have hs : (shapeExtend x i)^2<r^2 := hi.trans_lt hx
  have ha : |shapeExtend x i|<r := (sq_lt_sq₀ (abs_nonneg _) hr.le).mp (by simpa only [sq_abs] using hs)
  simpa [complexShape] using ha

theorem smallConstrainedEnergyBall_subset {n : ℕ} {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    smallConstrainedEnergyBall n r⊆constrainedEnergyBall n := by
  intro x hx
  change (∑i : Fin (n+1),(shapeExtend x i)^2)<r^2 at hx
  exact hx.le.trans (by nlinarith)

end
end IsingBulk.Anisotropic.NegativeDominance
