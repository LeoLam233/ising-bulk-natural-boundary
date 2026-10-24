import IsingBulk.Anisotropic.NegativeNormalForm.PoleEquation
import IsingBulk.Anisotropic.NegativeNormalForm.TripleScalarIdentity
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectionLinear

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

def poleAverage {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (d t : ℂ) (v : Config n) : ℂ := poleEquation B phi hphi d t v/(n:ℂ)

def averageSquaredNorm {n : ℕ} (v : Config n) : ℝ := (∑ i, ‖v i‖^2)/(n:ℝ)

theorem poleAverage_zeroMean_bound {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (v : Config n) (hv : ZeroMean v) {M : ℝ}
    (hfirst : ∀ i, phaseIncrement B phi hphi d (1-Complex.cos d) (v i)=
      v i*phaseFirstFactor B phi hphi d (1-Complex.cos d) (v i))
    (hsecond : ∀ i, phaseFirstFactor B phi hphi d (1-Complex.cos d) (v i)-
      phaseFirstFactor B phi hphi d (1-Complex.cos d) 0=
      v i*phaseSecondFactor B phi hphi d (1-Complex.cos d) (v i))
    (hbound : ∀ i, ‖phaseSecondFactor B phi hphi d (1-Complex.cos d) (v i)‖≤M) :
    ‖poleAverage B phi hphi d (1-Complex.cos d) v‖≤M*averageSquaredNorm v := by
  have hterm (i : Fin n) : negativePhase B phi hphi (1-Complex.cos d) (d+v i)-(phi:ℂ)*Complex.I =
      v i*phaseFirstFactor B phi hphi d (1-Complex.cos d) 0+
        (v i)^2*phaseSecondFactor B phi hphi d (1-Complex.cos d) (v i) := by
    have hh := hfirst i
    simp only [phaseIncrement,negativePhase_center] at hh
    linear_combination hh+(v i)*(hsecond i)
  have he : poleEquation B phi hphi d (1-Complex.cos d) v=
      ∑ i, (v i)^2*phaseSecondFactor B phi hphi d (1-Complex.cos d) (v i) := by
    unfold poleEquation
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hv,zero_mul,zero_add]
  have hh : ‖poleEquation B phi hphi d (1-Complex.cos d) v‖≤M*(∑ i, ‖v i‖^2) := by
    rw [he]
    calc
      _ ≤ ∑ i, ‖(v i)^2*phaseSecondFactor B phi hphi d (1-Complex.cos d) (v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖v i‖^2*M := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,norm_pow]
        exact mul_le_mul_of_nonneg_left (hbound i) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  unfold poleAverage averageSquaredNorm
  rw [norm_div,Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)).trans_eq (by ring)

end
end IsingBulk.Anisotropic.NegativeNormalForm
