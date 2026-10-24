import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.PhysicalField
noncomputable section
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

def mean (p A : Ω → ℝ) : ℝ := ∑ ω, p ω*A ω

/-- Exact finite marginal change of measure for the energy field −h S.
The factor β is in the Boltzmann exponential, not absorbed into h. -/
def tiltedMean (β : ℝ) (p A S : Ω → ℝ) (h : ℝ) : ℝ :=
  (∑ ω, p ω*A ω*Real.exp ((β*S ω)*h)) /
    (∑ ω, p ω*Real.exp ((β*S ω)*h))

theorem tiltedMean_zero (β : ℝ) (p A S : Ω → ℝ) (hp : ∑ ω, p ω=1) :
    tiltedMean β p A S 0=mean p A := by simp [tiltedMean,mean,hp]

theorem tiltedMean_hasDerivAt_zero (β : ℝ) (p A S : Ω → ℝ)
    (hp : ∑ ω, p ω=1) :
    HasDerivAt (tiltedMean β p A S)
      (β*(mean p (fun ω => A ω*S ω)-mean p A*mean p S)) 0 := by
  have he (ω : Ω) : HasDerivAt (fun h : ℝ => Real.exp ((β*S ω)*h)) (β*S ω) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul (β*S ω)).exp)
  have hn := HasDerivAt.fun_sum (u := Finset.univ)
    (fun ω _ => (he ω).const_mul (p ω*A ω))
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun ω _ => (he ω).const_mul (p ω))
  have hz : (∑ ω, p ω*Real.exp ((β*S ω)*0))≠0 := by simp [hp]
  have h := hn.div hd hz
  have hna : (∑ ω, p ω*A ω*(β*S ω))=β*mean p (fun ω => A ω*S ω) := by
    simp only [mean,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hda : (∑ ω, p ω*(β*S ω))=β*mean p S := by
    simp only [mean,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  convert h using 1
  · rfl
  · simp only [mul_zero,Real.exp_zero,mul_one,hp,hna,hda,one_pow,div_one]
    unfold mean
    ring

def covariance (p A B : Ω → ℝ) : ℝ := mean p (fun ω => A ω*B ω)-mean p A*mean p B

theorem mean_sum {ι : Type*} [Fintype ι] (p : Ω → ℝ) (A : ι → Ω → ℝ) :
    mean p (fun ω => ∑ i, A i ω)=∑ i, mean p (A i) := by
  simp only [mean,Finset.mul_sum]
  exact Finset.sum_comm

theorem covariance_sum {ι : Type*} [Fintype ι] (p A : Ω → ℝ) (B : ι → Ω → ℝ) :
    covariance p A (fun ω => ∑ i, B i ω)=∑ i, covariance p A (B i) := by
  unfold covariance
  simp only [Finset.mul_sum,mean_sum,Finset.sum_sub_distrib]

theorem tiltedMean_sum_hasDerivAt_zero {ι : Type*} [Fintype ι]
    (β : ℝ) (p A : Ω → ℝ) (B : ι → Ω → ℝ) (hp : ∑ ω, p ω=1) :
    HasDerivAt (tiltedMean β p A (fun ω => ∑ i, B i ω))
      (β*∑ i, covariance p A (B i)) 0 := by
  rw [← covariance_sum]
  exact tiltedMean_hasDerivAt_zero β p A _ hp

end
end IsingBulk.Anisotropic.PhysicalField
