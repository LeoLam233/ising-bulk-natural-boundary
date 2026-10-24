import IsingBulk.Anisotropic.NegativeDominance.PaperModelData
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

def oddCoefficientLift (f : ℕ→ℂ) (N : ℕ) : ℂ := if Odd N then f (N/2) else 0

@[simp] theorem oddCoefficientLift_even (f : ℕ→ℂ) (n : ℕ) : oddCoefficientLift f (2*n)=0 := by
  simp only [oddCoefficientLift,ite_eq_right_iff]
  intro hn
  obtain ⟨k,hk⟩ := hn
  omega

@[simp] theorem oddCoefficientLift_odd (f : ℕ→ℂ) (n : ℕ) : oddCoefficientLift f (2*n+1)=f n := by
  rw [oddCoefficientLift,ite_eq_left (odd_two_mul_add_one n)]
  congr 1
  omega

theorem oddCoefficientLift_hasSum {f : ℕ→ℂ} (hf : Summable f) :
    HasSum (oddCoefficientLift f) (∑'n,f n) := by
  have he : HasSum (fun n=>oddCoefficientLift f (2*n)) 0 := by simpa only [oddCoefficientLift_even] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have ho : HasSum (fun n=>oddCoefficientLift f (2*n+1)) (∑'n,f n) := by simpa only [oddCoefficientLift_odd] using hf.hasSum
  simpa only [zero_add] using he.even_add_odd ho

theorem negativePaperCoefficient_eq_oddLift {lam : ℝ} {zeta A : ℂ→ℂ} {j : ℕ}
    (hs : Summable (fun n=>negativePaperParticleCoefficient lam zeta A n j)) :
    negativePaperCoefficient lam zeta A j=
      ∑'N,oddCoefficientLift (fun n=>negativePaperParticleCoefficient lam zeta A n j) N := by
  rw [negativePaperCoefficient_eq_particle_tsum]
  exact (oddCoefficientLift_hasSum hs).tsum_eq.symm

end
end IsingBulk.Anisotropic.NegativeDominance
