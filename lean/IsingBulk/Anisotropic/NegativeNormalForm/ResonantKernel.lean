import IsingBulk.Anisotropic.NegativeNormalForm.SimplePoleResidue
import IsingBulk.Anisotropic.NegativeNormalForm.PoleEquation

/-! Exact rational-phase resonance and identification of the actual kernel
with the shifted phase-sum coth kernel used in the residue calculation. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem coshHalf_div_sinhHalf (z : ℂ) :
    Complex.cosh (z/2)/Complex.sinh (z/2) = (Complex.exp z+1)/(Complex.exp z-1) := by
  have he : Complex.exp (z/2)*Complex.exp (z/2)=Complex.exp z := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hn := Complex.exp_ne_zero (z/2)
  have hc : Complex.cosh (z/2)=(Complex.exp z+1)/(2*Complex.exp (z/2)) := by
    rw [Complex.cosh, Complex.exp_neg]
    field_simp
    linear_combination he
  have hs : Complex.sinh (z/2)=(Complex.exp z-1)/(2*Complex.exp (z/2)) := by
    rw [Complex.sinh, Complex.exp_neg]
    field_simp
    linear_combination he
  rw [hc, hs, div_div_div_comm, div_self (mul_ne_zero (by norm_num) hn), div_one]

theorem rational_phase_resonance (p k r : ℕ) (hp : p ≠ 0) :
    Complex.exp (((p*k : ℕ) : ℂ) * (((2*Real.pi*r/p : ℝ) : ℂ)*Complex.I)) = 1 := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have he : ((p*k : ℕ) : ℂ) * (((2*Real.pi*r/p : ℝ) : ℂ)*Complex.I) =
      ((k*r : ℕ) : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by
    push_cast
    field_simp
  rw [he, Complex.exp_nat_mul_two_pi_mul_I]

/-- The full phase sum, not shifted to make its central value zero. -/
def fullPhaseSum {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d t : ℂ) (v : Config n) : ℂ :=
  ∑ i, negativePhase B phi hphi t (d+v i)

theorem fullPhaseSum_eq_poleEquation {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) :
    fullPhaseSum B phi hphi d t v = poleEquation B phi hphi d t v + n*((phi : ℂ)*Complex.I) := by
  simp [fullPhaseSum, poleEquation, Finset.sum_sub_distrib]

/-- Resonance identifies the actual global kernel with the local kernel whose
simple pole was proved, without imposing a phase common to distinct n. -/
theorem resonant_kernel_eq {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n)
    (hres : Complex.exp ((n : ℂ)*((phi : ℂ)*Complex.I))=1) :
    (Complex.exp (fullPhaseSum B phi hphi d t v)+1) /
      (Complex.exp (fullPhaseSum B phi hphi d t v)-1) =
      cothHalf (fun u => poleEquation B phi hphi d u v) t := by
  rw [fullPhaseSum_eq_poleEquation, Complex.exp_add, hres, mul_one]
  exact (coshHalf_div_sinhHalf _).symm

end
end IsingBulk.Anisotropic.NegativeNormalForm
