import IsingBulk.Anisotropic.NegativeCycles.ShiftedInnerPole
import IsingBulk.Anisotropic.NegativeNormalForm.DensityFactors

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open NegativeNormalForm
open scoped BigOperators

theorem formFactorNumerator_shift {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n) :
    formFactorNumerator B rootB phi hphi 0 t v=
      formFactorNumerator B rootB phi hphi d t (fun i => v i-d) := by
  have ha (i : Fin n) : d+(v i-d)=v i := by ring
  have hs (i j : Fin n) : (v i-d)-(v j-d)=v i-v j := by ring
  simp only [formFactorNumerator,pairDenominator,zero_add,ha,hs]

theorem poleParameterDerivative_shift {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n) :
    poleParameterDerivative B phi hphi 0 t v=
      poleParameterDerivative B phi hphi d t (fun i => v i-d) := by
  unfold poleParameterDerivative
  congr 1
  funext u
  exact poleEquation_shift B phi hphi d u v

theorem poleResidue_shift {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (T : Config n → ℂ) (v : Config n) :
    poleResidue B rootB phi hphi 0 (shiftedInnerPole d T) v=
      poleResidue B rootB phi hphi d T (fun i => v i-d) := by
  unfold poleResidue shiftedInnerPole
  rw [formFactorNumerator_shift B rootB phi hphi d,poleParameterDerivative_shift B phi hphi d]

end
end IsingBulk.Anisotropic.NegativeCycles
