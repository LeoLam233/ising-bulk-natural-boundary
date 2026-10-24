import IsingBulk.Anisotropic.NegativeNormalForm.SimplePoleResidue
import IsingBulk.Anisotropic.NegativeCycles.CentralWindingSymmetry
import IsingBulk.Anisotropic.NegativeCycles.WindingTranslation

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open NegativeNormalForm IsingBulk.First Set MeasureTheory
open scoped BigOperators

theorem formFactorNumerator_neg_center {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n) :
    formFactorNumerator B rootB phi hphi (-d) t (-v)=formFactorNumerator B rootB phi hphi d t v := by
  have he (i : Fin n) : -d+(-v) i=-(d+v i) := by simp only [Pi.neg_apply]; ring
  have hp (i j : Fin n) : ((-v) i-(-v) j)/2=-((v i-v j)/2) := by simp only [Pi.neg_apply]; ring
  simp only [formFactorNumerator,pairDenominator,he,hp,negativePhase_neg_angle,
    Complex.sin_neg,neg_div,neg_sq]

theorem poleEquation_neg_center {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n) :
    poleEquation B phi hphi (-d) t (-v)=poleEquation B phi hphi d t v := by
  have he (i : Fin n) : -d+(-v) i=-(d+v i) := by simp only [Pi.neg_apply]; ring
  simp only [poleEquation,he,negativePhase_neg_angle]

theorem shapeExtend_neg_fun {n : ℕ} (v : Fin n→ℝ) : shapeExtend (-v)= -shapeExtend v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [shapeExtend,Finset.sum_neg_distrib]
  · simp [shapeExtend]

theorem constrainedSquaredRadius_neg {n : ℕ} (v : Fin n→ℝ) :
    constrainedSquaredRadius (-v)=constrainedSquaredRadius v := by
  simp only [constrainedSquaredRadius,squaredRadius,shapeExtend_neg_fun,Pi.neg_apply,neg_sq]

/-- Full physical central winding integrals, not just their center amplitudes,
are equal under exact real-angle reflection. No pole-witness matching needed. -/
theorem opposite_winding_kernel_integral (n : ℕ) (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (σ : ℝ) :
    (∫ v in {v : Fin n→ℝ | constrainedSquaredRadius v<σ},
      formFactorNumerator B rootB phi hphi (-d) t (fun i => ((shapeExtend v i:ℝ):ℂ))*
        cothHalf (fun u => poleEquation B phi hphi (-d) u (fun i => ((shapeExtend v i:ℝ):ℂ))) t)=
    ∫ v in {v : Fin n→ℝ | constrainedSquaredRadius v<σ},
      formFactorNumerator B rootB phi hphi d t (fun i => ((shapeExtend v i:ℝ):ℂ))*
        cothHalf (fun u => poleEquation B phi hphi d u (fun i => ((shapeExtend v i:ℝ):ℂ))) t := by
  let S : Set (Fin n→ℝ) := {v | constrainedSquaredRadius v<σ}
  have hS : MeasurableSet S := measurableSet_lt
    (constrainedSquaredRadius_contDiff (n := n) 0).continuous.measurable measurable_const
  let F : (Fin n→ℝ)→ℂ := fun v =>
    formFactorNumerator B rootB phi hphi (-d) t (fun i => ((shapeExtend v i:ℝ):ℂ))*
      cothHalf (fun u => poleEquation B phi hphi (-d) u (fun i => ((shapeExtend v i:ℝ):ℂ))) t
  have he (v : Fin n→ℝ) : F (-v)=
      formFactorNumerator B rootB phi hphi d t (fun i => ((shapeExtend v i:ℝ):ℂ))*
        cothHalf (fun u => poleEquation B phi hphi d u (fun i => ((shapeExtend v i:ℝ):ℂ))) t := by
    dsimp only [F]
    have hv : (fun i => ((shapeExtend (-v) i:ℝ):ℂ))= -(fun i => ((shapeExtend v i:ℝ):ℂ)) := by
      funext i
      simp only [shapeExtend_neg_fun,Pi.neg_apply,Complex.ofReal_neg]
    rw [hv,formFactorNumerator_neg_center]
    simp only [cothHalf,poleEquation_neg_center]
  have hind : (fun v => S.indicator F (-v))=S.indicator (fun v => F (-v)) := by
    funext v
    have hm : -v∈S ↔ v∈S := by simp only [S,mem_ofPred_eq,constrainedSquaredRadius_neg]
    by_cases hv : v∈S
    · simp only [indicator_of_mem hv,indicator_of_mem (hm.mpr hv)]
    · simp only [indicator_of_notMem hv,indicator_of_notMem (not_congr hm |>.mpr hv)]
  have hh := integral_neg_eq_self (μ := volume) (S.indicator F)
  rw [hind,integral_indicator hS,integral_indicator hS] at hh
  rw [←hh]
  apply setIntegral_congr_fun hS
  intro v _
  exact he v

end
end IsingBulk.Anisotropic.NegativeCycles
