import IsingBulk.Anisotropic.NegativeNormalForm.DensityFactors
import IsingBulk.Anisotropic.NegativeNormalForm.Homotopy
import Mathlib.MeasureTheory.Group.Integral

/-! Exact reflection between the two nearest winding charts. No assertion
about a common phase across different particle indices is made. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators
open MeasureTheory IsingBulk.First

theorem negativePhase_reflect (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d t x : ℂ) :
    negativePhase B phi hphi t (-d+x) = negativePhase B phi hphi t (d-x) := by
  have h : -d+x = -(d-x) := by ring
  rw [h, negativePhase_even]

theorem poleEquation_reflect {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) :
    poleEquation B phi hphi (-d) t v = poleEquation B phi hphi d t (-v) := by
  simp only [poleEquation, Pi.neg_apply, ← sub_eq_add_neg, negativePhase_reflect]

theorem formFactorNumerator_reflect {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) :
    formFactorNumerator B rootB phi hphi (-d) t v =
      formFactorNumerator B rootB phi hphi d t (-v) := by
  unfold formFactorNumerator pairDenominator
  simp only [Pi.neg_apply, ← sub_eq_add_neg, negativePhase_reflect]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  have he : (-v p.1 - -v p.2)/2 = -((v p.1-v p.2)/2) := by ring
  rw [he, Complex.sin_neg, neg_div, neg_sq]

def reflectedPole {n : ℕ} (T : Config n → ℂ) (v : Config n) : ℂ := T (-v)

theorem poleResidue_reflect {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config n → ℂ) (v : Config n) :
    poleResidue B rootB phi hphi (-d) (reflectedPole T) v =
      poleResidue B rootB phi hphi d T (-v) := by
  simp only [poleResidue, reflectedPole, formFactorNumerator_reflect, poleParameterDerivative,
    poleEquation_reflect]

/-- The literal independent real coordinates, with the last component fixed by momentum. -/
def freeConfiguration (m : ℕ) (u : Fin m → ℝ) : Config (m+1) :=
  Fin.lastCases (-∑ i, (u i : ℂ)) (fun i => (u i : ℂ))

theorem freeConfiguration_zeroMean (m : ℕ) (u : Fin m → ℝ) : ZeroMean (freeConfiguration m u) := by
  simp [ZeroMean, freeConfiguration, Fin.sum_univ_castSucc]

@[simp] theorem freeConfiguration_neg (m : ℕ) (u : Fin m → ℝ) :
    freeConfiguration m (-u) = -freeConfiguration m u := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [freeConfiguration]

/-- Actual residue coefficient integrated over the same real q-ball in either winding chart. -/
def windingCoefficient (m j : ℕ) (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ) (r : ℝ) : ℂ :=
  ∫ u : Fin m → ℝ, if absoluteEnergy (freeConfiguration m u) < r^2 then
    poleResidue B rootB phi hphi d T (freeConfiguration m u) / T (freeConfiguration m u)^(j+1)
    else 0

/-- Both nearest windings agree exactly by reflection of their genuine residue integrals. -/
theorem windingCoefficient_reflect (m j : ℕ) (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ) (r : ℝ) :
    windingCoefficient m j B rootB phi hphi (-d) (reflectedPole T) r =
      windingCoefficient m j B rootB phi hphi d T r := by
  unfold windingCoefficient
  simp only [poleResidue_reflect, reflectedPole]
  convert integral_neg_eq_self (fun u : Fin m → ℝ =>
      if absoluteEnergy (freeConfiguration m u) < r^2 then
        poleResidue B rootB phi hphi d T (freeConfiguration m u) /
          T (freeConfiguration m u)^(j+1) else 0) volume using 1
  congr 1
  ext u
  simp [absoluteEnergy]
  rfl

end
end IsingBulk.Anisotropic.NegativeNormalForm
