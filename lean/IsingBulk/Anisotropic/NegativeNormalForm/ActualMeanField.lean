import IsingBulk.Anisotropic.NegativeNormalForm.ActualProjectedInverse
import IsingBulk.Anisotropic.NegativeNormalForm.MeanCorrectionAnalytic

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators

def inverseRootField {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (T : Config n → ℂ) (V : Config n → Config n) (w : Config n) : Config n :=
  fun i => Complex.sqrt (phaseEnergy B phi hphi d (T (V w)) (V w i))

def actualMeanField {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (T : Config n → ℂ) (V : Config n → Config n) (w : Config n) : Config n :=
  meanCoefficients (inverseRootField B phi hphi d T V w)

theorem inverseRootField_analyticAt {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hBn : B (1-Complex.cos d) ≠ 0) (hh : centralHessian B phi d ≠ 0)
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d)
    (V : Config n → Config n) (hV : AnalyticAt ℂ V 0) (hV0 : V 0=0) :
    AnalyticAt ℂ (inverseRootField B phi hphi d T V) 0 := by
  have hTV : AnalyticAt ℂ (fun w => T (V w)) 0 := hT.comp_of_eq hV hV0
  apply analyticAt_pi_iff.mpr
  intro i
  exact (phaseRootEnergy_analyticAt B phi hphi d hB hBn hh).comp_of_eq
    (hTV.prod (analyticAt_pi_iff.mp hV i)) (by simp [hV0,hT0])

theorem inverseRootField_zero {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hBn : B (1-Complex.cos d) ≠ 0) (hh : centralHessian B phi d ≠ 0)
    (T : Config n → ℂ) (hT0 : T 0=1-Complex.cos d)
    (V : Config n → Config n) (hV0 : V 0=0) : inverseRootField B phi hphi d T V 0=1 := by
  ext i
  simp [inverseRootField,hV0,hT0,phaseEnergy_center B phi hphi d hB hBn hh]

theorem actualMeanField_analyticAt {n : ℕ} (hn : n ≠ 0) (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hBn : B (1-Complex.cos d) ≠ 0) (hh : centralHessian B phi d ≠ 0)
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d)
    (V : Config n → Config n) (hV : AnalyticAt ℂ V 0) (hV0 : V 0=0) :
    AnalyticAt ℂ (actualMeanField B phi hphi d T V) 0 :=
  meanCoefficients_analyticAt hn _ (inverseRootField_analyticAt B phi hphi d hB hBn hh T hT hT0 V hV hV0)
    (inverseRootField_zero B phi hphi d hB hBn hh T hT0 V hV0)

/-- The field factors the genuine mean whenever the genuine projected inverse
identity holds. Both denominator conditions are derived in a neighborhood. -/
theorem actualMeanField_factorization_eventually {n : ℕ} (hn : n ≠ 0) (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hBn : B (1-Complex.cos d) ≠ 0) (hh : centralHessian B phi d ≠ 0)
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0=1-Complex.cos d)
    (V : Config n → Config n) (hV : AnalyticAt ℂ V 0) (hV0 : V 0=0) :
    ∀ᶠ w in 𝓝 (0:Config n), ZeroMean w → ZeroMean (V w) →
      project (phaseSeparableMap B phi hphi d (T (V w)) (V w))=w →
      pairing w (actualMeanField B phi hphi d T V w)=
        mean (phaseSeparableMap B phi hphi d (T (V w)) (V w)) := by
  let S := inverseRootField B phi hphi d T V
  have hS : AnalyticAt ℂ S 0 := inverseRootField_analyticAt B phi hphi d hB hBn hh T hT hT0 V hV hV0
  have hS0 : S 0=1 := inverseRootField_zero B phi hphi d hB hBn hh T hT0 V hV0
  have hInv (i : Fin n) : AnalyticAt ℂ (fun w => (S w i)⁻¹) 0 :=
    (analyticAt_pi_iff.mp hS i).inv (by change S 0 i ≠ 0; rw [hS0]; simp)
  have hden : AnalyticAt ℂ (fun w => ∑ i, (S w i)⁻¹) 0 :=
    Finset.analyticAt_fun_sum Finset.univ (fun i _ => hInv i)
  have hne : ∀ᶠ w in 𝓝 (0:Config n), ∀ i, S w i ≠ 0 := Filter.eventually_all.mpr (fun i =>
    (analyticAt_pi_iff.mp hS i).continuousAt.eventually_ne (by change S 0 i ≠ 0; rw [hS0]; simp))
  have hden0 : (∑ i, (S 0 i)⁻¹) ≠ 0 := by simp [hS0,hn]
  filter_upwards [hne,hden.continuousAt.eventually_ne hden0] with w hw hd
  intro hmean hm hproj
  exact meanCoefficients_factorization (V w) w (S w) hm hmean hw hd hproj

end
end IsingBulk.Anisotropic.NegativeNormalForm
