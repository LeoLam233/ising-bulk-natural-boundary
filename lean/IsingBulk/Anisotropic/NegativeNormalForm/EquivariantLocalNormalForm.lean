import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantProjectedInverse
import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantMeanCorrection

/-! A genuinely constructed local pole normal form from the actual phase.
All operations are analytic through coincidences and the complex null cone.
Uniform radii, density bounds, and cycle comparison are separate obligations. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

theorem exists_equivariant_actual_local_normal_form {n : ℕ} (hn : n ≠ 0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hh : centralHessian B phi d ≠ 0) :
    ∃ T : Config n → ℂ, ∃ Phi : Config n → Config n,
      AnalyticAt ℂ T 0 ∧ T 0=1-Complex.cos d ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, T (permute e v)=T v) ∧
      AnalyticAt ℂ Phi 0 ∧ Phi 0=0 ∧
      HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, Phi (permute e v)=permute e (Phi v)) ∧
      (∀ᶠ y in 𝓝 (0:Config n), ZeroMean y →
        ZeroMean (Phi y) ∧ poleEquation B phi hphi d (T (Phi y)) (Phi y)=0 ∧
        T (Phi y)=1-Complex.cos d+centralHessian B phi d/(2*n)*quadratic y) := by
  obtain ⟨T,V,hT,hT0,hsym,hV,hV0,hdV,hsymV,hactual⟩ := exists_equivariant_actual_projected_inverse hn B phi hphi d hB hBn hh
  let ell := actualMeanField B phi hphi d T V
  have hell : AnalyticAt ℂ ell 0 := actualMeanField_analyticAt hn B phi hphi d hB hBn hh T hT hT0 V hV hV0
  have hell0 : ell 0=0 := by
    rw [show ell 0=meanCoefficients (inverseRootField B phi hphi d T V 0) from rfl,
      inverseRootField_zero B phi hphi d hB hBn hh T hT0 V hV0,meanCoefficients_one]
  have hmean (w : Config n) : ZeroMean (ell w) := meanCoefficients_zeroMean hn _
  have hsymEll := actualMeanField_permute B phi hphi d T V hsym hsymV
  obtain ⟨W,hW,hW0,hdW,hsymW,hWinv⟩ := exists_equivariant_meanCorrection_inverse hn ell hell hell0 hmean hsymEll
  have hmu := actualMeanField_factorization_eventually hn B phi hphi d hB hBn hh T hT hT0 V hV hV0
  have hstep : ∀ᶠ w in 𝓝 (0:Config n), ZeroMean w → ZeroMean (V w) ∧
      poleEquation B phi hphi d (T (V w)) (V w)=0 ∧
      T (V w)-(1-Complex.cos d)=centralHessian B phi d/(2*n)*quadratic (meanCorrection (ell w) w) := by
    filter_upwards [hactual,hmu] with w hw hmw
    intro hm
    obtain ⟨hv,hproj,hpole,he⟩ := hw hm
    have hp := hmw hm hv hproj
    have hq := quadratic_meanCorrection (ell w) w
    rw [hp] at hq
    exact ⟨hv,hpole,he.trans (congrArg (fun z => centralHessian B phi d/(2*n)*z) hq.symm)⟩
  let Phi : Config n → Config n := fun y => V (W y)
  have hPhi : AnalyticAt ℂ Phi 0 := hV.comp_of_eq hW hW0
  have hPhi0 : Phi 0=0 := by simp [Phi,hW0,hV0]
  have hdV' : HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) (W 0) := by simpa only [hW0] using hdV
  have hdPhi : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config n)) 0 := by
    convert! hdV'.comp 0 hdW using 1
  have htW : Filter.Tendsto W (𝓝 0) (𝓝 0) := by simpa only [hW0] using hW.continuousAt.tendsto
  have hsymPhi (e : Equiv.Perm (Fin n)) (v : Config n) : Phi (permute e v)=permute e (Phi v) := by
    dsimp only [Phi]
    rw [hsymW e v,hsymV e (W v)]
  refine ⟨T,Phi,hT,hT0,hsym,hPhi,hPhi0,hdPhi,hsymPhi,?_⟩
  filter_upwards [hWinv,htW.eventually hstep] with y hy hs
  intro hmy
  obtain ⟨hmW,hcorr⟩ := hy hmy
  obtain ⟨hmV,hpole,he⟩ := hs hmW
  rw [hcorr] at he
  refine ⟨hmV,hpole,?_⟩
  change T (V (W y))=1-Complex.cos d+centralHessian B phi d/(2*n)*quadratic y
  linear_combination he

end
end IsingBulk.Anisotropic.NegativeNormalForm
