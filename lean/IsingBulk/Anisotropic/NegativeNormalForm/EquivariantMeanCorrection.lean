import IsingBulk.Anisotropic.NegativeNormalForm.ActualMeanField
import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantInverse

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators

theorem meanCoefficients_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (S : Config n) :
    meanCoefficients (permute e S)=permute e (meanCoefficients S) := by
  have hs : (∑ j, ((permute e S) j)⁻¹)=∑ j, (S j)⁻¹ :=
    Equiv.sum_comp e (fun j => (S j)⁻¹)
  unfold meanCoefficients
  rw [hs]
  exact project_permute e (fun i => (1-(S i)⁻¹)/(∑ j, (S j)⁻¹))

theorem inverseRootField_permute {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (T : Config n → ℂ) (V : Config n → Config n)
    (hT : ∀ e : Equiv.Perm (Fin n), ∀ v, T (permute e v)=T v)
    (hV : ∀ e : Equiv.Perm (Fin n), ∀ v, V (permute e v)=permute e (V v))
    (e : Equiv.Perm (Fin n)) (w : Config n) :
    inverseRootField B phi hphi d T V (permute e w)=permute e (inverseRootField B phi hphi d T V w) := by
  ext i
  change Complex.sqrt (phaseEnergy B phi hphi d (T (V (permute e w))) (V (permute e w) i)) = _
  rw [hV e w,hT e (V w)]
  rfl

theorem actualMeanField_permute {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (T : Config n → ℂ) (V : Config n → Config n)
    (hT : ∀ e : Equiv.Perm (Fin n), ∀ v, T (permute e v)=T v)
    (hV : ∀ e : Equiv.Perm (Fin n), ∀ v, V (permute e v)=permute e (V v))
    (e : Equiv.Perm (Fin n)) (w : Config n) :
    actualMeanField B phi hphi d T V (permute e w)=permute e (actualMeanField B phi hphi d T V w) := by
  unfold actualMeanField
  rw [inverseRootField_permute B phi hphi d T V hT hV,meanCoefficients_permute]

theorem exists_equivariant_meanCorrection_inverse {n : ℕ} (hn : n ≠ 0) (ell : Config n → Config n)
    (hell : AnalyticAt ℂ ell 0) (hell0 : ell 0=0) (hmean : ∀ w, ZeroMean (ell w))
    (hsym : ∀ e : Equiv.Perm (Fin n), ∀ w, ell (permute e w)=permute e (ell w)) :
    ∃ W : Config n → Config n, AnalyticAt ℂ W 0 ∧ W 0=0 ∧
      HasFDerivAt W (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, W (permute e v)=permute e (W v)) ∧
      (∀ᶠ y in 𝓝 (0:Config n), ZeroMean y →
        ZeroMean (W y) ∧ meanCorrection (ell (W y)) (W y)=y) := by
  have hsymK (e : Equiv.Perm (Fin n)) (w : Config n) :
      meanCorrection (ell (permute e w)) (permute e w)=permute e (meanCorrection (ell w) w) := by
    rw [hsym e w,meanCorrection_permute]
  obtain ⟨W,hW,hW0,hdW,hsymW,hr⟩ := exists_equivariant_projected_inverse hn (fun w => meanCorrection (ell w) w)
    (meanCorrection_analyticAt_along ell hell hell0) (meanCorrection_zero_along ell)
    (meanCorrection_hasFDerivAt_along ell hell hell0) hsymK
  refine ⟨W,hW,hW0,hdW,hsymW,?_⟩
  filter_upwards [hr] with y hy
  intro hmy
  obtain ⟨hm,hp⟩ := hy.2 hmy
  refine ⟨hm,?_⟩
  rw [project_eq_self (meanCorrection_zeroMean (ell (W y)) (W y) (hmean (W y)) hm)] at hp
  exact hp

end
end IsingBulk.Anisotropic.NegativeNormalForm
