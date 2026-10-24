import IsingBulk.Anisotropic.NegativeNormalForm.AnalyticSeparableMap
import IsingBulk.Anisotropic.NegativeNormalForm.MeanCoefficients
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedExtension

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators

theorem quadratic_analyticAt_along {n : ℕ} (ell : Config n → Config n) (hell : AnalyticAt ℂ ell 0) :
    AnalyticAt ℂ (fun w => quadratic (ell w)) 0 := by
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (analyticAt_pi_iff.mp hell i).pow 2

theorem pairing_analyticAt_along {n : ℕ} (ell : Config n → Config n) (hell : AnalyticAt ℂ ell 0) :
    AnalyticAt ℂ (fun w => pairing w (ell w)) 0 := by
  apply Finset.analyticAt_fun_sum
  intro i _
  exact ((ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt 0).mul
    (analyticAt_pi_iff.mp hell i)

theorem rankOneCoefficient_analyticAt_along {n : ℕ} (ell : Config n → Config n)
    (hell : AnalyticAt ℂ ell 0) (hell0 : ell 0=0) :
    AnalyticAt ℂ (fun w => rankOneCoefficient (ell w)) 0 := by
  have hq := quadratic_analyticAt_along ell hell
  have hs : AnalyticAt ℂ (fun w => Complex.sqrt (1+n*quadratic (ell w))) 0 :=
    sqrt_analyticAt_one.comp_of_eq (analyticAt_const.add (analyticAt_const.mul hq))
      (by simp [hell0,quadratic])
  exact analyticAt_const.div (analyticAt_const.add hs) (one_add_sqrt_ne_zero _)

theorem meanCorrection_analyticAt_along {n : ℕ} (ell : Config n → Config n)
    (hell : AnalyticAt ℂ ell 0) (hell0 : ell 0=0) :
    AnalyticAt ℂ (fun w => meanCorrection (ell w) w) 0 := by
  have ha := (rankOneCoefficient_analyticAt_along ell hell hell0).mul (pairing_analyticAt_along ell hell)
  apply analyticAt_pi_iff.mpr
  intro i
  exact ((ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt 0).add
    (ha.mul (analyticAt_pi_iff.mp hell i))

theorem meanCorrection_hasFDerivAt_along {n : ℕ} (ell : Config n → Config n)
    (hell : AnalyticAt ℂ ell 0) (hell0 : ell 0=0) :
    HasFDerivAt (fun w => meanCorrection (ell w) w) (ContinuousLinearMap.id ℂ (Config n)) 0 := by
  let a : Config n → ℂ := fun w => rankOneCoefficient (ell w)*pairing w (ell w)
  have ha : AnalyticAt ℂ a 0 := (rankOneCoefficient_analyticAt_along ell hell hell0).mul
    (pairing_analyticAt_along ell hell)
  have ha0 : a 0=0 := by simp [a,pairing]
  have hd := (hasFDerivAt_id (𝕜 := ℂ) (0:Config n)).add
    (ha.differentiableAt.hasFDerivAt.smul hell.differentiableAt.hasFDerivAt)
  convert! hd using 1
  ext w i
  simp [a,hell0,pairing]

theorem meanCorrection_zero_along {n : ℕ} (ell : Config n → Config n) :
    meanCorrection (ell 0) (0:Config n)=0 := by
  ext i
  simp [meanCorrection,pairing]

/-- A genuine analytic inverse of the constructed correction on the zero-mean
hyperplane. The input is the coefficient field, not a presumed normal form. -/
theorem exists_meanCorrection_inverse {n : ℕ} (hn : n ≠ 0) (ell : Config n → Config n)
    (hell : AnalyticAt ℂ ell 0) (hell0 : ell 0=0) (hmean : ∀ w, ZeroMean (ell w)) :
    ∃ W : Config n → Config n, AnalyticAt ℂ W 0 ∧ W 0=0 ∧
      HasFDerivAt W (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ᶠ y in 𝓝 (0:Config n), ZeroMean y →
        ZeroMean (W y) ∧ meanCorrection (ell (W y)) (W y)=y) := by
  obtain ⟨W,hW,hW0,hdW,_hl,hr⟩ := exists_projected_inverse hn (fun w => meanCorrection (ell w) w)
    (meanCorrection_analyticAt_along ell hell hell0) (meanCorrection_zero_along ell)
    (meanCorrection_hasFDerivAt_along ell hell hell0)
  refine ⟨W,hW,hW0,hdW,?_⟩
  filter_upwards [hr] with y hy
  intro hmy
  obtain ⟨hm,hp⟩ := hy.2 hmy
  refine ⟨hm,?_⟩
  rw [project_eq_self (meanCorrection_zeroMean (ell (W y)) (W y) (hmean (W y)) hm)] at hp
  exact hp

end
end IsingBulk.Anisotropic.NegativeNormalForm
