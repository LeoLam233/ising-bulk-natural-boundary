import IsingBulk.Anisotropic.NegativeNormalForm.Homotopy
import IsingBulk.Anisotropic.NegativeNormalForm.MeanUniformBounds

/-! Sharp Hermitian-energy estimates for the mean-zero projection. -/
noncomputable section
open scoped BigOperators
namespace IsingBulk.Anisotropic.NegativeNormalForm

 theorem complex_norm_sub_sq (z c : ℂ) :
    ‖z-c‖^2=‖z‖^2-2*(z.re*c.re+z.im*c.im)+‖c‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

 theorem absoluteEnergy_sub_constant {n : ℕ} (v : Config n) (c : ℂ) :
    absoluteEnergy (fun i => v i-c)=absoluteEnergy v-
      2*((∑ i, v i).re*c.re+(∑ i, v i).im*c.im)+(n:ℝ)*‖c‖^2 := by
  simp only [absoluteEnergy,complex_norm_sub_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_mul,
    Complex.re_sum,Complex.im_sum]
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]

 theorem sum_eq_card_mul_mean {n : ℕ} (hn : n ≠ 0) (v : Config n) :
    (∑ i, v i)=(n:ℂ)*mean v := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  unfold mean
  field_simp

 theorem absoluteEnergy_project {n : ℕ} (hn : n ≠ 0) (v : Config n) :
    absoluteEnergy (project v)=absoluteEnergy v-(n:ℝ)*‖mean v‖^2 := by
  change absoluteEnergy (fun i => v i-mean v)=_
  rw [absoluteEnergy_sub_constant,sum_eq_card_mul_mean hn]
  simp only [Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero,add_zero,Complex.sq_norm,Complex.normSq_apply]
  ring

 theorem absoluteEnergy_project_le {n : ℕ} (hn : n ≠ 0) (v : Config n) :
    absoluteEnergy (project v)≤absoluteEnergy v := by
  rw [absoluteEnergy_project hn]
  exact sub_le_self _ (by positivity)

 theorem absoluteEnergy_div {n : ℕ} (v : Config n) (z : ℂ) :
    absoluteEnergy (fun i => v i/z)=absoluteEnergy v/‖z‖^2 := by
  simp [absoluteEnergy,div_pow,Finset.sum_div]

 theorem project_sub_constant {n : ℕ} (hn : n ≠ 0) (v : Config n) (c : ℂ) :
    project (fun i => v i-c)=project v := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  ext i
  simp only [project,mean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,sub_div,mul_div_cancel_left₀ c hn']
  ring

 theorem meanCoefficients_shift {n : ℕ} (hn : n ≠ 0) (S : Config n) (a : ℂ) :
    meanCoefficients S=project (fun i => (a-(S i)⁻¹)/(∑ j, (S j)⁻¹)) := by
  have he : (fun i => (a-(S i)⁻¹)/(∑ j, (S j)⁻¹))=
      fun i => (1-(S i)⁻¹)/(∑ j, (S j)⁻¹)-(1-a)/(∑ j, (S j)⁻¹) := by
    ext i
    ring
  rw [he,project_sub_constant hn]
  rfl

 theorem meanCoefficients_energy_le {n : ℕ} (hn : n ≠ 0) (S : Config n) (a : ℂ) :
    absoluteEnergy (meanCoefficients S)≤
      absoluteEnergy (fun i => a-(S i)⁻¹)/‖∑ j, (S j)⁻¹‖^2 := by
  rw [meanCoefficients_shift hn S a]
  exact (absoluteEnergy_project_le hn _).trans_eq (absoluteEnergy_div _ _)

end IsingBulk.Anisotropic.NegativeNormalForm
