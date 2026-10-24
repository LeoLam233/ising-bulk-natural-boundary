import IsingBulk.Anisotropic.RegularEdges.ComplexAngular
import IsingBulk.Anisotropic.RegularEdges.AngularFullCoefficient

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open FormFactors IsingBulk.First IsingBulk.HT.Contour
open scoped BigOperators

theorem transferW_real (lam x q : ℝ) :
    transferW lam (x:ℂ) (q:ℂ) = (realC lam x-realB lam x*Real.cos q:ℝ) := by
  unfold transferW spectralA spectralS spectralT realC realB
  push_cast
  ring

theorem transferRoot_real {lam x : ℝ} (hlam : 0<lam) (hx : 0<x)
    (hp : realProduct lam x≠1) (q : ℝ) :
    transferRoot lam (x:ℂ) (q:ℂ) = (root (realB lam x) (realC lam x) q:ℝ) := by
  have hB := (realB_pos hlam hx).le
  have hgap := real_dispersion_gap hlam hx hp
  have hr := root_bounds hB hgap q
  unfold transferRoot
  rw [transferW_real]
  apply smallRoot_eq_of_quadratic
  · exact Or.inr (Or.inl (by simpa only [← Complex.ofReal_cos,Complex.ofReal_sub,Complex.ofReal_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using dispersion_gt_one hB hgap q))
  · have he := root_trace hB hgap q
    have hn := hr.1.ne'
    field_simp [hn] at he
    have hh : (root (realB lam x) (realC lam x) q)^2 -
        2*(realC lam x-realB lam x*Real.cos q)*root (realB lam x) (realC lam x) q+1=0 := by
      nlinarith
    exact_mod_cast hh
  · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr.1] using hr.2

theorem angularRootPair_real {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) (a b : ℝ) :
    angularRootPair (root B C a:ℝ) (root B C b:ℝ) (a:ℂ) (b:ℂ) =
      ((Real.sin ((a-b)/2)/Real.sinh ((gamma B C a+gamma B C b)/2))^2:ℝ) := by
  have hh := physical_pair_root_ratio (gamma_pos hB hgap a) (gamma_pos hB hgap b)
  have he : 4*root B C a*root B C b*(Real.sin ((a-b)/2))^2 /
      (1-root B C a*root B C b)^2 =
      (Real.sin ((a-b)/2)/Real.sinh ((gamma B C a+gamma B C b)/2))^2 := by
    calc
      _ = 4*(Real.sin ((a-b)/2))^2 *
          (root B C a*root B C b/(1-root B C a*root B C b)^2) := by ring
      _ = _ := by change _ = _ at hh; simp only [root] at ⊢; rw [hh]; simp only [div_eq_mul_inv,mul_inv_rev]; norm_num; ring
  unfold angularRootPair
  exact_mod_cast he

theorem angularOneBody_real {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) (q : ℝ) :
    2*(root B C q:ℂ)/(1-(root B C q:ℂ)^2) = ((Real.sinh (gamma B C q))⁻¹:ℝ) := by
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (root_bounds hB hgap q).1.ne')
  calc
    _ = residueFactor (root B C q:ℂ) := by unfold residueFactor; ring
    _ = _ := by rw [residue_factor hB hgap]; push_cast; rfl

theorem scaled_complexAngularWeight_real {N : ℕ} {lam x : ℝ}
    (hlam : 0<lam) (hx : 0<x) (hp : realProduct lam x≠1) (q : Fin N → ℝ) :
    ((Real.sqrt (realProduct lam x))^N:ℝ)*
      complexAngularWeight lam (x:ℂ) (fun i => (q i:ℂ)) =
      (angularWeight (realB lam x) (realC lam x) q:ℝ) := by
  have hB := realB_pos hlam hx
  have hgap := real_dispersion_gap hlam hx hp
  have hS : Real.sinh x≠0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hratio : spectralT lam (x:ℂ)/spectralS (x:ℂ) = (realB lam x:ℝ) := by
    simp only [spectralT,spectralS,realB,Complex.ofReal_div,Complex.ofReal_sinh,Complex.ofReal_mul]
  have hscale := temperatureScale_pair_power N hB hS
  rw [physical_temperatureScale hlam hx] at hscale
  have hc : (((Real.sqrt (realProduct lam x))^N:ℝ):ℂ)*(realB lam x:ℂ)^(N.choose 2)*
      ((Real.sinh x:ℂ)^N)⁻¹ = (anisotropyPower N (realB lam x):ℝ) := by exact_mod_cast hscale
  unfold complexAngularWeight angularWeight FormFactors.pairProduct
  simp_rw [transferRoot_real hlam hx hp, angularOneBody_real hB.le hgap,
    angularRootPair_real hB.le hgap]
  rw [hratio]
  simp only [spectralS,← Complex.ofReal_sinh,inv_pow]
  push_cast
  have hm := congrArg (fun a : ℂ => a *
    (∏ i, (((Real.sinh (gamma (realB lam x) (realC lam x) (q i)))⁻¹:ℝ):ℂ)) *
    (FormFactors.pairProduct (realB lam x) (realC lam x) q:ℝ)) hc
  unfold FormFactors.pairProduct at hm
  push_cast at hm
  simpa only [inv_pow,mul_assoc] using hm

end
end IsingBulk.Anisotropic.RegularEdges
