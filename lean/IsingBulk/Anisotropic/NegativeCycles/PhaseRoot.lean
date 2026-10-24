import IsingBulk.Anisotropic.NegativeNormalForm.Dispersion
import IsingBulk.Anisotropic.RegularEdges.PhasePrime
import IsingBulk.Anisotropic.NegativeDominance.NegativeNumeratorBridge

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Tail IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

theorem exp_neg_quadratic_of_cosh {g W : ℂ} (hg : Complex.cosh g=W) :
    Complex.exp (-g)^2-2*W*Complex.exp (-g)+1=0 := by
  have hm : Complex.exp g*Complex.exp (-g)=1 := by rw [←Complex.exp_add]; simp
  rw [Complex.cosh] at hg
  linear_combination 2*Complex.exp (-g)*hg-hm

/-- The actual inverse-cosh germ agrees with the continued lower quadratic root. -/
theorem continuedRoot_eq_exp_edgePhase_eventually {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0) :
    ∀ᶠ W in 𝓝 (Real.cos phi:ℂ),
      continuedRoot W=Complex.exp (-edgePhase phi hphi W) := by
  let b : ℂ := (Real.cos phi:ℂ)
  have hb : |Real.cos phi|<1 := by
    refine abs_lt.mpr ⟨?_,?_⟩
    · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi hp.le le_rfl hpi
    · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hpi.le hp
  have hD : b∈continuedRootDomain := Or.inr (by change |(Real.cos phi:ℂ).re|<1; simpa only [Complex.ofReal_re] using hb)
  have hr := (continuedRoot_analyticAt hD).continuousAt
  have he := (Complex.continuous_exp.continuousAt.comp
    ((edgePhase_spec phi hphi).1.continuousAt.neg))
  have he0 : Complex.exp (-edgePhase phi hphi b)=continuedRoot b := by
    rw [(edgePhase_spec phi hphi).2.1,continuedRoot_cos_formula hp hpi]
    congr 1
    ring
  have hgap : continuedRoot b+Complex.exp (-edgePhase phi hphi b)-2*b≠0 := by
    rw [he0]
    have hi : (continuedRoot b).im<0 := by
      rw [continuedRoot_compactRight_real (Real.cos phi) hb]
      exact (compactRight_real_norm_im (Real.cos phi) hb).2
    intro h
    have hh := congrArg Complex.im h
    simp [b] at hh
    simp only [b,Complex.ofReal_cos] at hi
    linarith
  have hg : ∀ᶠ W in 𝓝 b, continuedRoot W+Complex.exp (-edgePhase phi hphi W)-2*W≠0 :=
    ((hr.add he).sub (continuousAt_const.mul continuousAt_id)).eventually_ne hgap
  filter_upwards [hg,(edgePhase_spec phi hphi).2.2.1] with W hw hc
  have hq := exp_neg_quadratic_of_cosh hc
  have hmul : (continuedRoot W-Complex.exp (-edgePhase phi hphi W))*
      (continuedRoot W+Complex.exp (-edgePhase phi hphi W)-2*W)=0 := by
    linear_combination continuedRoot_quadratic W-hq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hw)


theorem continuedRoot_negativeDispersion_eq_exp_eventually (B : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0),
      continuedRoot (negativeDispersion B (Real.cos phi) p.1 p.2)=
        Complex.exp (-negativePhase B phi hphi p.1 p.2) := by
  have hw : AnalyticAt ℂ (fun p : ℂ × ℂ => negativeDispersion B (Real.cos phi) p.1 p.2) (0,0) := by
    unfold negativeDispersion
    exact analyticAt_const.add ((hB.comp_of_eq analyticAt_fst rfl).mul
      ((analyticAt_fst.sub analyticAt_const).add (Complex.analyticAt_cos.comp analyticAt_snd)))
  have ht : Tendsto (fun p : ℂ × ℂ => negativeDispersion B (Real.cos phi) p.1 p.2)
      (𝓝 (0,0)) (𝓝 (Real.cos phi:ℂ)) := by
    simpa only [ContinuousAt,negativeDispersion,Complex.cos_zero,zero_sub,neg_add_cancel,
      mul_zero,add_zero] using hw.continuousAt
  exact ht.eventually (continuedRoot_eq_exp_edgePhase_eventually hp hpi hphi)

theorem continuedTransferRoot_eq_negativeDispersion {lam phi : ℝ} (B : ℂ→ℂ)
    {z t : ℂ} (hB : B t=spectralT lam z/spectralS z)
    (he : edgeMapV lam (-1) z=(Real.cos phi:ℂ)+B t*t) (delta : ℂ) :
    NegativeDominance.continuedTransferRoot lam z ((Real.pi:ℂ)+delta)=
      continuedRoot (negativeDispersion B (Real.cos phi) t delta) := by
  unfold NegativeDominance.continuedTransferRoot
  congr 1
  unfold transferW
  rw [Complex.cos_add,Complex.cos_pi,Complex.sin_pi]
  unfold negativeDispersion
  rw [hB]
  rw [hB] at he
  unfold edgeMapV at he
  simp only [neg_mul,one_mul,sub_neg_eq_add] at he
  linear_combination he

end IsingBulk.Anisotropic.NegativeCycles
