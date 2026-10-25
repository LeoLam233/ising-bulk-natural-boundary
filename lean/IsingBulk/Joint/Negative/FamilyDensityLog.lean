import IsingBulk.Joint.Negative.FamilyDensityScalar
import IsingBulk.Anisotropic.NegativeNormalForm.PairLogarithm
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Literal analytic logarithms for the scalar prefactors on a common complex-family disk. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The same principal logarithm works jointly in both moving scalar parameters
and in the independent complex family parameter. No pointwise branch choices. -/
theorem compact_family_parameter_log_control (f : ℂ × E → ℂ) {K : Set E}
    (hK : IsCompact K) (hf : ∀ eta ∈ K, AnalyticAt ℂ f (0,eta))
    (hf0 : ∀ eta ∈ K, f (0,eta) ≠ 0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ t t₀ : ℂ, ‖t‖<r → ‖t₀‖<r →
      AnalyticAt ℂ (fun q : (ℂ × ℂ) × E => Complex.log (f (q.1.1,q.2)/f (q.1.2,q.2))) ((t,t₀),eta) ∧
      Complex.exp (Complex.log (f (t,eta)/f (t₀,eta)))=f (t,eta)/f (t₀,eta) ∧
      ‖Complex.log (f (t,eta)/f (t₀,eta))‖≤L*‖t-t₀‖ := by
  obtain ⟨a,M,ha,hM,hcontrol⟩ := compact_family_parameter_ratio_control f hK hf hf0
  obtain ⟨b,hb,hlocal⟩ := compact_family_parameter_nonzero f hK hf hf0
  let r := min a (min b (1/(8*M)))
  have hr : 0<r := by dsimp [r]; positivity
  have hra : r≤a := min_le_left _ _
  have hrb : r≤b := (min_le_right _ _).trans (min_le_left _ _)
  have hrM : M*r≤1/8 := by
    have hh : r≤1/(8*M) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0<8*M)).mp hh
    nlinarith
  refine ⟨r,2*M,hr,by positivity,?_⟩
  intro eta heta t t₀ ht ht₀
  have hft := hlocal eta heta t (ht.trans_le hrb)
  have hft₀ := hlocal eta heta t₀ (ht₀.trans_le hrb)
  have he := (hcontrol eta heta t t₀ (ht.trans_le hra) (ht₀.trans_le hra)).2
  have hsmall : ‖f (t,eta)/f (t₀,eta)-1‖≤1/2 := by
    have hdist : ‖t-t₀‖≤2*r := (norm_sub_le t t₀).trans (by linarith)
    have hh := he.trans (mul_le_mul_of_nonneg_left hdist hM.le)
    nlinarith
  have hslit : f (t,eta)/f (t₀,eta)∈Complex.slitPlane := by
    simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one
      (hsmall.trans_lt (by norm_num : (1:ℝ)/2<1))
  have hratio : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E => f (q.1.1,q.2)/f (q.1.2,q.2)) ((t,t₀),eta) := by
    apply AnalyticAt.div
    · exact hft.1.comp (f:=fun q : (ℂ × ℂ) × E => (q.1.1,q.2))
        ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
    · exact hft₀.1.comp (f:=fun q : (ℂ × ℂ) × E => (q.1.2,q.2))
        ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)
    · exact hft₀.2
  refine ⟨hratio.clog hslit,Complex.exp_log (div_ne_zero hft.2 hft₀.2),?_⟩
  exact (norm_log_near_one _ hsmall).trans ((mul_le_mul_of_nonneg_left he (by norm_num)).trans_eq (by ring))

end
end IsingBulk.Joint.Negative
