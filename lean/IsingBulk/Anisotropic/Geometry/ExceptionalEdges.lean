import IsingBulk.Anisotropic.Geometry.LocallyFinite
import IsingBulk.Anisotropic.Geometry.PhysicalAxis

namespace IsingBulk.Anisotropic
noncomputable section

def spectralADeriv (lam : ℝ) (z : ℂ) : ℂ :=
  Complex.sinh z*Complex.cosh ((lam:ℂ)*z)+Complex.cosh z*((lam:ℂ)*Complex.sinh ((lam:ℂ)*z))

def edgeMapU (lam : ℝ) (e z : ℂ) : ℂ := (spectralA lam z-e*spectralS z)/spectralT lam z
def edgeMapV (lam : ℝ) (e z : ℂ) : ℂ := (spectralA lam z-e*spectralT lam z)/spectralS z

def edgeNumeratorU (lam : ℝ) (e z : ℂ) : ℂ :=
  (spectralADeriv lam z-e*Complex.cosh z)*spectralT lam z-
    (spectralA lam z-e*spectralS z)*((lam:ℂ)*Complex.cosh ((lam:ℂ)*z))

def edgeNumeratorV (lam : ℝ) (e z : ℂ) : ℂ :=
  (spectralADeriv lam z-e*((lam:ℂ)*Complex.cosh ((lam:ℂ)*z)))*spectralS z-
    (spectralA lam z-e*spectralT lam z)*Complex.cosh z

theorem spectralT_hasDerivAt (lam : ℝ) (z : ℂ) :
    HasDerivAt (spectralT lam) ((lam:ℂ)*Complex.cosh ((lam:ℂ)*z)) z := by
  have h : HasDerivAt (spectralT lam) (Complex.cosh ((lam:ℂ)*z)*((lam:ℂ)*1)) z :=
    (Complex.hasDerivAt_sinh ((lam:ℂ)*z)).comp z ((hasDerivAt_id z).const_mul (lam:ℂ))
  convert h using 1
  ring

theorem spectralA_hasDerivAt (lam : ℝ) (z : ℂ) : HasDerivAt (spectralA lam) (spectralADeriv lam z) z := by
  have h : HasDerivAt (spectralA lam)
      (Complex.sinh z*Complex.cosh ((lam:ℂ)*z)+Complex.cosh z*(Complex.sinh ((lam:ℂ)*z)*((lam:ℂ)*1))) z :=
    (Complex.hasDerivAt_cosh z).mul ((Complex.hasDerivAt_cosh ((lam:ℂ)*z)).comp z
      ((hasDerivAt_id z).const_mul (lam:ℂ)))
  convert h using 1
  unfold spectralADeriv
  ring

theorem edgeMapU_hasDerivAt (lam : ℝ) (e z : ℂ) (ht : spectralT lam z≠0) :
    HasDerivAt (edgeMapU lam e) (edgeNumeratorU lam e z/(spectralT lam z)^2) z :=
  ((spectralA_hasDerivAt lam z).sub ((Complex.hasDerivAt_sinh z).const_mul e)).div
    (spectralT_hasDerivAt lam z) ht

theorem edgeMapV_hasDerivAt (lam : ℝ) (e z : ℂ) (hs : spectralS z≠0) :
    HasDerivAt (edgeMapV lam e) (edgeNumeratorV lam e z/(spectralS z)^2) z :=
  ((spectralA_hasDerivAt lam z).sub ((spectralT_hasDerivAt lam z).const_mul e)).div
    (Complex.hasDerivAt_sinh z) hs

theorem edgeNumeratorU_analyticAt (lam : ℝ) (e z : ℂ) : AnalyticAt ℂ (edgeNumeratorU lam e) z := by
  unfold edgeNumeratorU spectralADeriv spectralA spectralS spectralT
  fun_prop

theorem edgeNumeratorV_analyticAt (lam : ℝ) (e z : ℂ) : AnalyticAt ℂ (edgeNumeratorV lam e) z := by
  unfold edgeNumeratorV spectralADeriv spectralA spectralS spectralT
  fun_prop

@[simp] theorem edgeNumeratorU_zero (lam : ℝ) (e : ℂ) : edgeNumeratorU lam e 0= -(lam:ℂ) := by
  simp [edgeNumeratorU,spectralADeriv,spectralA,spectralS,spectralT]

@[simp] theorem edgeNumeratorV_zero (lam : ℝ) (e : ℂ) : edgeNumeratorV lam e 0= -1 := by
  simp [edgeNumeratorV,spectralADeriv,spectralA,spectralS,spectralT]

def edgeExceptionalSet (lam : ℝ) : Set ℂ :=
  {z | z∈spectralSet lam ∧ spectralDet lam z=0} ∪
  {z | spectralS z=0} ∪ {z | spectralT lam z=0} ∪ {z | spectralProduct lam z^2=1} ∪
  {z | edgeNumeratorU lam 1 z=0} ∪ {z | edgeNumeratorU lam (-1) z=0} ∪
  {z | edgeNumeratorV lam 1 z=0} ∪ {z | edgeNumeratorV lam (-1) z=0}

/-- The entire exceptional set of poles, corners, collinearity, and edge critical points is locally finite. -/
theorem edgeExceptionalSet_locally_finite {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) :
    LocallyFiniteSubset (edgeExceptionalSet lam) := by
  have hS : LocallyFiniteSubset {z | spectralS z=0} :=
    analytic_zeros_locally_finite (fun _ => Complex.analyticAt_sinh)
      ⟨1,sinh_ne_zero_of_re_pos (by norm_num)⟩
  have hT : LocallyFiniteSubset {z | spectralT lam z=0} := by
    apply analytic_zeros_locally_finite
    · intro z
      unfold spectralT
      fun_prop
    · refine ⟨1,sinh_ne_zero_of_re_pos ?_⟩
      simpa using hlam
  have hp : LocallyFiniteSubset {z | spectralProduct lam z^2=1} := by
    have he : {z | spectralProduct lam z^2=1}={z | spectralProduct lam z^2-1=0} := by
      ext z
      exact sub_eq_zero.symm
    rw [he]
    apply analytic_zeros_locally_finite
    · intro z
      unfold spectralProduct spectralS spectralT
      fun_prop
    · exact ⟨0,by simp [spectralProduct,spectralS,spectralT]⟩
  have hU (e : ℂ) : LocallyFiniteSubset {z | edgeNumeratorU lam e z=0} :=
    analytic_zeros_locally_finite (edgeNumeratorU_analyticAt lam e)
      ⟨0,by simpa using (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hlam.ne'))⟩
  have hV (e : ℂ) : LocallyFiniteSubset {z | edgeNumeratorV lam e z=0} :=
    analytic_zeros_locally_finite (edgeNumeratorV_analyticAt lam e) ⟨0,by simp⟩
  exact (((((((collinear_spectral_locally_finite hlam hne).union hS).union hT).union hp).union
    (hU 1)).union (hU (-1))).union (hV 1)).union (hV (-1))

end
end IsingBulk.Anisotropic
