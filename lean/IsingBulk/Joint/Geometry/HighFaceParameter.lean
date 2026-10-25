import IsingBulk.Joint.Geometry.FaceRatios
import IsingBulk.Joint.Geometry.Collars

namespace IsingBulk.Joint
noncomputable section
open Set

/-- Continuous parametrization of one entire high-temperature rectangular face. -/
def highFaceParameter (sgn : ℝ) (q : (ℝ × ℝ) × ℝ) : Coupling :=
  ((q.1.1 : ℂ) + (sgn*Real.arccos (faceRatio1 q.1) : ℝ)*Complex.I,
   (q.1.2 : ℂ) + (q.2*Real.arccos (faceRatio2 q.1) : ℝ)*Complex.I)

@[fun_prop] theorem highFaceParameter_continuous (sgn : ℝ) : Continuous (highFaceParameter sgn) := by
  unfold highFaceParameter
  fun_prop

theorem highFaceParameter_coordinates (sgn : ℝ) (q : (ℝ × ℝ) × ℝ) :
    (highFaceParameter sgn q).1.re = q.1.1 ∧
    (highFaceParameter sgn q).2.re = q.1.2 ∧
    (highFaceParameter sgn q).1.im = sgn*Real.arccos (faceRatio1 q.1) ∧
    (highFaceParameter sgn q).2.im = q.2*Real.arccos (faceRatio2 q.1) := by
  simp [highFaceParameter]

theorem cos_sign_mul (sgn a : ℝ) (hs : sgn = -1 ∨ sgn = 1) :
    Real.cos (sgn*a) = Real.cos a := by rcases hs with h | h <;> simp [h]

theorem highFaceParameter_frontier {sgn : ℝ} (hs : sgn = -1 ∨ sgn = 1)
    {v : ℝ × ℝ} (hv : v ∈ regularRealSubcritical) {a : ℝ} (ha : |a| < 1) :
    highFaceParameter sgn (v,a) ∈ frontier highDomain := by
  have hr₁ := faceRatio1_pos hv.2.2
  have hr₂ := faceRatio2_pos hv.2.1
  have h₁ := (faceRatio1_lt_one_iff v).mpr hv.1
  have h₂ := (faceRatio2_lt_one_iff v).mpr hv.1
  have hsabs : |sgn| = 1 := by rcases hs with h | h <;> simp [h]
  have hcos : Real.cos (sgn * Real.arccos (faceRatio1 v)) = faceRatio1 v := by
    rw [cos_sign_mul _ _ hs,Real.cos_arccos (by linarith) h₁.le]
  have hy : |sgn * Real.arccos (faceRatio1 v)| < Real.pi/2 := by
    rw [abs_mul,hsabs,one_mul,abs_of_nonneg (Real.arccos_nonneg _)]
    exact Real.arccos_lt_pi_div_two.mpr hr₁
  have hvc := cosine_scaled_arccos_gt hr₂.le h₂ ha
  have hvi := scaled_arccos_strip hr₂.le h₂ ha
  rw [highDomain_isOpen.frontier_eq]
  refine ⟨?_,?_⟩
  · apply closure_high_of_nonstrict
    · simpa [highFaceParameter] using hy.le
    · simpa [highFaceParameter] using hvi.le
    · simp only [highFaceParameter,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,add_zero,
        Complex.add_im,Complex.mul_im,zero_add,mul_one]
      change faceRatio1 v ≤ Real.cos (sgn*Real.arccos (faceRatio1 v))
      rw [hcos]
    · simpa [highFaceParameter,faceRatio2] using hvc.le
  · intro hm
    have he := hm.2.2.1
    simp only [highFaceParameter,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,zero_add,mul_one] at he
    change faceRatio1 v < Real.cos (sgn*Real.arccos (faceRatio1 v)) at he
    rw [hcos] at he
    exact (lt_irrefl _) he

theorem highFaceParameter_regular {sgn : ℝ} (hs : sgn = -1 ∨ sgn = 1)
    {v : ℝ × ℝ} (hv : v ∈ regularRealSubcritical) {a : ℝ} (ha : |a| < 1) :
    IsRegularJointEdge (highFaceParameter sgn (v,a)) := by
  let K := highFaceParameter sgn (v,a)
  have hcoords := highFaceParameter_coordinates sgn (v,a)
  have hx : K.1.re = v.1 := hcoords.1
  have hu : K.2.re = v.2 := hcoords.2.1
  have hi : K.2.im = a*Real.arccos (faceRatio2 v) := hcoords.2.2.2
  have hr₁ := faceRatio1_pos hv.2.2
  have hr₂ := faceRatio2_pos hv.2.1
  have h₁ := (faceRatio1_lt_one_iff v).mpr hv.1
  have h₂ := (faceRatio2_lt_one_iff v).mpr hv.1
  have hcos : Real.cos K.1.im = faceRatio1 v := by
    change Real.cos (highFaceParameter sgn (v,a)).1.im = _
    rw [hcoords.2.2.1,cos_sign_mul _ _ hs,Real.cos_arccos (by linarith) h₁.le]
  have hF : F1 K = 0 := by
    unfold F1
    rw [hcos]
    rw [hx,hu]
    rw [faceRatio1,Real.tanh_eq_sinh_div_cosh,cosh_abs_eq]
    have hh : Real.sinh |v.2|^2 = Real.sinh v.2^2 := by rw [←Real.abs_sinh,sq_abs]
    field_simp
    nlinarith [hh]
  have hg : 0 < F2 K := by
    have him : |K.2.im| < Real.pi/2 := by
      change |(highFaceParameter sgn (v,a)).2.im| < _
      rw [hcoords.2.2.2]
      exact scaled_arccos_strip hr₂.le h₂ ha
    have he : Real.cosh K.2.re*Real.tanh |K.1.re| < Real.cos K.2.im := by
      rw [hx,hu,hi]
      change faceRatio2 v < Real.cos (a*Real.arccos (faceRatio2 v))
      exact cosine_scaled_arccos_gt hr₂.le h₂ ha
    simpa [F2,mul_comm] using positive_edge_of_high him he
  apply regularJointEdge_of_face (Or.inl (highFaceParameter_frontier hs hv ha))
    (by simpa only [hcoords.2.1] using hv.2.2) hF hg.ne'

end
end IsingBulk.Joint
