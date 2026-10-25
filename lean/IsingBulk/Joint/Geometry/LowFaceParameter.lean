import IsingBulk.Joint.Geometry.AbsoluteCosineCharts

namespace IsingBulk.Joint
noncomputable section
open Set

def positiveRealSubcritical : Set (ℝ × ℝ) :=
  {v | realProduct v < 1 ∧ 0 < v.1 ∧ 0 < v.2}

theorem nonnegative_realProduct_mem_closure_positive {v : ℝ × ℝ}
    (hx : 0 ≤ v.1) (hu : 0 ≤ v.2) (hp : realProduct v ≤ 1) :
    v ∈ closure positiveRealSubcritical := by
  have hm : MapsTo (fun w : ℝ × ℝ => (|w.1|,|w.2|))
      regularRealSubcritical positiveRealSubcritical := by
    intro w hw
    exact ⟨by simpa [realProduct] using hw.1,abs_pos.mpr hw.2.1,abs_pos.mpr hw.2.2⟩
  have hc : Continuous (fun w : ℝ × ℝ => (|w.1|,|w.2|)) := by fun_prop
  have hh := hm.closure hc (realProduct_le_one_mem_closure_regular hp)
  simpa only [abs_of_nonneg hx,abs_of_nonneg hu,Prod.mk.eta] using hh

/-- All periods and both reflected cosine charts are retained. -/
def lowFaceParameter (k l : ℤ) (sgn τ : ℝ) (q : (ℝ × ℝ) × ℝ) : Coupling :=
  ((q.1.1 : ℂ) + ((k:ℝ)*Real.pi+sgn*Real.arccos (faceRatio1 q.1) : ℝ)*Complex.I,
   (q.1.2 : ℂ) + (2*(l:ℝ)*Real.pi+
     τ*(Real.pi/2+q.2*(Real.pi/2-Real.arccos (faceRatio2 q.1))) : ℝ)*Complex.I)

@[fun_prop] theorem lowFaceParameter_continuous (k l : ℤ) (sgn τ : ℝ) :
    Continuous (lowFaceParameter k l sgn τ) := by unfold lowFaceParameter; fun_prop

theorem lowFaceParameter_coordinates (k l : ℤ) (sgn τ : ℝ) (q : (ℝ × ℝ) × ℝ) :
    (lowFaceParameter k l sgn τ q).1.re = q.1.1 ∧
    (lowFaceParameter k l sgn τ q).2.re = q.1.2 ∧
    (lowFaceParameter k l sgn τ q).1.im = (k:ℝ)*Real.pi+sgn*Real.arccos (faceRatio1 q.1) ∧
    (lowFaceParameter k l sgn τ q).2.im = 2*(l:ℝ)*Real.pi+
      τ*(Real.pi/2+q.2*(Real.pi/2-Real.arccos (faceRatio2 q.1))) := by
  simp [lowFaceParameter]

theorem lowFaceParameter_frontier (k l : ℤ) {sgn τ : ℝ}
    (hs : sgn = -1 ∨ sgn = 1) (hτ : τ = -1 ∨ τ = 1)
    {v : ℝ × ℝ} (hv : v ∈ positiveRealSubcritical) {a : ℝ} (ha : |a| < 1) :
    lowFaceParameter k l sgn τ (v,a) ∈ frontier lowDomain := by
  have hr₁ := faceRatio1_pos hv.2.2.ne'
  have hr₂ := faceRatio2_pos hv.2.1.ne'
  have h₁ := (faceRatio1_lt_one_iff v).mpr hv.1
  have h₂ := (faceRatio2_lt_one_iff v).mpr hv.1
  have hcos := abs_cos_chart k hs hr₁.le h₁.le
  have hfree := cosine_free_chart_strict l hτ hr₂ h₂ ha
  rw [lowDomain_isOpen.frontier_eq]
  refine ⟨?_,?_⟩
  · apply closure_low_of_nonstrict
    · simpa [lowFaceParameter] using hv.2.1.le
    · simpa [lowFaceParameter] using hv.2.2.le
    · simpa [lowFaceParameter,faceRatio1,abs_of_pos hv.2.2] using hcos.le
    · simpa [lowFaceParameter,faceRatio2,abs_of_pos hv.2.1] using hfree.le
  · intro hm
    have hh := hm.2.2.1
    simp only [lowFaceParameter,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,zero_add,mul_one] at hh
    rw [hcos] at hh
    have he : faceRatio1 v = Real.cosh v.1*Real.tanh v.2 := by simp [faceRatio1,abs_of_pos hv.2.2]
    rw [he] at hh
    exact (lt_irrefl _) hh

theorem lowFaceParameter_regular (k l : ℤ) {sgn τ : ℝ}
    (hs : sgn = -1 ∨ sgn = 1) (hτ : τ = -1 ∨ τ = 1)
    {v : ℝ × ℝ} (hv : v ∈ positiveRealSubcritical) {a : ℝ} (ha : |a| < 1) :
    IsRegularJointEdge (lowFaceParameter k l sgn τ (v,a)) := by
  let K := lowFaceParameter k l sgn τ (v,a)
  have hcoords := lowFaceParameter_coordinates k l sgn τ (v,a)
  have hx : K.1.re = v.1 := hcoords.1
  have hu : K.2.re = v.2 := hcoords.2.1
  have hr₁ := faceRatio1_pos hv.2.2.ne'
  have hr₂ := faceRatio2_pos hv.2.1.ne'
  have h₁ := (faceRatio1_lt_one_iff v).mpr hv.1
  have h₂ := (faceRatio2_lt_one_iff v).mpr hv.1
  have hcos : |Real.cos K.1.im| = faceRatio1 v := by
    change |Real.cos (lowFaceParameter k l sgn τ (v,a)).1.im| = _
    rw [hcoords.2.2.1]
    exact abs_cos_chart k hs hr₁.le h₁.le
  have hF : F1 K = 0 := by
    unfold F1
    rw [←sq_abs (Real.cos K.1.im),hcos,hx,hu]
    rw [faceRatio1,abs_of_pos hv.2.2,Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring
  have hg : F2 K < 0 := by
    have he : |Real.cos K.2.im| < Real.cosh K.2.re*Real.tanh K.1.re := by
      change |Real.cos (lowFaceParameter k l sgn τ (v,a)).2.im| < _
      rw [hcoords.2.2.2,hx,hu]
      simpa [faceRatio2,abs_of_pos hv.2.1] using cosine_free_chart_strict l hτ hr₂ h₂ ha
    simpa [F2,mul_comm] using negative_edge_of_low he
  exact regularJointEdge_of_face (Or.inr (lowFaceParameter_frontier k l hs hτ hv ha))
    (by rw [hu]; exact hv.2.2.ne') hF hg.ne

end
end IsingBulk.Joint
