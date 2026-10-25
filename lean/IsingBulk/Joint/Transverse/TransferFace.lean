import IsingBulk.Joint.Transverse.CurveCoordinates
import IsingBulk.Joint.Geometry.TransferChart
import IsingBulk.Joint.Geometry.Basic

/-! # Literal parallelogram coordinates and the regular positive face
The local side is derived from the independently defined spectral set.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter
open scoped Topology

def faceA (K : Coupling) : ℝ :=
  (transferC K).re-(transferB K).re*((transferC K).im/(transferB K).im)
def faceB (K : Coupling) : ℝ := (transferC K).im/(transferB K).im

theorem spectralSet_iff_transfer {K : Coupling} (hS : S K≠0) :
    K∈spectralSet ↔ ∃ a∈Icc (-1:ℝ) 1, ∃ b∈Icc (-1:ℝ) 1,
      transferC K=(a:ℂ)+transferB K*(b:ℂ) := by
  constructor
  · rintro ⟨a,ha,b,hb,he⟩
    refine ⟨a,ha,b,hb,?_⟩
    unfold transferC transferB
    rw [he]
    field_simp
  · rintro ⟨a,ha,b,hb,he⟩
    refine ⟨a,ha,b,hb,?_⟩
    unfold transferC transferB at he
    field_simp at he
    linear_combination he

theorem transfer_face_coordinates {K : Coupling} (hB : (transferB K).im≠0) :
    transferC K=(faceA K:ℂ)+transferB K*(faceB K:ℂ) := by
  apply Complex.ext
  · simp [faceA,faceB,Complex.mul_re]
  · simp only [faceA,faceB,Complex.add_im,Complex.ofReal_im,zero_add,
      Complex.mul_im,Complex.ofReal_re,mul_zero]
    exact (mul_div_cancel₀ (transferC K).im hB).symm

theorem transfer_face_coordinates_unique {K : Coupling} {a b : ℝ}
    (hB : (transferB K).im≠0) (he : transferC K=(a:ℂ)+transferB K*(b:ℂ)) :
    faceA K=a ∧ faceB K=b := by
  have hi := congrArg Complex.im he
  have hr := congrArg Complex.re he
  simp only [Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.ofReal_re,mul_zero] at hi
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    mul_zero,sub_zero] at hr
  have hb : faceB K=b := by
    unfold faceB
    rw [hi,mul_div_cancel_left₀ _ hB]
  refine ⟨?_,hb⟩
  change (transferC K).re-(transferB K).re*faceB K=a
  rw [hb,hr]
  ring

theorem spectralSet_iff_face_coordinates {K : Coupling}
    (hS : S K≠0) (hB : (transferB K).im≠0) :
    K∈spectralSet ↔ faceA K∈Icc (-1:ℝ) 1 ∧ faceB K∈Icc (-1:ℝ) 1 := by
  rw [spectralSet_iff_transfer hS]
  constructor
  · rintro ⟨a,ha,b,hb,he⟩
    obtain ⟨hfa,hfb⟩ := transfer_face_coordinates_unique hB he
    simpa [hfa,hfb] using And.intro ha hb
  · rintro ⟨ha,hb⟩
    exact ⟨faceA K,ha,faceB K,hb,transfer_face_coordinates hB⟩

/-- An actual open neighborhood of the relative interior of the positive face. -/
def positiveFaceNeighborhood : Set Coupling :=
  {K | S K≠0 ∧ 0<(transferB K).im ∧ |faceA K|<1 ∧ -1<faceB K}

theorem positiveFaceNeighborhood_isOpen : IsOpen positiveFaceNeighborhood := by
  apply isOpen_iff_mem_nhds.mpr
  intro K hK
  have hC := (transferC_analyticAt hK.1).continuousAt
  have hB := (transferB_analyticAt hK.1).continuousAt
  have hfB : ContinuousAt faceB K :=
    (Complex.continuous_im.continuousAt.comp hC).div
      (Complex.continuous_im.continuousAt.comp hB) hK.2.1.ne'
  have hfA : ContinuousAt faceA K :=
    (Complex.continuous_re.continuousAt.comp hC).sub
      ((Complex.continuous_re.continuousAt.comp hB).mul hfB)
  filter_upwards [continuous_S.continuousAt.eventually_ne hK.1,
    (Complex.continuous_im.continuousAt.comp hB).eventually_const_lt hK.2.1,
    hfA.abs.eventually_lt_const hK.2.2.1,hfB.eventually_const_lt hK.2.2.2] with L hs hb ha hc
  exact ⟨hs,hb,ha,hc⟩

theorem mem_positiveFaceNeighborhood {K : Coupling} {b : ℝ}
    (hS : S K≠0) (hB : 0<(transferB K).im) (hb : |b|<1)
    (he : positiveParameter b K=0) : K∈positiveFaceNeighborhood := by
  have hc : transferC K=(b:ℂ)+transferB K*(1:ℂ) := by
    unfold positiveParameter at he
    linear_combination he
  have hf := transfer_face_coordinates_unique hB.ne' hc
  exact ⟨hS,hB,by simpa [hf.1] using hb,by rw [hf.2]; norm_num⟩

/-- The physical complement is exactly the outward normal half-side here.
This is an identity of actual joint spectral sets, not a slice condition. -/
theorem positiveFace_complement_iff {K : Coupling} (hK : K∈positiveFaceNeighborhood) (b : ℝ) :
    K∉spectralSet ↔ 0<(positiveParameter b K).im := by
  rw [spectralSet_iff_face_coordinates hK.1 hK.2.1.ne']
  have ha : faceA K∈Icc (-1:ℝ) 1 := ⟨(abs_lt.mp hK.2.2.1).1.le,(abs_lt.mp hK.2.2.1).2.le⟩
  have he : (positiveParameter b K).im=(transferB K).im*(faceB K-1) := by
    simp only [positiveParameter,Complex.sub_im,Complex.ofReal_im,sub_zero,faceB]
    rw [mul_sub,mul_div_cancel₀ _ hK.2.1.ne',mul_one]
  rw [and_iff_right ha,mem_Icc,not_and,he]
  constructor
  · intro hn
    have ht : 1<faceB K := lt_of_not_ge (hn hK.2.2.2.le)
    exact mul_pos hK.2.1 (sub_pos.mpr ht)
  · intro hp _ hb
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hK.2.1.le (sub_nonpos.mpr hb))) hp

end
end IsingBulk.Joint.Transverse
