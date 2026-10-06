import IsingBulk.Tail.CompactPairStrictness
import IsingBulk.Tail.CompactRootContinuation
import IsingBulk.Analysis.RegularCoordinates

/-! Actual limiting compact roots and angular dispersion geometry. These
lemmas precede the choice of endpoint slivers and deformation strength. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

theorem compactRight_real_formula (w : ℝ) (hw : |w| < 1) :
    interiorRoot (w:ℂ) = (w:ℂ)-Complex.I*(Real.sqrt (1-w^2):ℂ) := by
  rw [interiorRoot,inverseCosineRoot_inverse]
  rw [show (1-(w:ℂ)^2)=((1-w^2:ℝ):ℂ) by push_cast; rfl,
    IsingBulk.Branch.sqrt_ofReal_nonnegative _ (by have h := abs_lt.mp hw; nlinarith)]

theorem compactRight_real_norm_im (w : ℝ) (hw : |w| < 1) :
    ‖interiorRoot (w:ℂ)‖=1 ∧ (interiorRoot (w:ℂ)).im<0 := by
  have hw' := abs_lt.mp hw
  have hpos : 0 < 1-w^2 := by nlinarith
  have hs := Real.sq_sqrt hpos.le
  have he := compactRight_real_formula w hw
  have him : (interiorRoot (w:ℂ)).im = -Real.sqrt (1-w^2) := by rw [he]; simp
  have hre : (interiorRoot (w:ℂ)).re = w := by rw [he]; simp
  constructor
  · have hn : Complex.normSq (interiorRoot (w:ℂ))=1 := by
      rw [Complex.normSq_apply,him,hre]
      nlinarith
    rw [← Complex.sq_norm] at hn
    nlinarith [norm_nonneg (interiorRoot (w:ℂ))]
  · rw [him]
    exact neg_neg_of_pos (Real.sqrt_pos.mpr hpos)

def limitingAngularW (b θ : ℝ) : ℝ := 1+Real.cos b-Real.cos θ

theorem limiting_left_W_gt_one (b θ : ℝ)
    (hb : 0 < b) (hbπ : b < Real.pi) (hθπ : -Real.pi ≤ θ) (hθ : θ < -b) :
    1 < limitingAngularW b θ := by
  have hcos := Real.strictAntiOn_cos
    (show b ∈ Set.Icc 0 Real.pi from ⟨hb.le,hbπ.le⟩)
    (show -θ ∈ Set.Icc 0 Real.pi from ⟨by linarith,by linarith⟩)
    (show b < -θ by linarith)
  rw [Real.cos_neg] at hcos
  unfold limitingAngularW
  linarith

theorem limiting_right_W_inside (b θ : ℝ)
    (hb : 0 < b) (hbπ : b < Real.pi) (hθ : -b < θ) (hθ0 : θ ≤ 0) :
    |limitingAngularW b θ| < 1 := by
  have hcos := Real.strictAntiOn_cos
    (show -θ ∈ Set.Icc 0 Real.pi from ⟨by linarith,by linarith⟩)
    (show b ∈ Set.Icc 0 Real.pi from ⟨hb.le,hbπ.le⟩)
    (show -θ < b by linarith)
  rw [Real.cos_neg] at hcos
  have hbcos : -1 < Real.cos b := by
    have h := Real.strictAntiOn_cos
      (show b ∈ Set.Icc 0 Real.pi from ⟨hb.le,hbπ.le⟩)
      (show Real.pi ∈ Set.Icc 0 Real.pi from ⟨Real.pi_pos.le,le_rfl⟩) hbπ
    simpa using h
  rw [abs_lt]
  unfold limitingAngularW
  constructor <;> linarith [Real.cos_le_one θ]

def limitingAngle (θ : ℝ) : ℂ := Complex.exp ((θ:ℂ)*Complex.I)

theorem limitingAngle_trace (θ : ℝ) :
    limitingAngle θ+(limitingAngle θ)⁻¹=2*(Real.cos θ:ℂ) := by
  unfold limitingAngle
  rw [← Complex.exp_neg]
  have he : -((θ:ℂ)*Complex.I)=((-θ:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  ring

theorem limitingAngle_norm (θ : ℝ) : ‖limitingAngle θ‖=1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem limitingAngle_lower_im (θ : ℝ) (hlo : -Real.pi ≤ θ) (hhi : θ ≤ 0) :
    (limitingAngle θ).im ≤ 0 := by
  simpa [limitingAngle] using Real.sin_nonpos_of_nonpos_of_neg_pi_le hhi hlo

theorem limiting_dispersion_coefficient (s : ℂ) (b θ : ℝ)
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) :
    2*sourceS s-limitingAngle θ-(limitingAngle θ)⁻¹ =
      2*(limitingAngularW b θ:ℂ) := by
  have ht := limitingAngle_trace θ
  rw [hS]
  unfold limitingAngularW
  push_cast at ht ⊢
  linear_combination -ht

/-- Actual limiting L×L complete pair, including θ=−π endpoints. -/
theorem limiting_left_complete_pair_strict (s : ℂ) (b θ φ : ℝ)
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ))
    (hb : 0 < b) (hbπ : b < Real.pi)
    (hθπ : -Real.pi ≤ θ) (hθ : θ < -b)
    (hφπ : -Real.pi ≤ φ) (hφ : φ < -b) :
    ‖canceledPair (limitingAngle θ) (limitingAngle φ)
      (compactLeftRoot (limitingAngularW b θ:ℂ))
      (compactLeftRoot (limitingAngularW b φ:ℂ))‖ < 1 := by
  have hWθ := limiting_left_W_gt_one b θ hb hbπ hθπ hθ
  have hWφ := limiting_left_W_gt_one b φ hb hbπ hφπ hφ
  obtain ⟨_,hiθ,hnθ⟩ := compactLeftRoot_real_bounds hWθ
  obtain ⟨_,hiφ,hnφ⟩ := compactLeftRoot_real_bounds hWφ
  apply complete_pair_strict_left (s := s) (limitingAngle_norm θ) (limitingAngle_norm φ)
    (limitingAngle_lower_im θ hθπ (by linarith))
    (limitingAngle_lower_im φ hφπ (by linarith))
    (compactLeftRoot_nonzero _) (compactLeftRoot_nonzero _)
  · rw [limiting_dispersion_coefficient s b θ hS]
    exact compactLeftRoot_quadratic _
  · rw [limiting_dispersion_coefficient s b φ hS]
    exact compactLeftRoot_quadratic _
  · exact hnθ
  · exact hnφ
  · exact hiθ.le
  · exact hiφ.le

/-- Actual limiting R×R complete pair, including θ=0 endpoints. -/
theorem limiting_right_complete_pair_strict (s : ℂ) (b θ φ : ℝ)
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ))
    (hb : 0 < b) (hbπ : b < Real.pi)
    (hθ : -b < θ) (hθ0 : θ ≤ 0) (hφ : -b < φ) (hφ0 : φ ≤ 0) :
    ‖canceledPair (limitingAngle θ) (limitingAngle φ)
      (interiorRoot (limitingAngularW b θ:ℂ))
      (interiorRoot (limitingAngularW b φ:ℂ))‖ < 1 := by
  have hWθ := limiting_right_W_inside b θ hb hbπ hθ hθ0
  have hWφ := limiting_right_W_inside b φ hb hbπ hφ hφ0
  obtain ⟨hnθ,hiθ⟩ := compactRight_real_norm_im _ hWθ
  obtain ⟨hnφ,hiφ⟩ := compactRight_real_norm_im _ hWφ
  apply complete_pair_strict_right (s := s) (limitingAngle_norm θ) (limitingAngle_norm φ)
    (limitingAngle_lower_im θ (by linarith) hθ0)
    (limitingAngle_lower_im φ (by linarith) hφ0)
    (interiorRoot_nonzero _) (interiorRoot_nonzero _)
  · rw [limiting_dispersion_coefficient s b θ hS]
    exact interiorRoot_quadratic _
  · rw [limiting_dispersion_coefficient s b φ hS]
    exact interiorRoot_quadratic _
  · exact hnθ.le
  · exact hnφ.le
  · exact hiθ
  · exact hiφ

end
end IsingBulk.Tail
