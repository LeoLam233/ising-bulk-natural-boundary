import IsingBulk.Tail.CompactRootContinuation
import Mathlib.Topology.UniformSpace.HeineCantor

/-! A continuous boundary representation of the physical root on the closed
upper W half-plane. This is not an analytic extension through branch points. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

def upperSqrtFormula (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z‖+z.re)/2):ℂ)+(Real.sqrt ((‖z‖-z.re)/2):ℂ)*Complex.I

theorem upperSqrtFormula_eq {z : ℂ} (hz : 0 ≤ z.im) :
    upperSqrtFormula z=Complex.sqrt z := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [upperSqrtFormula,hz]

theorem upperSqrtFormula_continuous : Continuous upperSqrtFormula := by
  unfold upperSqrtFormula
  fun_prop

def closedUpperRoot (W : ℂ) : ℂ := W-upperSqrtFormula (W-1)*upperSqrtFormula (W+1)

theorem closedUpperRoot_continuous : Continuous closedUpperRoot := by
  exact continuous_id.sub ((upperSqrtFormula_continuous.comp (continuous_id.sub continuous_const)).mul
    (upperSqrtFormula_continuous.comp (continuous_id.add continuous_const)))

theorem closedUpperRoot_eq_compactLeft {W : ℂ} (hW : 0 ≤ W.im) :
    closedUpperRoot W=compactLeftRoot W := by
  unfold closedUpperRoot compactLeftRoot
  rw [upperSqrtFormula_eq (by simpa using hW),upperSqrtFormula_eq (by simpa using hW)]

theorem sqrt_upper_strict_quadrant {z : ℂ} (hz : 0 < z.im) :
    0 < (Complex.sqrt z).re ∧ 0 < (Complex.sqrt z).im := by
  have hre := sqrt_real_nonnegative z
  have him : 0 ≤ (Complex.sqrt z).im := by
    rw [← upperSqrtFormula_eq hz.le,upperSqrtFormula]
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add]
    exact Real.sqrt_nonneg _
  have hs := congrArg Complex.im (sqrt_sq z)
  simp only [pow_two,Complex.mul_im] at hs
  constructor <;> nlinarith

/-- Any upper root of z+z⁻¹=2W has norm>1 when Im W>0. -/
theorem positive_imaginary_trace_root_norm {W z : ℂ} (hW : 0 < W.im)
    (hz : 0 < z.im) (ht : z+z⁻¹=2*W) : 1 < ‖z‖ := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have ht' := congrArg Complex.im ht
  simp [Complex.inv_im,Complex.mul_im,neg_div] at ht'
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have hh := (div_eq_iff (ne_of_gt hn)).mp
    (show z.im/Complex.normSq z=z.im-2*W.im by linarith)
  have hns : 1 < Complex.normSq z := by
    by_contra h
    have hle : Complex.normSq z ≤ 1 := le_of_not_gt h
    nlinarith [mul_pos hW hn]
  exact Complex.one_lt_normSq_iff.mp hns

/-- Physical overlap on the entire upper half-plane, not only Re W>1. -/
theorem compactLeftRoot_eq_physical_upper {W : ℂ} (hW : 0 < W.im) :
    compactLeftRoot W=interiorRoot W := by
  let a := Complex.sqrt (W-1)
  let b := Complex.sqrt (W+1)
  have ha : 0 < a.re ∧ 0 < a.im := sqrt_upper_strict_quadrant (by simpa using hW)
  have hb : 0 < b.re ∧ 0 < b.im := sqrt_upper_strict_quadrant (by simpa using hW)
  have hp : (W+a*b)*compactLeftRoot W=1 := by
    have ha2 : a^2=W-1 := sqrt_sq (W-1)
    have hb2 : b^2=W+1 := sqrt_sq (W+1)
    change (W+a*b)*(W-a*b)=1
    calc
      _ = W^2-a^2*b^2 := by ring
      _ = 1 := by rw [ha2,hb2]; ring
  have hvim : 0 < (W+a*b).im := by
    rw [Complex.add_im,Complex.mul_im]
    exact add_pos hW (add_pos (mul_pos ha.1 hb.2) (mul_pos ha.2 hb.1))
  have hinv := inv_eq_of_mul_eq_one_right hp
  have htrace : (W+a*b)+(W+a*b)⁻¹=2*W := by
    rw [hinv]
    change (W+a*b)+(W-a*b)=2*W
    ring
  have hn := positive_imaginary_trace_root_norm hW hvim htrace
  have hroot : ‖compactLeftRoot W‖ < 1 := by
    rw [← hinv,norm_inv]
    exact inv_lt_one_of_one_lt₀ hn
  exact quadratic_root_unique (compactLeftRoot_quadratic W) (interiorRoot_quadratic W)
    hroot (interiorRoot_norm_lt_one hW)

theorem closedUpperRoot_eq_physical {W : ℂ} (hW : 0 < W.im) :
    closedUpperRoot W=interiorRoot W := by
  rw [closedUpperRoot_eq_compactLeft hW.le]
  exact compactLeftRoot_eq_physical_upper hW

/-- A single root-continuation tolerance works on every bounded limiting
support. This uniformity precedes N, ε, λ and occupancy. -/
theorem physical_root_uniform_boundary_transfer (B η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ W W₀ : ℂ, ‖W₀‖ ≤ B → 0 < W.im →
      ‖W-W₀‖ < δ → ‖interiorRoot W-closedUpperRoot W₀‖ < η := by
  have hu := (isCompact_closedBall (0:ℂ) (B+1)).uniformContinuousOn_of_continuous
    closedUpperRoot_continuous.continuousOn
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  refine ⟨min δ 1,lt_min hδ zero_lt_one,?_⟩
  intro W W₀ hW₀ hi hdist
  have hWnorm : ‖W‖ ≤ B+1 := by
    have hn := norm_le_norm_add_norm_sub W₀ W
    rw [norm_sub_rev W₀ W] at hn
    have hh : ‖W-W₀‖ < 1 := hdist.trans_le (min_le_right _ _)
    linarith
  have hmem : W ∈ Metric.closedBall (0:ℂ) (B+1) := by simpa using hWnorm
  have hmem₀ : W₀ ∈ Metric.closedBall (0:ℂ) (B+1) := by
    simpa using (show ‖W₀‖ ≤ B+1 by linarith)
  have hh := hd W hmem W₀ hmem₀ (by simpa [dist_eq_norm] using hdist.trans_le (min_le_left _ _))
  rw [closedUpperRoot_eq_physical hi] at hh
  simpa [dist_eq_norm] using hh

end
end IsingBulk.Tail
