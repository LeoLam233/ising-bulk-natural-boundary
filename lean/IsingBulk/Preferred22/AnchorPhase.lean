import IsingBulk.Preferred22.RightDomain
import IsingBulk.Preferred22.PhysicalAnalytic

/-! The compact-left physical phase, including its real reference curve.
The definition uses the physical disk root, so its boundary value at W>1
is the lower phase approached by the actual outward contour. The equality
with the manuscript's explicit inverse cosine is proved on the actual
upper-W source, rather than asserted at the branch-cut totalization. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A branch-explicit physical phase on the compact left part. -/
def preferredPhysicalPhase (W : ℂ) : ℂ := Complex.I*Complex.log (physicalRoot W)

theorem physicalRoot_re_pos_of_re_pos {W : ℂ} (hW : 0<W.re) :
    0<(physicalRoot W).re := by
  have hr : (physicalRoot W).re+(physicalRoot W).re/Complex.normSq (physicalRoot W)=2*W.re := by
    simpa [Complex.inv_re] using congrArg Complex.re (physicalRoot_trace W)
  by_contra hn
  have hz : (physicalRoot W).re≤0 := le_of_not_gt hn
  have hi : (physicalRoot W).re/Complex.normSq (physicalRoot W)≤0 :=
    div_nonpos_of_nonpos_of_nonneg hz (Complex.normSq_nonneg _)
  linarith

theorem preferredPhysicalPhase_exp (W : ℂ) :
    Complex.exp (-Complex.I*preferredPhysicalPhase W)=physicalRoot W := by
  have he : -Complex.I*preferredPhysicalPhase W=Complex.log (physicalRoot W) := by
    unfold preferredPhysicalPhase
    calc
      _ = -(Complex.I*Complex.I)*Complex.log (physicalRoot W) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he,Complex.exp_log (physicalRoot_ne_zero W)]

theorem preferredPhysicalPhase_cos (W : ℂ) :
    Complex.cos (preferredPhysicalPhase W)=W := by
  have he : preferredPhysicalPhase W*Complex.I= -Complex.log (physicalRoot W) := by
    unfold preferredPhysicalPhase
    calc
      _ = Complex.I*Complex.I*Complex.log (physicalRoot W) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Complex.cos,he,Complex.exp_neg,Complex.exp_log (physicalRoot_ne_zero W)]
  have hn : -preferredPhysicalPhase W*Complex.I=Complex.log (physicalRoot W) := by
    rw [neg_mul,he,neg_neg]
  rw [hn,Complex.exp_log (physicalRoot_ne_zero W)]
  have ht := physicalRoot_trace W
  linear_combination ht/2

/-- Exact physical agreement at every actual outward point. -/
theorem preferredPhysicalPhase_eq_arccos_upper {W : ℂ} (hW : 0<W.im) :
    preferredPhysicalPhase W=preferredArccos W := by
  have hs := IsingBulk.Branch.lowerArccos_sheet_of_upper hW
  change Complex.cos (preferredArccos W)=W ∧ 0<(preferredArccos W).re ∧
    (preferredArccos W).re<Real.pi ∧ (preferredArccos W).im<0 at hs
  have hl : -Real.pi<(-Complex.I*preferredArccos W).im := by
    simpa using neg_lt_neg hs.2.2.1
  have hu : (-Complex.I*preferredArccos W).im≤Real.pi := by
    simp only [Complex.mul_im,Complex.neg_im,Complex.I_im,
      Complex.I_re,zero_mul,zero_add,neg_mul,one_mul]
    linarith [Real.pi_pos]
  unfold preferredPhysicalPhase
  rw [←preferredArccos_physical_upper W hW,Complex.log_exp hl hu]
  calc
    _ = -(Complex.I*Complex.I)*preferredArccos W := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem preferredPhysicalPhase_analyticAt {W : ℂ}
    (hW : OffRealSegment W) (hr : 0<W.re) : AnalyticAt ℂ preferredPhysicalPhase W := by
  exact analyticAt_const.mul ((physicalRoot_analyticAt hW).clog
    (Or.inl (physicalRoot_re_pos_of_re_pos hr)))

theorem preferredPhysicalPhase_analyticAt_right {W : ℂ} (hr : 1<W.re) :
    AnalyticAt ℂ preferredPhysicalPhase W :=
  preferredPhysicalPhase_analyticAt (Or.inr (hr.trans_le (le_abs_self _))) (by linarith)

theorem preferredPhysicalPhase_im_neg {W : ℂ} (hW : OffRealSegment W) :
    (preferredPhysicalPhase W).im<0 := by
  change (Complex.I*Complex.log (physicalRoot W)).im<0
  simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,Complex.log_re]
  exact Real.log_neg (norm_pos_iff.mpr (physicalRoot_ne_zero W)) (physicalRoot_inside hW)

theorem preferredPhysicalPhase_re_of_real {x : ℝ} (hx : 1<x) :
    (preferredPhysicalPhase (x:ℂ)).re=0 := by
  have hOff : OffRealSegment (x:ℂ) := Or.inr (by simpa using hx.trans_le (le_abs_self x))
  have hc := physicalRoot_conj hOff
  have hi : (physicalRoot (x:ℂ)).im=0 := by
    have h : (physicalRoot (x:ℂ)).im= -(physicalRoot (x:ℂ)).im := by
      simpa using congrArg Complex.im hc
    linarith
  have hr : 0<(physicalRoot (x:ℂ)).re := physicalRoot_re_pos_of_re_pos (by simpa using lt_trans zero_lt_one hx)
  have he : physicalRoot (x:ℂ)=((physicalRoot (x:ℂ)).re:ℂ) := by
    apply Complex.ext <;> simp [hi]
  unfold preferredPhysicalPhase
  rw [he,←Complex.ofReal_log hr.le]
  simp

theorem preferredPhysicalPhase_sin_ne_zero {W : ℂ} (hW : 1<W.re) :
    Complex.sin (preferredPhysicalPhase W)≠0 := by
  intro hs
  have hp := Complex.sin_sq_add_cos_sq (preferredPhysicalPhase W)
  rw [hs,preferredPhysicalPhase_cos] at hp
  have hz : (W-1)*(W+1)=0 := by linear_combination hp
  rcases mul_eq_zero.mp hz with hz | hz
  · have he : W=1 := sub_eq_zero.mp hz
    simp [he] at hW
  · have he : W= -1 := eq_neg_of_add_eq_zero_left hz
    norm_num [he] at hW

/-- The literal inverse remains regular on the lower physical reference
curve in the compact-left region, with no artificial boundary branch. -/
theorem preferred_compact_left_inverse_reference (s : ℂ) (θ : ℝ)
    (hS : 0<(temperatureTrace s).re)
    (hSi : (temperatureTrace s).im=0)
    (hW : 1<(temperatureTrace s-Complex.cos (θ:ℂ)).re)
    (hθlo : -2*Real.pi<θ) (hθhi : θ<0)
    (hB : AnalyticAt ℂ preferredMovingBranch s) :
    let φ := preferredPhysicalPhase (temperatureTrace s-Complex.cos (θ:ℂ))
    let q := φ+(θ:ℂ)-preferredMovingBranch s
    preferredMovingInverse s q=(θ:ℂ) ∧
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) ∧
    deriv (preferredMovingInverse s) q≠0 := by
  let W := temperatureTrace s-Complex.cos (θ:ℂ)
  let φ := preferredPhysicalPhase W
  let q := φ+(θ:ℂ)-preferredMovingBranch s
  have hWi : W.im=0 := by simp [W,Complex.cos_ofReal_im,hSi]
  have hWcast : W=(W.re:ℂ) := by apply Complex.ext <;> simp [hWi]
  have hφre : φ.re=0 := by
    change (preferredPhysicalPhase W).re=0
    rw [hWcast]
    exact preferredPhysicalPhase_re_of_real hW
  have hdisp : Complex.cos (θ:ℂ)+Complex.cos φ=temperatureTrace s := by
    rw [show Complex.cos φ=W from preferredPhysicalPhase_cos W]
    dsimp [W]
    ring
  have hc : Complex.cos (((θ:ℂ)+φ)/2)≠0 := by
    intro hz
    have hh := Complex.cos_add_cos (θ:ℂ) φ
    rw [hz,mul_zero,zero_mul,hdisp] at hh
    rw [hh,Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  have hl : 0<((φ-(θ:ℂ))/2).re := by
    simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.ofReal_re,hφre]
    linarith
  have hu : ((φ-(θ:ℂ))/2).re<Real.pi := by
    simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.ofReal_re,hφre]
    linarith
  have hraw := complexRightInverse_analyticAt_of_strip (temperatureTrace s) (θ:ℂ) φ hdisp hc hl hu
  have hqeq : q+preferredMovingBranch s=(θ:ℂ)+φ := by dsimp [q]; ring
  have hinv : preferredMovingInverse s q=(θ:ℂ) := by
    change complexRightInverse (temperatureTrace s) (q+preferredMovingBranch s)=(θ:ℂ)
    rw [hqeq]
    exact complexRightInverse_inverse _ _ _ hdisp hc hl hu
  have hs0 : s≠0 := by intro he; simp [he,temperatureTrace] at hS
  have hSa : AnalyticAt ℂ temperatureTrace s := analyticAt_id.add (analyticAt_id.inv hs0)
  have hSf : AnalyticAt ℂ (fun z : ℂ × ℂ => temperatureTrace z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := temperatureTrace) hSa analyticAt_fst
  have hBf : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingBranch z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := preferredMovingBranch) hB analyticAt_fst
  have hmap : AnalyticAt ℂ (fun z : ℂ × ℂ => (temperatureTrace z.1,z.2+preferredMovingBranch z.1)) (s,q) :=
    hSf.prod (analyticAt_snd.add hBf)
  have hUa : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) :=
    hraw.comp_of_eq hmap (by simp only [hqeq])
  have hraw₁ : AnalyticAt ℂ (complexRightInverse (temperatureTrace s)) ((θ:ℂ)+φ) :=
    AnalyticAt.comp (f := fun v : ℂ => (temperatureTrace s,v))
      (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) hraw (analyticAt_const.prod analyticAt_id)
  have hder := hraw₁.differentiableAt.hasDerivAt.comp_of_eq q
    ((hasDerivAt_id q).add_const (preferredMovingBranch s)) hqeq.symm
  have hd : deriv (preferredMovingInverse s) q=
      deriv (complexRightInverse (temperatureTrace s)) ((θ:ℂ)+φ) := by
    convert! hder.deriv using 1
    simp only [mul_one]
  refine ⟨hinv,hUa,?_⟩
  rw [hd]
  exact complexRightInverse_deriv_ne_zero_of_strip _ _ _ hdisp hc hl hu
    (preferredPhysicalPhase_sin_ne_zero hW)

end
end IsingBulk.Preferred22
