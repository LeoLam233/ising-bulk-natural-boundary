import IsingBulk.Tail.MicrocoreAllOrder
import IsingBulk.Analysis.BranchDerivative

/-! The microcore coefficient chart follows from physical quadrant and
angular-branch orientation, without selected-pair or collision hypotheses. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Branch IsingBulk.Lie

theorem square_mem_slit_of_re_pos (z : ℂ) (hz : 0 < z.re) : z^2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : z.im=0
  · left
    simp [pow_two,Complex.mul_re,hi]
    positivity
  · right
    simp only [pow_two,Complex.mul_im]
    intro h
    have hh : z.re*z.im=0 := by linarith
    exact (mul_ne_zero hz.ne' hi) hh

theorem microcoreJetPoint_of_quadrants {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hs : s ≠ 0) (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re) : MicrocoreJetPoint v θ s x := by
  refine ⟨hs,hr,hi,hg,?_,?_⟩
  · intro i hn
    have he : Complex.sin (chartPhase s v θ (x i))^2=1-(chartW s v θ (x i))^2 := by
      rw [chartPhase,sin_lowerArccos,sqrt_sq]
    rw [hn,zero_pow (by norm_num : (2:ℕ)≠0)] at he
    have hh := congrArg Complex.im he
    simp only [Complex.zero_im,Complex.sub_im,Complex.one_im,pow_two,Complex.mul_im] at hh
    nlinarith [mul_pos (hr i) (hi i)]
  · intro i
    have hy : angularY v θ (x i) ≠ 0 := Complex.exp_ne_zero _
    have hH : s+s⁻¹-Complex.cos (chartPhase s v θ (x i)) =
        (angularY v θ (x i)+(angularY v θ (x i))⁻¹)/2 := by
      rw [chartPhase_cos,chartW,IsingBulk.Branch.dispersion]
      ring
    have hsq : (angularG v θ (x i))^2 =
        1-((angularY v θ (x i)+(angularY v θ (x i))⁻¹)/2)^2 := by
      unfold angularG
      field_simp
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hH,← hsq]
    exact square_mem_slit_of_re_pos _ (hg i)

end
end IsingBulk.Tail
