import IsingBulk.Tail.SelectorJacobian
import IsingBulk.Tail.SelectorHypotheses
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Real.Lemmas

/-! Dimension-uniform source angular Jacobian cost. Derivative suprema come
from fixed periodic bumps; occupancy remains variable and satisfies P≤N. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

 theorem retractionJacobian_norm_le {N : ℕ} (hN : 0 < N) {lam τ Bp Bm : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hτ : 0 ≤ τ) (_hBp : 0 ≤ Bp) (_hBm : 0 ≤ Bm)
    (p m p' m' : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp' : ∀ i, |p' i| ≤ Bp) (hm' : ∀ i, |m' i| ≤ Bm)
    (hdisjoint : ∀ i, m i*p' i=0) :
    ‖(retractionJacobian lam τ p m p' m').det‖ ≤ (1+2*τ*Bp+τ*Bm/2)^N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg hp0
  have hP1 := occupancy_le hp1
  let A := τ*occupancy p/(2*N)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : A ≤ τ/2 := by
    dsimp [A]
    apply (div_le_iff₀ (show 0 < (2:ℝ)*N by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hP1 hτ]
  have hl : |lam| ≤ 1 := abs_le.mpr ⟨by linarith,hlam1⟩
  have hbound (i : Fin N) :
      ‖Complex.I+(lam*(-2*τ*p' i+τ*occupancy p/(2*N)*m' i):ℝ)‖ ≤ 1+2*τ*Bp+τ*Bm/2 := by
    have hcoef : |-2*τ*p' i+A*m' i| ≤ 2*τ*Bp+τ*Bm/2 := by
      calc
        _ ≤ |-2*τ*p' i|+|A*m' i| := abs_add_le _ _
        _ = 2*τ*|p' i|+A*|m' i| := by simp [abs_mul,abs_of_nonneg hτ,abs_of_nonneg hA0]
        _ ≤ 2*τ*Bp+τ*Bm/2 := by
          have hp := mul_le_mul_of_nonneg_left (hp' i) (show 0 ≤ 2*τ by positivity)
          have hm := mul_le_mul hA1 (hm' i) (abs_nonneg (m' i)) (show 0 ≤ τ/2 by positivity)
          nlinarith
    have hmul := mul_le_mul_of_nonneg_right hl (abs_nonneg (-2*τ*p' i+A*m' i))
    have hnrm := norm_add_le Complex.I ((lam*(-2*τ*p' i+A*m' i):ℝ):ℂ)
    simp only [Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,abs_mul] at hnrm
    change ‖Complex.I+(lam*(-2*τ*p' i+A*m' i):ℝ)‖ ≤ _
    linarith
  rw [retractionJacobian_det lam τ p m p' m' hdisjoint,norm_prod]
  calc
    _ ≤ ∏ _i : Fin N, (1+2*τ*Bp+τ*Bm/2) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hbound i)
    _ = _ := by simp

 theorem constructed_m_mul_p_deriv_zero (b η α : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α) :
    ∀ θ, (constructedSelector b η α).m θ*deriv (constructedSelector b η α).p θ=0 := by
  intro θ
  by_cases hm : (constructedSelector b η α).m θ=0
  · rw [hm,zero_mul]
  · have hd := constructed_selector_supports_disjoint b η α hb hη hηsmall hα
    have hp : deriv (constructedSelector b η α).p θ=0 := by
      by_contra hp
      exact Set.disjoint_left.mp hd (support_deriv_subset hp) (subset_closure hm)
    rw [hp,mul_zero]

 theorem constructed_selector_jacobian_bound (b η α τ : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      ∀ θ : Fin N → ℝ, ‖(angularJacobian (constructedSelector b η α) τ lam θ).det‖ ≤ C^N := by
  let f := constructedSelector b η α
  have hf := constructedSelector_regular b η α hb hη hηsmall hα
  have hpbd := (periodic_derivative hf.p_periodic).isBounded_of_continuous
    Real.two_pi_pos.ne' (hf.p_smooth.continuous_deriv (by simp))
  have hmbd := (periodic_derivative hf.m_periodic).isBounded_of_continuous
    Real.two_pi_pos.ne' (hf.m_smooth.continuous_deriv (by simp))
  obtain ⟨Bp,hBp,hp⟩ := hpbd.exists_pos_norm_le
  obtain ⟨Bm,hBm,hm⟩ := hmbd.exists_pos_norm_le
  refine ⟨1+2*τ*Bp+τ*Bm/2,by positivity,?_⟩
  intro N hN lam hlam hlam1 θ
  apply retractionJacobian_norm_le hN hlam hlam1 hτ hBp.le hBm.le
  · intro i; exact (thresholdStep_range _ _ _).1
  · intro i; exact (thresholdStep_range _ _ _).2
  · intro i
    simpa only [Real.norm_eq_abs] using hp (deriv f.p (θ i)) ⟨θ i,rfl⟩
  · intro i
    simpa only [Real.norm_eq_abs] using hm (deriv f.m (θ i)) ⟨θ i,rfl⟩
  · intro i
    exact constructed_m_mul_p_deriv_zero b η α hb hη hηsmall hα (θ i)

end
end IsingBulk.Tail
