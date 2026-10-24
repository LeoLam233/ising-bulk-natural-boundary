import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedWitness
import IsingBulk.Anisotropic.NegativeNormalForm.ActualMeanField

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric

/-- Actual reciprocal-root input bounds on a common smaller inverse ball. -/
theorem inverseRootField_uniform_on_subball {n : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C) (hr : 0<r)
    (δ ρ ε L : ℝ) (hδ : 0<δ) (hδr : 4*δ≤r) (hδρ : 4*δ≤ρ)
    (hd : ‖d‖<δ) (hτ : ‖1-Complex.cos d‖<ρ/2) (hε : 0≤ε) (hL : 0≤L)
    (hroot : ∀ p : ScalarTriple, ‖p‖<ρ →
      AnalyticAt ℂ (fun x : ScalarTriple => Complex.sqrt (phaseEnergy B phi hphi x.2.1 x.1 x.2.2)) p ∧
      ‖Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)-1‖≤ε)
    (hLip : ∀ p q : ScalarTriple, ‖p‖<ρ → ‖q‖<ρ →
      ‖Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)-
        Complex.sqrt (phaseEnergy B phi hphi q.2.1 q.1 q.2.2)‖≤L*‖p-q‖) :
    AnalyticOnNhd ℂ (inverseRootField B phi hphi d P.T P.V) (ball 0 δ) ∧
      (∀ w : Config n, ‖w‖≤δ → ‖inverseRootField B phi hphi d P.T P.V w-1‖≤ε) ∧
      (∀ w z : Config n, ‖w‖≤δ → ‖z‖≤δ →
        ‖inverseRootField B phi hphi d P.T P.V w-inverseRootField B phi hphi d P.T P.V z‖≤2*L*‖w-z‖) := by
  have hVbound (w : Config n) (hw : ‖w‖≤δ) : ‖P.V w‖≤2*‖w‖ :=
    (P.v_inverse w (by linarith)).2.1
  have hVsource (w : Config n) (hw : ‖w‖≤δ) : ‖P.V w‖<2*r := by
    have hh := hVbound w hw
    linarith
  have hinput (w : Config n) (hw : ‖w‖≤δ) (i : Fin n) : ‖(P.T (P.V w),(d,P.V w i))‖<ρ := by
    have hT := P.t_lip (P.V w) 0 (hVsource w hw) (by simpa using (show 0<2*r by positivity))
    rw [P.t_zero,sub_zero] at hT
    have htri := norm_le_norm_sub_add (P.T (P.V w)) (1-Complex.cos d)
    have hV := hVbound w hw
    have hi := norm_le_pi_norm (P.V w) i
    exact max_lt (by linarith) (max_lt (by linarith) (by linarith))
  refine ⟨?_,?_,?_⟩
  · intro w hw
    have hw' : ‖w‖<δ := by simpa using hw
    have hV := P.v_analytic w (show w∈ball 0 (r/2) by simpa using (show ‖w‖<r/2 by linarith))
    have hT := P.t_analytic (P.V w) (by simpa using hVsource w hw'.le)
    have hTV := hT.comp (f := P.V) hV
    apply analyticAt_pi_iff.mpr
    intro i
    exact ((hroot (P.T (P.V w),(d,P.V w i)) (hinput w hw'.le i)).1).comp
      (f := fun z : Config n => (P.T (P.V z),(d,P.V z i)))
      (hTV.prod (analyticAt_const.prod (analyticAt_pi_iff.mp hV i)))
  · intro w hw
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    exact (hroot (P.T (P.V w),(d,P.V w i)) (hinput w hw i)).2
  · intro w z hw hz
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hV := P.v_lip w z (by linarith) (by linarith)
    have hT := P.t_lip (P.V w) (P.V z) (hVsource w hw) (hVsource z hz)
    have hdist : ‖(P.T (P.V w),(d,P.V w i))-(P.T (P.V z),(d,P.V z i))‖≤2*‖w-z‖ := by
      change max ‖P.T (P.V w)-P.T (P.V z)‖ (max ‖d-d‖ ‖P.V w i-P.V z i‖)≤2*‖w-z‖
      simp only [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
      exact max_le (hT.trans hV) ((norm_le_pi_norm (P.V w-P.V z) i).trans hV)
    have hh := (hLip (P.T (P.V w),(d,P.V w i)) (P.T (P.V z),(d,P.V z i))
      (hinput w hw i) (hinput z hz i)).trans (mul_le_mul_of_nonneg_left hdist hL)
    convert hh using 1
    · rfl
    · ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
