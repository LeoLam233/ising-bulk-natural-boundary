import IsingBulk.Preferred22.ContourBumpJets
import IsingBulk.Preferred22.ContourJetDeterminant
import IsingBulk.Preferred22.ContourJacobianRestriction

/-! The balanced full Jacobian has diagonal O(1) and off-diagonal O(1/N)
fixed jets. All occupancies are their genuine angular sums. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def jacobianDiagonalCoefficient {N : ℕ} (p m : ℝ → ℝ) (i : Fin N)
    (θ : Fin N → ℝ) : ℝ :=
  normalizedOccupancy p θ*deriv m (θ i) - normalizedOccupancy m θ*deriv p (θ i)

def jacobianRankCoefficient {N : ℕ} (p m : ℝ → ℝ) (i j : Fin N)
    (θ : Fin N → ℝ) : ℝ :=
  m (θ i)*deriv p (θ j) - p (θ i)*deriv m (θ j)

theorem jacobianDiagonalCoefficient_contDiff {N : ℕ} (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (i : Fin N) :
    ContDiff ℝ ∞ (jacobianDiagonalCoefficient p m i) := by
  have hdp := (contDiff_infty_iff_deriv.mp hp).2
  have hdm := (contDiff_infty_iff_deriv.mp hm).2
  exact ((normalizedOccupancy_contDiff p hp).mul (hdm.comp (contDiff_apply ℝ ℝ i))).sub
    ((normalizedOccupancy_contDiff m hm).mul (hdp.comp (contDiff_apply ℝ ℝ i)))

theorem jacobianRankCoefficient_contDiff {N : ℕ} (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (i j : Fin N) :
    ContDiff ℝ ∞ (jacobianRankCoefficient p m i j) := by
  have hdp := (contDiff_infty_iff_deriv.mp hp).2
  have hdm := (contDiff_infty_iff_deriv.mp hm).2
  exact ((hm.comp (contDiff_apply ℝ ℝ i)).mul (hdp.comp (contDiff_apply ℝ ℝ j))).sub
    ((hp.comp (contDiff_apply ℝ ℝ i)).mul (hdm.comp (contDiff_apply ℝ ℝ j)))

theorem fullAngularJacobian_entry_decomposition {N : ℕ}
    (τ lam : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) (i j : Fin N) :
    fullAngularJacobian τ lam p m θ i j = (if i=j then 1 else 0) -
      (Complex.I*(lam:ℂ)*(τ:ℂ)) *
        ((if i=j then (jacobianDiagonalCoefficient p m i θ:ℂ) else 0) +
          (N:ℂ)⁻¹*(jacobianRankCoefficient p m i j θ:ℂ)) := by
  unfold fullAngularJacobian shiftJacobian jacobianDiagonalCoefficient
    jacobianRankCoefficient normalizedOccupancy occupancy
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  · simp only [hij, ite_false]
    push_cast
    simp only [div_eq_mul_inv]
    ring

theorem jacobianCoefficients_uniform_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (J : ℕ) : ∃ A : ℝ, 0<A ∧ ∀ N : ℕ, 0<N → ∀ (i j : Fin N) (θ : Fin N → ℝ),
      ∀ r≤J,
        ‖iteratedFDeriv ℝ r (jacobianDiagonalCoefficient p m i) θ‖≤A ∧
        ‖iteratedFDeriv ℝ r (jacobianRankCoefficient p m i j) θ‖≤A := by
  have hdp : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.mp hp).2
  have hdm : ContDiff ℝ ∞ (deriv m) := (contDiff_infty_iff_deriv.mp hm).2
  obtain ⟨Bp,hBp,hbp⟩ := bump_finite_jets p hp hpp J
  obtain ⟨Bm,hBm,hbm⟩ := bump_finite_jets m hm hmp J
  obtain ⟨Dp,hDp,hdpB⟩ := bump_finite_jets (deriv p) hdp (bump_derivative_periodic hpp) J
  obtain ⟨Dm,hDm,hdmB⟩ := bump_finite_jets (deriv m) hdm (bump_derivative_periodic hmp) J
  let B := Bp+Bm+Dp+Dm
  have hB : 0<B := by dsimp [B]; linarith
  have hbp' (r : ℕ) (hr : r≤J) (x : ℝ) : ‖iteratedFDeriv ℝ r p x‖≤B :=
    (hbp r hr x).trans (by dsimp [B]; linarith)
  have hbm' (r : ℕ) (hr : r≤J) (x : ℝ) : ‖iteratedFDeriv ℝ r m x‖≤B :=
    (hbm r hr x).trans (by dsimp [B]; linarith)
  have hdp' (r : ℕ) (hr : r≤J) (x : ℝ) : ‖iteratedFDeriv ℝ r (deriv p) x‖≤B :=
    (hdpB r hr x).trans (by dsimp [B]; linarith)
  have hdm' (r : ℕ) (hr : r≤J) (x : ℝ) : ‖iteratedFDeriv ℝ r (deriv m) x‖≤B :=
    (hdmB r hr x).trans (by dsimp [B]; linarith)
  refine ⟨2*(2^J*B*B),by positivity,?_⟩
  intro N hN i j θ r hr
  have hP (r : ℕ) (hr : r≤J) := normalizedOccupancy_jet_le hN p hp hB.le (hbp' r hr) θ
  have hM (r : ℕ) (hr : r≤J) := normalizedOccupancy_jet_le hN m hm hB.le (hbm' r hr) θ
  have hpc (i : Fin N) (r : ℕ) (hr : r≤J) := coordinate_real_jet_le p hp hB.le (hbp' r hr) i θ
  have hmc (i : Fin N) (r : ℕ) (hr : r≤J) := coordinate_real_jet_le m hm hB.le (hbm' r hr) i θ
  have hdpc (i : Fin N) (r : ℕ) (hr : r≤J) := coordinate_real_jet_le (deriv p) hdp hB.le (hdp' r hr) i θ
  have hdmc (i : Fin N) (r : ℕ) (hr : r≤J) := coordinate_real_jet_le (deriv m) hdm hB.le (hdm' r hr) i θ
  have hPsm := @normalizedOccupancy_contDiff N p hp
  have hMsm := @normalizedOccupancy_contDiff N m hm
  have hpcsm (i : Fin N) := hp.comp (contDiff_apply ℝ ℝ i)
  have hmcsm (i : Fin N) := hm.comp (contDiff_apply ℝ ℝ i)
  have hdpcsm (i : Fin N) := hdp.comp (contDiff_apply ℝ ℝ i)
  have hdmcsm (i : Fin N) := hdm.comp (contDiff_apply ℝ ℝ i)
  constructor
  · exact (real_difference_jet_le _ _ (hPsm.mul (hdmcsm i)) (hMsm.mul (hdpcsm i)) θ r
      (real_two_factor_uniform_jet _ _ hPsm (hdmcsm i) θ J r hr hB.le hB.le hP (hdmc i))
      (real_two_factor_uniform_jet _ _ hMsm (hdpcsm i) θ J r hr hB.le hB.le hM (hdpc i))).trans_eq
      (by ring)
  · exact (real_difference_jet_le _ _ ((hmcsm i).mul (hdpcsm j)) ((hpcsm i).mul (hdmcsm j)) θ r
      (real_two_factor_uniform_jet _ _ (hmcsm i) (hdpcsm j) θ J r hr hB.le hB.le (hmc i) (hdpc j))
      (real_two_factor_uniform_jet _ _ (hpcsm i) (hdmcsm j) θ J r hr hB.le hB.le (hpc i) (hdmc j))).trans_eq
      (by ring)

end
end IsingBulk.Preferred22
