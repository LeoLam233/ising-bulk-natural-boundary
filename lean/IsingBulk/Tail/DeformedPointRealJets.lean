import IsingBulk.Tail.RealCompositionJets
import IsingBulk.Tail.CompactPhaseJointJets
import IsingBulk.Tail.SelectorHypotheses
import IsingBulk.Tail.CompactSourceSmooth

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped Topology ContDiff
set_option maxHeartbeats 1800000

/-- The literal coupled contour coordinates have bounded real jets of every
fixed order, uniformly in particle number and all angles. -/
theorem deformedPoint_real_finite_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ r → r ≤ 1 → 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ i : Fin N, ∀ θ : Fin N → ℝ, ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (fun x => deformedPoint f r τ lam x i) θ‖ ≤ C := by
  obtain ⟨A,hA,hret⟩ := periodic_retraction_finite_jets f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic J
  let C := (J.factorial:ℝ)*Real.exp A*(1+A)^J
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i θ k hk
  let R := normalizedRetractionShift N f.p f.m i
  have hR : ContDiff ℝ ∞ R := normalizedRetractionShift_smooth N f.p f.m hf.p_smooth hf.m_smooth i
  let L : (Fin N → ℝ) →L[ℝ] ℂ := Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by
    simpa [L] using norm_le_pi_norm x i)
  let g : (Fin N → ℝ) → ℂ := fun x => L x+((lam*τ:ℝ):ℂ)*(R x:ℂ)
  have hRc : ContDiff ℝ ∞ (fun x => (R x:ℂ)) := Complex.ofRealCLM.contDiff.comp hR
  have hg : ContDiff ℝ ∞ g := L.contDiff.add (hRc.const_smul ((lam*τ:ℝ):ℂ))
  have hlt0 : 0 ≤ lam*τ := mul_nonneg hlam hτ
  have hlt1 : lam*τ ≤ 1 := (mul_le_of_le_one_right hlam hτ1).trans hlam1
  have hRbound (m : ℕ) (hm : m ≤ J) : ‖iteratedFDeriv ℝ m (fun x => (R x:ℂ)) θ‖ ≤ A := by
    have hh := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := θ) hR.contDiffAt
      (by simp : (m:ℕ∞ω) ≤ ∞)
    have hc : ‖Complex.ofRealCLM‖ ≤ 1 := Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)
    exact (hh.trans (mul_le_of_le_one_left (norm_nonneg _) hc)).trans (hret N hN i θ m hm)
  have hgj : ∀ m, 1 ≤ m → m ≤ J → ‖iteratedFDeriv ℝ m g θ‖ ≤ 1+A := by
    intro m hm hmJ
    change ‖iteratedFDeriv ℝ m (fun x => L x+((lam*τ:ℝ):ℂ) • (R x:ℂ)) θ‖ ≤ _
    rw [fun_iteratedFDeriv_add_apply (L.contDiff.of_le (show (m:ℕ∞ω) ≤ ∞ by simp)).contDiffAt
      ((hRc.const_smul ((lam*τ:ℝ):ℂ)).of_le (show (m:ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
      iteratedFDeriv_const_smul_apply' (hRc.of_le (show (m:ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
    apply (norm_add_le _ _).trans
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlt0]
    apply add_le_add (positive_linear_jet_bound L hL θ m hm)
    exact (mul_le_mul_of_nonneg_left (hRbound m hmJ) hlt0).trans
      (mul_le_of_le_one_left (by linarith : 0 ≤ A) hlt1)
  have hge : ‖Complex.exp (g θ)‖ ≤ Real.exp A := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hb := hret N hN i θ 0 (Nat.zero_le J)
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
    have hb' : R θ ≤ A := (le_abs_self _).trans hb
    have hm := (mul_le_mul_of_nonneg_left hb' hlt0).trans
      (mul_le_of_le_one_left (by linarith : 0 ≤ A) hlt1)
    simpa [g,L,Complex.mul_re] using hm
  have hb := real_cexp_uniform_jets g θ J (Real.exp A) (1+A) hg.contDiffAt (Real.exp_pos _).le
    (by linarith) hge hgj k hk
  have he : (fun x => deformedPoint f r τ lam x i)=(fun x => (r:ℂ) • Complex.exp (g x)) := by
    funext x
    unfold deformedPoint
    rw [retractionShift_normalized]
    simp only [g,L,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
    congr 2
    ring
  rw [he,iteratedFDeriv_const_smul_apply' (hg.cexp.of_le (by simp)).contDiffAt,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left hb hr).trans (mul_le_of_le_one_left hC.le hr1)

theorem deformedPoint_joint_finite_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ r → r ≤ 1 → 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ i : Fin N, ∀ p : ℂ × (Fin N → ℝ), ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (fun q : ℂ × (Fin N → ℝ) => deformedPoint f r τ lam q.2 i) p‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := deformedPoint_real_finite_jets f hf J
  refine ⟨C,hC,?_⟩
  intro N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i p k hk
  let L := ContinuousLinearMap.snd ℝ ℂ (Fin N → ℝ)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by simpa [L] using norm_snd_le x)
  exact (jet_comp_contraction_right L hL _
    (deformedPoint_fixed_contDiff f r τ lam hf.p_smooth hf.m_smooth i) p k).trans
    (hb N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i p.2 k hk)

end
end IsingBulk.Tail
