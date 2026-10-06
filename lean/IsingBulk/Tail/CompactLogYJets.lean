import IsingBulk.Tail.CompactPhaseSymmetry

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

lemma retractionShift_normalized {N : ℕ} (f : SelectorFunctions) (tau : ℝ)
    (theta : Fin N → ℝ) (i : Fin N) :
    retractionShift tau (fun k => f.p (theta k)) (fun k => f.m (theta k)) i =
      tau*normalizedRetractionShift N f.p f.m i theta := by
  unfold retractionShift normalizedRetractionShift normalizedAngularOccupancy occupancy
  ring

def logYBaseline (N : ℕ) (theta : Fin N → ℝ) : ℂ := Complex.I*∑ i, (theta i:ℂ)

/-- All fixed positive angular orders. The entire coupled occupancy is
retained; the real constant N log r has zero positive-order jets. -/
theorem unwrappedLogY_positive_jet_perturbation (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi))
    (j : ℕ) (hj : 0<j) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N → ∀ r tau lam : ℝ,
      0≤tau → tau≤1 → 0≤lam → ∀ theta : Fin N → ℝ,
      ‖iteratedFDeriv ℝ j (unwrappedLogY f r tau lam) theta-
        iteratedFDeriv ℝ j (logYBaseline N) theta‖ ≤ C*N*lam := by
  obtain ⟨C,hC,hbound⟩ := periodic_retraction_jet_bound f.p f.m hp hm hpper hmper j
  refine ⟨C,hC,?_⟩
  intro N hN r tau lam ht ht1 hl theta
  let R : (Fin N → ℝ) → ℝ := fun x => ∑ i, (Real.log r+lam*tau*normalizedRetractionShift N f.p f.m i x)
  have hRs : ContDiff ℝ ∞ R := ContDiff.sum (fun i _ => contDiff_const.add
    ((normalizedRetractionShift_smooth N f.p f.m hp hm i).const_smul (lam*tau)))
  have hbase : ContDiff ℝ ∞ (logYBaseline N) := by
    unfold logYBaseline
    apply contDiff_const.mul
    exact ContDiff.sum (fun i _ => Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))
  have hRc : ContDiff ℝ ∞ (fun x => (R x:ℂ)) := Complex.ofRealCLM.contDiff.comp hRs
  have he : unwrappedLogY f r tau lam = fun x => (R x:ℂ)+logYBaseline N x := by
    funext x
    unfold unwrappedLogY logYBaseline
    rw [← Complex.ofReal_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    rw [retractionShift_normalized]
    ring
  rw [he,fun_iteratedFDeriv_add_apply
    (hRc.of_le (by simp)).contDiffAt
    (hbase.of_le (by simp)).contDiffAt,add_sub_cancel_right]
  have hcast := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := theta) hRs.contDiffAt (by simp : (j:ℕ∞ω)≤∞)
  have hCLM : ‖Complex.ofRealCLM‖ ≤ 1 :=
    Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)
  apply (hcast.trans (mul_le_of_le_one_left (norm_nonneg _) hCLM)).trans
  have hri (i : Fin N) : ContDiff ℝ ∞ (fun x => Real.log r+lam*tau*normalizedRetractionShift N f.p f.m i x) :=
    contDiff_const.add ((normalizedRetractionShift_smooth N f.p f.m hp hm i).const_smul (lam*tau))
  have hjbound (i : Fin N) :
      ‖iteratedFDeriv ℝ j (fun x => Real.log r+lam*tau*normalizedRetractionShift N f.p f.m i x) theta‖ ≤ lam*tau*C := by
    have hmuli : ContDiff ℝ ∞ (fun x => lam*tau*normalizedRetractionShift N f.p f.m i x) :=
      (normalizedRetractionShift_smooth N f.p f.m hp hm i).const_smul (lam*tau)
    rw [fun_iteratedFDeriv_add_apply (f := fun _ => Real.log r) contDiffAt_const
      (hmuli.of_le (by simp)).contDiffAt,
      iteratedFDeriv_const_of_ne (by omega : j≠0),Pi.zero_apply,zero_add]
    change ‖iteratedFDeriv ℝ j (fun x => (lam*tau) • normalizedRetractionShift N f.p f.m i x) theta‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply'
      ((normalizedRetractionShift_smooth N f.p f.m hp hm i).of_le (by simp)).contDiffAt,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hl ht)]
    exact mul_le_mul_of_nonneg_left (hbound N hN i theta) (mul_nonneg hl ht)
  dsimp only [R]
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hri i).of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ i : Fin N, ‖iteratedFDeriv ℝ j (fun x => Real.log r+lam*tau*normalizedRetractionShift N f.p f.m i x) theta‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, lam*tau*C := Finset.sum_le_sum (fun i _ => hjbound i)
    _ = C*N*(lam*tau) := by simp; ring
    _ ≤ C*N*lam := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hl ht1) (by positivity)

end
end IsingBulk.Tail
