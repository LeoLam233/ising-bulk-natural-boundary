import IsingBulk.Anisotropic.NegativeDominance.NonresonantBoundaryCauchy
import IsingBulk.Anisotropic.NegativeDominance.ParticleCauchyGaussian

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open RegularEdges

/-- Normalize the actual derivative Cauchy estimate without losing any factor
of N or of the Taylor order. -/
theorem normalized_cauchy_coefficient {z : ℂ} {j N : ℕ} {a H : ℝ}
    (ha : 0<a) (hN : 0<N)
    (hz : ‖z‖≤(j.factorial : ℝ)*H/(a/(N : ℝ))^j) :
    ‖z/(j.factorial : ℂ)‖≤H*((N : ℝ)/a)^j := by
  have hjne : (j.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hNne : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hz (by positivity : 0≤(j.factorial : ℝ))).trans_eq
  rw [div_pow,div_pow]
  field_simp [ha.ne',hjne,hNne]

/-- The literal all-index nonresonant physical Cauchy estimate implies one
common sharp Gaussian envelope, before every particle and Taylor order. -/
theorem nonresonant_cauchy_gaussian {a r C M K : ℝ}
    (ha : 0<a) (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (hK : 0<K)
    (p : ℕ) (g : ℕ→ℂ→ℂ)
    (hcauchy : ∀j n : ℕ,Odd (n+1) → ¬p∣n+1 →
      ‖iteratedDeriv j (g n) 0‖≤(j.factorial : ℝ)*(K*particleEdgeMajorant r C M (n+1))/(a/((n+1 : ℕ) : ℝ))^j) :
    ∃aG CG : ℝ,0<aG ∧ 0<CG ∧ ∀j n : ℕ,Odd (n+1) → ¬p∣n+1 →
      ‖iteratedDeriv j (g n) 0/(j.factorial : ℂ)‖≤
        Real.exp (-aG*((n+1 : ℕ) : ℝ)^2+((j : ℝ)+1)*Real.log (n+1)+CG*((j : ℝ)+1)) := by
  obtain ⟨aG,CG,haG,hCG,hbound⟩ := particle_cauchy_gaussian_bound hr hr1 hC hM ha hK
  refine ⟨aG,CG,haG,hCG,fun j n hn hres=>?_⟩
  have hh := normalized_cauchy_coefficient ha (Nat.succ_pos n) (hcauchy j n hn hres)
  simpa only [Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one] using hh.trans (hbound (n+1) (by omega) j)

end
end IsingBulk.Anisotropic.NegativeDominance
