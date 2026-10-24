import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueFactorization
import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueSlopeUniform
import IsingBulk.Anisotropic.NegativeNormalForm.RelativeDensityAlgebra

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

 theorem real_exp_error_envelope (a : ℝ) : Real.exp a-1≤a*Real.exp a := by
  have h := Real.add_one_le_exp (-a)
  rw [Real.exp_neg,inv_eq_one_div] at h
  have hh := (le_div_iff₀ (Real.exp_pos a)).mp h
  nlinarith

 theorem scalar_relative_envelope (z : ℂ) (a : ℝ) (ha : 0≤a) (hz : ‖z-1‖≤a) :
    ‖z‖≤Real.exp a ∧ ‖z-1‖≤a*Real.exp a := by
  constructor
  · have h := norm_le_norm_sub_add z (1:ℂ)
    rw [norm_one] at h
    exact (h.trans (by linarith)).trans (Real.add_one_le_exp a)
  · exact hz.trans (le_mul_of_one_le_right ha (Real.one_le_exp_iff.mpr ha))

 theorem finite_product_relative_envelope {ι : Type*} (s : Finset ι) (f : ι→ℂ)
    (a : ℝ) (hsum : (∑i∈s,‖f i-1‖)≤a) :
    ‖∏i∈s,f i‖≤Real.exp a ∧ ‖(∏i∈s,f i)-1‖≤a*Real.exp a := by
  have he : ‖(∏i∈s,f i)-1‖≤Real.exp a-1 :=
    (finite_product_relative_error s f).trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)
  constructor
  · have h := norm_le_norm_sub_add (∏i∈s,f i) (1:ℂ)
    rw [norm_one] at h
    linarith
  · exact he.trans (real_exp_error_envelope a)

 theorem power_relative_envelope (z : ℂ) (a : ℝ) (k : ℕ) (hz : ‖z-1‖≤a) :
    ‖z^k‖≤Real.exp ((k:ℝ)*a) ∧ ‖z^k-1‖≤((k:ℝ)*a)*Real.exp ((k:ℝ)*a) := by
  have hsum : (∑_i:Fin k,‖z-1‖)≤(k:ℝ)*a := by
    simpa using mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg k)
  simpa using finite_product_relative_envelope (Finset.univ : Finset (Fin k)) (fun _ => z) ((k:ℝ)*a) hsum

 theorem residue_oneBody_error_sum {n : ℕ} (v : Config n) (F : Fin n→ℂ)
    (K e d : ℝ) (hK : 0≤K) (hd : 0≤d)
    (hF : ∀i,‖F i-1‖≤K*(e+(d+‖v i‖)*‖v i‖)) :
    (∑i,‖F i-1‖)≤K*((n:ℝ)*e+d*Real.sqrt ((n:ℝ)*absoluteEnergy v)+absoluteEnergy v) := by
  calc
    _ ≤ ∑i,K*(e+(d+‖v i‖)*‖v i‖) := Finset.sum_le_sum (fun i _ => hF i)
    _ = K*((n:ℝ)*e+d*(∑i,‖v i‖)+absoluteEnergy v) := by
      simp only [mul_add,add_mul,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,absoluteEnergy,pow_two]
      ring
    _ ≤ _ := by gcongr; exact sum_norm_le_sqrt_energy v

 theorem exponential_envelope_mono (z : ℂ) {a b : ℝ} (ha : 0≤a) (hab : a≤b)
    (hn : ‖z‖≤Real.exp a) (he : ‖z-1‖≤a*Real.exp a) :
    ‖z‖≤Real.exp b ∧ ‖z-1‖≤b*Real.exp b := by
  exact ⟨hn.trans (Real.exp_le_exp.mpr hab),he.trans
    (mul_le_mul hab (Real.exp_le_exp.mpr hab) (Real.exp_pos a).le (ha.trans hab))⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
