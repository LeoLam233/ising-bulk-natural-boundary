import IsingBulk.Anisotropic.NegativeDominance.NegativePhysicalSheet
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

theorem analytic_normalized_deriv_bound {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ j : ℕ,
      ‖iteratedDeriv j f z/(j.factorial : ℂ)‖*r^j≤C := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun j => iteratedDeriv j f z/(j.factorial : ℂ))
  have hp : 0<p.radius := hf.hasFPowerSeriesAt.radius_pos
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  obtain ⟨C, hC, hb⟩ := p.norm_mul_pow_le_of_lt_radius hr
  refine ⟨r, C, ?_, hC, ?_⟩
  · exact_mod_cast hr0
  · intro j
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using hb j

/-- A common Cauchy/geometric bound for an arbitrary finite collection of
actual analytic germs, controlling the sum of moduli rather than only the
modulus of their sum. -/
theorem finite_analytic_normalized_deriv_bound {ι : Type*} (S : Finset ι)
    (f : ι → ℂ → ℂ) (z : ℂ) (hf : ∀ i∈S, AnalyticAt ℂ (f i) z) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ j : ℕ,
      (∑ i∈S, ‖iteratedDeriv j (f i) z/(j.factorial : ℂ)‖)*r^j≤C := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,1,by norm_num,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨r,C,hr,hC,hb⟩ := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    obtain ⟨s,D,hs,hD,hd⟩ := analytic_normalized_deriv_bound (hf i (Finset.mem_insert_self _ _))
    refine ⟨min r s,C+D,lt_min hr hs,add_pos hC hD,?_⟩
    intro j
    rw [Finset.sum_insert hi, add_mul]
    have h1 := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hr.le hs.le) (min_le_left r s) j)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).trans (hb j)
    have h2 := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hr.le hs.le) (min_le_right r s) j)
      (norm_nonneg _)).trans (hd j)
    linarith only [h1,h2]

/-- Genuine finite low-particle Cauchy bound at a regular negative endpoint.
The family consists of the literal normalized angular continuation integrals. -/
theorem finite_odd_continuedAngularCoefficient_bound (S : Finset ℕ)
    (hodd : ∀ n∈S, Odd (n+1)) {lam b : ℝ} {z : ℂ}
    (hS : spectralS z≠0)
    (hedge : spectralA lam z+spectralT lam z=
      (b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ j : ℕ,
      (∑ n∈S, ‖iteratedDeriv j (continuedAngularCoefficient n lam) z/(j.factorial : ℂ)‖)*r^j≤C :=
  finite_analytic_normalized_deriv_bound S (fun n => continuedAngularCoefficient n lam) z
    (fun n hn => continuedAngularCoefficient_negative_analyticAt n (hodd n hn) hS hedge hb hB)

end
end IsingBulk.Anisotropic.NegativeDominance
