import IsingBulk.Anisotropic.RegularEdges.RootGap
import IsingBulk.Tail.ReciprocalProductJets
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Polynomial-in-particle-number derivatives of the singular reciprocal.
Unlike the numerator Cauchy estimate, this explicitly retains the pole gap. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Tail

 theorem one_sub_inverse_jet_norm (z : ℂ) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (fun w : ℂ => (1-w)⁻¹) z‖ =
      (k.factorial:ℝ)*(‖1-z‖⁻¹)^(k+1) := by
  have he : (fun w : ℂ => (1-w)⁻¹) = fun w => ((-1)*w+1)⁻¹ := by
    funext w
    congr 1
    ring
  rw [he, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    iter_deriv_inv_linear]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, mul_one, norm_zpow]
  rw [show (-1-(k:ℤ)) = -((k+1:ℕ):ℤ) by omega, zpow_neg, zpow_natCast, inv_pow]
  rw [show (-1:ℂ)*z+1=1-z by ring]

/-- Exact reciprocal gap plus bounded scalar-root jets give the required N^j
loss, not an exponential particle-number loss. -/
theorem reciprocal_product_gap_jets {N j : ℕ} {f : Fin N → ℂ → ℂ} {u : ℂ}
    {M d : ℝ} (hM : 1≤M) (hd : 0<d) (hd1 : d≤1)
    (ha : ∀ i, AnalyticAt ℂ (f i) u)
    (hj : ∀ i, ∀ k≤j, ‖iteratedFDeriv ℂ k (f i) u‖≤M^k)
    (hgap : d≤‖1-∏ i,f i u‖) :
    ‖iteratedFDeriv ℂ j (fun v => (1-∏ i,f i v)⁻¹) u‖≤
      (j.factorial:ℝ)^2*(d⁻¹)^(j+1)*(M*(N:ℝ))^j := by
  let F : ℂ → ℂ := fun v => ∏ i,f i v
  have hF : AnalyticAt ℂ F u := Finset.analyticAt_fun_prod _ (fun i _ => ha i)
  have hne : 1-F u≠0 := norm_pos_iff.mp (hd.trans_le hgap)
  have hout : AnalyticAt ℂ (fun w : ℂ => (1-w)⁻¹) (F u) :=
    (analyticAt_const.sub analyticAt_id).inv hne
  have hC (k : ℕ) (hk : k≤j) :
      ‖iteratedFDeriv ℂ k (fun w : ℂ => (1-w)⁻¹) (F u)‖≤
        (j.factorial:ℝ)*(d⁻¹)^(j+1) := by
    rw [one_sub_inverse_jet_norm]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hk
    · calc
        (‖1-F u‖⁻¹)^(k+1) ≤ (d⁻¹)^(k+1) := by
          gcongr
        _ ≤ (d⁻¹)^(j+1) := pow_le_pow_right₀ ((one_le_inv₀ hd).mpr hd1) (by omega)
    · positivity
    · positivity
  have hD (k : ℕ) (_hk : 1≤k) (hkj : k≤j) :
      ‖iteratedFDeriv ℂ k F u‖≤(M*(N:ℝ))^k := by
    have hh := analytic_finset_product_geometric_jets Finset.univ f u j 1 M
      (by norm_num) (by linarith) (fun i _ => ha i)
      (fun i _ k hk => by simpa using hj i k hk) k hkj
    simpa [F, mul_comm] using hh
  have hh := analytic_composition_geometric_jets (fun w : ℂ => (1-w)⁻¹) F u j hout hF
    ((j.factorial:ℝ)*(d⁻¹)^(j+1)) (M*(N:ℝ)) hC hD
  simpa only [F, Function.comp_def, pow_two, mul_assoc] using hh

end IsingBulk.Anisotropic.RegularEdges
