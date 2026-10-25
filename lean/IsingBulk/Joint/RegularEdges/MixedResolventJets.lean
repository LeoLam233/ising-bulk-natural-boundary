import IsingBulk.Joint.RegularEdges.CompactRootJets
import IsingBulk.Anisotropic.RegularEdges.ResolventJets
import IsingBulk.Analysis.JetsNormBounds

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Exact reciprocal gap plus bounded scalar-root jets give the required N^j
loss, not an exponential particle-number loss. -/
theorem reciprocal_product_gap_mixed_jets {N j : ℕ} {f : Fin N → E → ℂ} {u : E}
    {M d : ℝ} (hM : 1≤M) (hd : 0<d) (hd1 : d≤1)
    (ha : ∀ i, AnalyticAt ℂ (f i) u)
    (hj : ∀ i, ∀ k≤j, ‖iteratedFDeriv ℂ k (f i) u‖≤M^k)
    (hgap : d≤‖1-∏ i,f i u‖) :
    ‖iteratedFDeriv ℂ j (fun v => (1-∏ i,f i v)⁻¹) u‖≤
      (j.factorial:ℝ)^2*(d⁻¹)^(j+1)*(M*(N:ℝ))^j := by
  let F : E → ℂ := fun v => ∏ i,f i v
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


theorem affine_product_mixed_jet_bound (f g : E → ℂ) (u : E) (j : ℕ)
    (hf : AnalyticAt ℂ f u) (hg : AnalyticAt ℂ g u)
    {A D : ℝ} (hA : 0≤A) (hD : 0≤D)
    (hfj : ∀ k≤j, ‖iteratedFDeriv ℂ k f u‖≤A)
    (hgj : ∀ k≤j, ‖iteratedFDeriv ℂ k g u‖≤D) :
    ‖iteratedFDeriv ℂ j (fun v => 2*f v*g v-f v) u‖≤2^(j+1)*A*D+A := by
  have hp := IsingBulk.Jets.analytic_product_uniform_jet_bound f g u j j le_rfl hf hg
    A D hA hD hfj hgj
  have he : (fun v => (2:ℂ)*f v*g v-f v) =
      (fun v => (2:ℂ) • (f v*g v)-f v) := by funext v; simp only [smul_eq_mul]; ring
  rw [he]
  change ‖iteratedFDeriv ℂ j ((fun v => (2:ℂ) • (f v*g v))-f) u‖≤_
  have hfg : AnalyticAt ℂ (fun v => f v*g v) u := hf.mul hg
  have hs : ContDiffAt ℂ j (fun v => (2:ℂ) • (f v*g v)) u := hfg.contDiffAt.const_smul (2:ℂ)
  rw [iteratedFDeriv_sub_apply hs hf.contDiffAt,
    iteratedFDeriv_const_smul_apply' hfg.contDiffAt]
  calc
    _ ≤ ‖(2:ℂ) • iteratedFDeriv ℂ j (fun v => f v*g v) u‖+‖iteratedFDeriv ℂ j f u‖ := norm_sub_le _ _
    _ ≤ 2*(2^j*A*D)+A := by
      rw [norm_smul,Complex.norm_ofNat]
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)) (hfj j le_rfl)
    _ = _ := by rw [pow_succ]; ring

end
end IsingBulk.Joint.RegularEdges
