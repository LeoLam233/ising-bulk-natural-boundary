import IsingBulk.Anisotropic.RegularEdges.SingularJets
import IsingBulk.Anisotropic.RegularEdges.NumeratorJets

noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

/-- Algebraically rewritten full lattice multiplier. On its actual pole-free
locus this is numerator times `(1+Z)/(1-Z)`. -/
def edgeFullIntegrand {N : ℕ} (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (q : Fin N → ℝ) : ℂ :=
  2*edgeNumerator b B S u (List.ofFn q)*(1-edgeRootProduct b B u q)⁻¹ -
    edgeNumerator b B S u (List.ofFn q)

 theorem analytic_affine_product_jet_bound (f g : ℂ → ℂ) (u : ℂ) (j : ℕ)
    (hf : AnalyticAt ℂ f u) (hg : AnalyticAt ℂ g u)
    {A D : ℝ} (hA : 0≤A) (hD : 0≤D)
    (hfj : ∀ k≤j, ‖iteratedDeriv k f u‖≤A)
    (hgj : ∀ k≤j, ‖iteratedDeriv k g u‖≤D) :
    ‖iteratedDeriv j (fun v => 2*f v*g v-f v) u‖≤2^(j+1)*A*D+A := by
  have hp := IsingBulk.Jets.analytic_product_uniform_jet_bound f g u j j le_rfl hf hg
    A D hA hD (fun k hk => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hfj k hk)
    (fun k hk => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hgj k hk)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hp
  have he : (fun v => (2:ℂ)*f v*g v-f v) =
      (fun v => (2:ℂ)*(f v*g v)-f v) := by funext v; ring
  rw [he, iteratedDeriv_fun_sub (f := fun v => (2:ℂ)*(f v*g v)) (g := f)
    ((analyticAt_const.mul (hf.mul hg)).contDiffAt)
    hf.contDiffAt, iteratedDeriv_const_mul_field]
  calc
    _ ≤ ‖(2:ℂ)*iteratedDeriv j (fun v => f v*g v) u‖+‖iteratedDeriv j f u‖ := norm_sub_le _ _
    _ ≤ 2*(2^j*A*D)+A := by
      rw [norm_mul, Complex.norm_ofNat]
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)) (hfj j le_rfl)
    _ = _ := by rw [pow_succ]; ring

end IsingBulk.Anisotropic.RegularEdges
