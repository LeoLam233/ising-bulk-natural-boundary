import IsingBulk.Anisotropic.NegativeDominance.UniformRootLipschitz
import IsingBulk.Anisotropic.NegativeDominance.ProductPerturbation

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- A genuine angular boundary gap persists on one particle-scale complex
disk a/N. The root continuation and the perturbation estimate are derived. -/
theorem edgeRootProduct_disk_of_boundary_gap {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0) (κ : ℝ) (hκ : 0<κ) :
    ∃a : ℝ,0<a ∧ ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) → κ≤‖1-edgeRootProduct b B 0 q‖ →
      ∀u : ℂ,‖u‖<a/(N : ℝ) →
      (∀i,AnalyticAt ℂ (fun w=>edgeParamRoot b B w (q i)) u) ∧
      κ/2≤‖1-edgeRootProduct b B u q‖ := by
  obtain ⟨δ,L,hδ,hL,hroot⟩ := edgeParamRoot_uniform_lipschitz_zero hb hB hBa
  let E := Real.exp 1
  have hE : 0<E := Real.exp_pos _
  have hE1 : 1≤E := Real.one_le_exp_iff.mpr (by norm_num)
  let a := min δ (min (1/(E*L)) (κ/(2*E*L)))
  have ha : 0<a := lt_min hδ (lt_min (by positivity) (by positivity))
  have haδ : a≤δ := min_le_left _ _
  have ha1 : a≤1/(E*L) := (min_le_right _ _).trans (min_le_left _ _)
  have haκ : a≤κ/(2*E*L) := (min_le_right _ _).trans (min_le_right _ _)
  have hELa : E*L*a≤1 := by have hh := (le_div_iff₀ (mul_pos hE hL)).mp ha1; nlinarith
  have hELκ : E*L*a≤κ/2 := by have hh := (le_div_iff₀ (by positivity : 0<2*E*L)).mp haκ; nlinarith
  refine ⟨a,ha,?_⟩
  intro N hN q hq hgap u hu
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hscale : (N : ℝ)*‖u‖≤a := by have hh := (lt_div_iff₀ hNp).mp hu; nlinarith
  have hau : a/(N : ℝ)≤a := (div_le_iff₀ hNp).mpr (by nlinarith)
  have huδ : ‖u‖<δ := hu.trans_le (hau.trans haδ)
  have hNd : (N : ℝ)*(L*‖u‖)≤1 := by
    have hh := mul_le_mul_of_nonneg_left hscale hL.le
    have he := mul_le_mul_of_nonneg_right hE1 (show 0≤L*a by positivity)
    nlinarith
  have hbase (i : Fin N) : ‖edgeParamRoot b B 0 (q i)‖≤1 := by
    simpa only [edgeParamRoot_zero] using (edgeRoot_bounds hb hB (q i)).1
  have hdif (i : Fin N) : ‖edgeParamRoot b B u (q i)-edgeParamRoot b B 0 (q i)‖≤L*‖u‖ :=
    (hroot u huδ (q i) (hq i)).2
  have hp := norm_prod_perturbation_linear (fun i=>edgeParamRoot b B u (q i))
    (fun i=>edgeParamRoot b B 0 (q i)) (by positivity : 0≤L*‖u‖) hNd hbase hdif
  have herr : E*(N : ℝ)*(L*‖u‖)≤κ/2 := by
    have hh := mul_le_mul_of_nonneg_left hscale (mul_pos hE hL).le
    nlinarith
  have htri := norm_add_le
    (edgeRootProduct b B u q-edgeRootProduct b B 0 q) (1-edgeRootProduct b B u q)
  rw [show (edgeRootProduct b B u q-edgeRootProduct b B 0 q)+(1-edgeRootProduct b B u q)=
    1-edgeRootProduct b B 0 q by ring] at htri
  change ‖edgeRootProduct b B u q-edgeRootProduct b B 0 q‖≤E*(N : ℝ)*(L*‖u‖) at hp
  exact ⟨fun i=>(hroot u huδ (q i) (hq i)).1,by linarith⟩

end
end IsingBulk.Anisotropic.NegativeDominance
