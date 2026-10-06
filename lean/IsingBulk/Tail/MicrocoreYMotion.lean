import IsingBulk.Tail.MicrocoreAmplitudeBound
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual regular Y-product parameter motion with scalar constants chosen
before N. This is used to protect the algebraic Y-gap while phases are fixed. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Filter Metric
open scoped BigOperators Topology

theorem regularY_parameter_uniform (s₀ : ℂ) (c : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ s φ : ℂ, ‖s-s₀‖ < r → ‖φ‖ < r →
      AnalyticAt ℂ (fun t : ℂ × ℂ => regularY t.1 t.2) (s,φ) ∧
      ‖regularY s φ‖ ≤ C ∧ ‖deriv (fun t => regularY t φ) s‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := finite_family_jet_bounds
    (fun _ : Fin 1 => fun t : ℂ × ℂ => regularY t.1 t.2) (s₀,0)
    (fun _ => regularY_analytic_base s₀ c hs hS hc) 1
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨C,r,hC,hr,?_⟩
  intro s φ hsr hφ
  have hd : dist (s,φ) (s₀,0)<r := by simpa [Prod.dist_eq,dist_eq_norm] using And.intro hsr hφ
  have hj := hball hd (0:Fin 1)
  refine ⟨hj.analytic,?_,?_⟩
  · simpa using hj.bound 0 (by omega)
  · have hdiff := hj.analytic.differentiableAt.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s φ))
    have hdiff' : HasDerivAt (fun t => regularY t φ)
        (fderiv ℂ (fun t : ℂ × ℂ => regularY t.1 t.2) (s,φ) (1,0)) s := by
      convert! hdiff using 1
    rw [hdiff'.deriv]
    have hh := (fderiv ℂ (fun t : ℂ × ℂ => regularY t.1 t.2) (s,φ)).le_opNorm (1,0)
    norm_num at hh
    exact hh.trans (by simpa only [norm_iteratedFDeriv_one] using hj.bound 1 le_rfl)

theorem parameter_product_derivative_bound {N : ℕ} (f : Fin N → ℂ → ℂ) (s : ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, DifferentiableAt ℂ (f i) s)
    (hv : ∀ i, ‖f i s‖ ≤ C) (hd : ∀ i, ‖deriv (f i) s‖ ≤ C) :
    ‖deriv (fun t => ∏ i, f i t) s‖ ≤ (N:ℝ)*C^N := by
  rw [deriv_fun_finsetProd (fun i _ => hf i)]
  simp only [smul_eq_mul]
  apply (norm_sum_le _ _).trans
  calc
    (∑ i, ‖(∏ j ∈ Finset.univ.erase i, f j s)*deriv (f i) s‖) ≤
        ∑ _i : Fin N, C^N := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_prod]
      have hp : (∏ j ∈ Finset.univ.erase i, ‖f j s‖) ≤ C^(N-1) := by
        have hh : (∏ j ∈ Finset.univ.erase i, ‖f j s‖) ≤ ∏ _j ∈ Finset.univ.erase i, C := by
          gcongr
          exact hv _
        simpa only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin] using hh
      have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
      calc
        _ ≤ C^(N-1)*C := mul_le_mul hp (hd i) (norm_nonneg _) (pow_nonneg hC _)
        _ = C^N := by rw [← pow_succ]; congr 1; omega
    _ = _ := by simp

theorem regularY_product_motion_uniform (s₀ : ℂ) (c : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ N : ℕ, ∀ φ : Fin N → ℂ,
      (∀ i, ‖φ i‖ < r) → ∀ s t : ℂ, ‖s-s₀‖ < r → ‖t-s₀‖ < r →
      ‖regularYProduct t φ-regularYProduct s φ‖ ≤ (N:ℝ)*C^N*‖t-s‖ := by
  obtain ⟨C,r,hC,hr,hbound⟩ := regularY_parameter_uniform s₀ c hs hS hc
  refine ⟨C,r,hC,hr,?_⟩
  intro N φ hφ s t hs' ht'
  have hdiff : ∀ z ∈ ball s₀ r, ∀ i, DifferentiableAt ℂ (fun t => regularY t (φ i)) z := by
    intro z hz i
    have ha := (hbound z (φ i) (by simpa [mem_ball,dist_eq_norm] using hz) (hφ i)).1
    have hh := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_id z).prodMk (hasDerivAt_const z (φ i)))
    convert! hh.differentiableAt using 1
  have hdf : ∀ z ∈ ball s₀ r, DifferentiableAt ℂ (fun t => regularYProduct t φ) z := by
    intro z hz
    have hh := (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun i _ => (hdiff z hz i).hasDerivAt)).differentiableAt
    convert! hh using 1
  have hdb : ∀ z ∈ ball s₀ r, ‖deriv (fun t => regularYProduct t φ) z‖ ≤ (N:ℝ)*C^N := by
    intro z hz
    have hh := parameter_product_derivative_bound (fun i t => regularY t (φ i)) z C
      (by linarith) (hdiff z hz)
      (fun i => (hbound z (φ i) (by simpa [mem_ball,dist_eq_norm] using hz) (hφ i)).2.1)
      (fun i => (hbound z (φ i) (by simpa [mem_ball,dist_eq_norm] using hz) (hφ i)).2.2)
    convert! hh using 1
  exact Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
    (f := fun t : ℂ => regularYProduct t φ) (s := ball s₀ r) (x := s) (y := t) hdf hdb
    (convex_ball s₀ r) (by simpa [mem_ball,dist_eq_norm] using hs')
    (by simpa [mem_ball,dist_eq_norm] using ht')


end
end IsingBulk.Tail
