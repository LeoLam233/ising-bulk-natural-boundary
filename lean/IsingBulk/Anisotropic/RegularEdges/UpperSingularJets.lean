import IsingBulk.Anisotropic.RegularEdges.SingularJets
import IsingBulk.Anisotropic.RegularEdges.UpperProductGap
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges
theorem edgeReciprocal_retained_jets_upper {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0) (j : ℕ) :
    ∃ δ A : ℝ, 0<δ ∧ 0<A ∧ ∀ v : ℂ, 0<v.im → ‖v‖<δ →
      ∀ (N m : ℕ) [Nonempty (Fin m)] (q : Fin N → ℝ) (p : Fin m → Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → (fun i => q (p i))≠0 →
      ‖iteratedDeriv j (fun u => (1-edgeRootProduct b B u q)⁻¹) v‖≤
        A*(N:ℝ)^j*‖fun i => q (p i)‖^(-(2*(j+1):ℝ)) := by
  obtain ⟨η,M,hη,hM,hjet⟩ := edgeParamRoot_inward_geometric_jets hb hB hc j
  obtain ⟨c,δ,hcpos,hδ,hgap⟩ := edgeRootProduct_retained_gap_upper (b := b) hB hc.continuousAt
  refine ⟨min η δ,(j.factorial:ℝ)^2*(c⁻¹)^(j+1)*M^j,
    lt_min hη hδ,by positivity,?_⟩
  intro v hε hεδ N m _ q p hq hq0
  have hun : ‖v‖<η := by
    exact hεδ.trans_le (min_le_left _ _)
  have him : 0<v.im := hε
  have hroots := fun i => hjet _ hun him (q i) (hq i)
  have hg := hgap v hε (hεδ.trans_le (min_le_right _ _)) N m q p hq
  have hh := reciprocal_product_gap_jets hM hg.1 hg.2.1
    (fun i => (hroots i).1) (fun i k hk => (hroots i).2 k hk) hg.2.2
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  have hn : 0<‖fun i => q (p i)‖ := norm_pos_iff.mpr hq0
  have hinv : (c*(v.im+‖fun i => q (p i)‖^2))⁻¹ ≤
      (c*‖fun i => q (p i)‖^2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith
  calc
    _ ≤ (j.factorial:ℝ)^2*(c*(v.im+‖fun i => q (p i)‖^2))⁻¹^(j+1)*(M*(N:ℝ))^j := hh
    _ ≤ (j.factorial:ℝ)^2*(c*‖fun i => q (p i)‖^2)⁻¹^(j+1)*(M*(N:ℝ))^j := by gcongr
    _ = _ := by
      rw [mul_inv_rev, mul_pow, mul_pow, inverse_square_power_eq_rpow _ hn.le]
      ring

theorem edgeReciprocal_retained_jets_up_to_upper {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0) (j : ℕ) :
    ∃ δ A : ℝ, 0<δ ∧ 0<A ∧ ∀ v : ℂ, 0<v.im → ‖v‖<δ →
      ∀ (N m : ℕ) [Nonempty (Fin m)] (q : Fin N → ℝ) (p : Fin m → Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → (fun i => q (p i))≠0 →
      ∀ k≤j, ‖iteratedDeriv k (fun u => (1-edgeRootProduct b B u q)⁻¹) v‖≤
        A*(N:ℝ)^j*‖fun i => q (p i)‖^(-(2*(j+1):ℝ)) := by
  obtain ⟨η,M,hη,hM,hjet⟩ := edgeParamRoot_inward_geometric_jets hb hB hc j
  obtain ⟨c,δ,hcpos,hδ,hgap⟩ := edgeRootProduct_retained_gap_upper (b := b) hB hc.continuousAt
  refine ⟨min η δ,(j.factorial:ℝ)^2*(c⁻¹)^(j+1)*M^j,
    lt_min hη hδ,by positivity,?_⟩
  intro v hε hεδ N m _ q p hq hq0 k hk
  have hun : ‖v‖<η := by
    exact hεδ.trans_le (min_le_left _ _)
  have him : 0<v.im := hε
  have hroots := fun i => hjet _ hun him (q i) (hq i)
  have hg := hgap v hε (hεδ.trans_le (min_le_right _ _)) N m q p hq
  have hh := reciprocal_product_gap_jets hM hg.1 hg.2.1
    (fun i => (hroots i).1) (fun i a ha => (hroots i).2 a (ha.trans hk)) hg.2.2
  have hN : 1≤(N:ℝ) := by
    have hn := (p (Classical.arbitrary (Fin m))).isLt
    exact_mod_cast (show 1≤N by omega)
  have hd1 : 1≤(c*(v.im+‖fun i => q (p i)‖^2))⁻¹ := (one_le_inv₀ hg.1).mpr hg.2.1
  have hMN : 1≤M*(N:ℝ) := by nlinarith
  have hh' : ‖iteratedFDeriv ℂ k (fun v => (1-edgeRootProduct b B v q)⁻¹) v‖≤
      (j.factorial:ℝ)^2*(c*(v.im+‖fun i => q (p i)‖^2))⁻¹^(j+1)*(M*(N:ℝ))^j := by
    apply hh.trans
    gcongr
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh'
  have hn : 0<‖fun i => q (p i)‖ := norm_pos_iff.mpr hq0
  have hinv : (c*(v.im+‖fun i => q (p i)‖^2))⁻¹ ≤
      (c*‖fun i => q (p i)‖^2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith
  calc
    _ ≤ (j.factorial:ℝ)^2*(c*(v.im+‖fun i => q (p i)‖^2))⁻¹^(j+1)*(M*(N:ℝ))^j := hh'
    _ ≤ (j.factorial:ℝ)^2*(c*‖fun i => q (p i)‖^2)⁻¹^(j+1)*(M*(N:ℝ))^j := by gcongr
    _ = _ := by
      rw [mul_inv_rev, mul_pow, mul_pow, inverse_square_power_eq_rpow _ hn.le]
      ring


end IsingBulk.Anisotropic.RegularEdges
