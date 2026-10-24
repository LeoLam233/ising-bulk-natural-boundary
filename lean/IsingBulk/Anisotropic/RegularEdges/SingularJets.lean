import IsingBulk.Anisotropic.RegularEdges.RootJets
import IsingBulk.Anisotropic.RegularEdges.ProductGap
import IsingBulk.Anisotropic.RegularEdges.RetainedDimension

noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

 theorem inverse_square_power_eq_rpow (x : ℝ) (hx : 0≤x) (j : ℕ) :
    (x^2)⁻¹^(j+1)=x^(-(2*(j+1):ℝ)) := by
  rw [show -(2*(j+1):ℝ) = -((2*(j+1):ℕ):ℝ) by push_cast; ring,
    Real.rpow_neg hx, Real.rpow_natCast, pow_mul, inv_pow]

/-- The literal full root-product reciprocal has an integrable retained-angle
majorant with exactly the polynomial particle-number derivative loss. -/
theorem edgeReciprocal_retained_jets {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0) (j : ℕ) :
    ∃ δ A : ℝ, 0<δ ∧ 0<A ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      ∀ (N m : ℕ) [Nonempty (Fin m)] (q : Fin N → ℝ) (p : Fin m → Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → (fun i => q (p i))≠0 →
      ‖iteratedDeriv j (fun u => (1-edgeRootProduct b B u q)⁻¹) (Complex.I*(ε:ℂ))‖≤
        A*(N:ℝ)^j*‖fun i => q (p i)‖^(-(2*(j+1):ℝ)) := by
  obtain ⟨η,M,hη,hM,hjet⟩ := edgeParamRoot_inward_geometric_jets hb hB hc j
  obtain ⟨c,δ,hcpos,hδ,hgap⟩ := edgeRootProduct_retained_gap (b := b) hB hc.continuousAt
  refine ⟨min η δ,(j.factorial:ℝ)^2*(c⁻¹)^(j+1)*M^j,
    lt_min hη hδ,by positivity,?_⟩
  intro ε hε hεδ N m _ q p hq hq0
  have hun : ‖Complex.I*(ε:ℂ)‖<η := by
    simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hε] using hεδ.trans_le (min_le_left _ _)
  have him : 0<(Complex.I*(ε:ℂ)).im := by simpa using hε
  have hroots := fun i => hjet _ hun him (q i) (hq i)
  have hg := hgap ε hε (hεδ.trans_le (min_le_right _ _)) N m q p hq
  have hh := reciprocal_product_gap_jets hM hg.1 hg.2.1
    (fun i => (hroots i).1) (fun i k hk => (hroots i).2 k hk) hg.2.2
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  have hn : 0<‖fun i => q (p i)‖ := norm_pos_iff.mpr hq0
  have hinv : (c*(ε+‖fun i => q (p i)‖^2))⁻¹ ≤
      (c*‖fun i => q (p i)‖^2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith
  calc
    _ ≤ (j.factorial:ℝ)^2*(c*(ε+‖fun i => q (p i)‖^2))⁻¹^(j+1)*(M*(N:ℝ))^j := hh
    _ ≤ (j.factorial:ℝ)^2*(c*‖fun i => q (p i)‖^2)⁻¹^(j+1)*(M*(N:ℝ))^j := by gcongr
    _ = _ := by
      rw [mul_inv_rev, mul_pow, mul_pow, inverse_square_power_eq_rpow _ hn.le]
      ring

theorem edgeReciprocal_retained_jets_up_to {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0) (j : ℕ) :
    ∃ δ A : ℝ, 0<δ ∧ 0<A ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      ∀ (N m : ℕ) [Nonempty (Fin m)] (q : Fin N → ℝ) (p : Fin m → Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → (fun i => q (p i))≠0 →
      ∀ k≤j, ‖iteratedDeriv k (fun u => (1-edgeRootProduct b B u q)⁻¹) (Complex.I*(ε:ℂ))‖≤
        A*(N:ℝ)^j*‖fun i => q (p i)‖^(-(2*(j+1):ℝ)) := by
  obtain ⟨η,M,hη,hM,hjet⟩ := edgeParamRoot_inward_geometric_jets hb hB hc j
  obtain ⟨c,δ,hcpos,hδ,hgap⟩ := edgeRootProduct_retained_gap (b := b) hB hc.continuousAt
  refine ⟨min η δ,(j.factorial:ℝ)^2*(c⁻¹)^(j+1)*M^j,
    lt_min hη hδ,by positivity,?_⟩
  intro ε hε hεδ N m _ q p hq hq0 k hk
  have hun : ‖Complex.I*(ε:ℂ)‖<η := by
    simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hε] using hεδ.trans_le (min_le_left _ _)
  have him : 0<(Complex.I*(ε:ℂ)).im := by simpa using hε
  have hroots := fun i => hjet _ hun him (q i) (hq i)
  have hg := hgap ε hε (hεδ.trans_le (min_le_right _ _)) N m q p hq
  have hh := reciprocal_product_gap_jets hM hg.1 hg.2.1
    (fun i => (hroots i).1) (fun i a ha => (hroots i).2 a (ha.trans hk)) hg.2.2
  have hN : 1≤(N:ℝ) := by
    have hn := (p (Classical.arbitrary (Fin m))).isLt
    exact_mod_cast (show 1≤N by omega)
  have hd1 : 1≤(c*(ε+‖fun i => q (p i)‖^2))⁻¹ := (one_le_inv₀ hg.1).mpr hg.2.1
  have hMN : 1≤M*(N:ℝ) := by nlinarith
  have hh' : ‖iteratedFDeriv ℂ k (fun v => (1-edgeRootProduct b B v q)⁻¹) (Complex.I*(ε:ℂ))‖≤
      (j.factorial:ℝ)^2*(c*(ε+‖fun i => q (p i)‖^2))⁻¹^(j+1)*(M*(N:ℝ))^j := by
    apply hh.trans
    gcongr
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh'
  have hn : 0<‖fun i => q (p i)‖ := norm_pos_iff.mpr hq0
  have hinv : (c*(ε+‖fun i => q (p i)‖^2))⁻¹ ≤
      (c*‖fun i => q (p i)‖^2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith
  calc
    _ ≤ (j.factorial:ℝ)^2*(c*(ε+‖fun i => q (p i)‖^2))⁻¹^(j+1)*(M*(N:ℝ))^j := hh'
    _ ≤ (j.factorial:ℝ)^2*(c*‖fun i => q (p i)‖^2)⁻¹^(j+1)*(M*(N:ℝ))^j := by gcongr
    _ = _ := by
      rw [mul_inv_rev, mul_pow, mul_pow, inverse_square_power_eq_rpow _ hn.le]
      ring

 theorem edgeReciprocal_eventually_analytic {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0) :
    ∀ᶠ u in 𝓝 (0:ℂ), 0<u.im → ∀ (N : ℕ), 0<N → ∀ q : Fin N → ℝ,
      (∀ i, q i∈Icc (-Real.pi) Real.pi) →
      AnalyticAt ℂ (fun v => (1-edgeRootProduct b B v q)⁻¹) u := by
  obtain ⟨c,hcpos,hgap⟩ := edgeParamRoot_uniform_gap (b := b) hB hc.continuousAt
  filter_upwards [edgeParamW_uniform_domain hb hB hc.continuousAt,
    hc.eventually_analyticAt,hgap] with u hdom hBa hg
  intro him N hN q hq
  have hr (i : Fin N) : AnalyticAt ℂ (fun v => edgeParamRoot b B v (q i)) u :=
    edgeParamRoot_analyticAt b hBa (hdom (q i) (hq i))
  have hnorm (i : Fin N) : ‖edgeParamRoot b B u (q i)‖<1 := by
    have hh := hg (q i) (hq i) him
    have hp : 0<c*(u.im+(q i)^2) := by positivity
    linarith
  have hp : ‖edgeRootProduct b B u q‖<1 :=
    (root_product_norm_le_factor (fun i => edgeParamRoot b B u (q i))
      (fun i => (hnorm i).le) ⟨0,hN⟩).trans_lt (hnorm ⟨0,hN⟩)
  apply (analyticAt_const.sub (Finset.analyticAt_fun_prod _ (fun i _ => hr i))).inv
  intro he
  have he' : edgeRootProduct b B u q=1 := (sub_eq_zero.mp he).symm
  simp [he'] at hp

end IsingBulk.Anisotropic.RegularEdges
