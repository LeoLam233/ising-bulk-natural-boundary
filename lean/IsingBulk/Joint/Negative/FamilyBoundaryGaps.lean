import IsingBulk.Joint.Negative.FamilyRootGap
import IsingBulk.Anisotropic.NegativeDominance.NonresonantBoundaryGap

/-! # Dimension-uniform outer and nonresonant gaps over compact families -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
  IsingBulk.Anisotropic.NegativeDominance IsingBulk.Joint.RegularEdges Set
open scoped BigOperators

theorem compact_boundary_product_gaussian {b : ℝ} {Q : Set (ℂ × ℂ)} (hb : |b|<1) (hQ : IsCompact Q) (hB : ∀ v∈Q, 0<v.1.im) :
    ∃c : ℝ,0<c ∧ ∀v∈Q, ∀N : ℕ,∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      ‖∏i,edgeRoot b v.1 (q i)‖≤Real.exp (-c*∑i,(q i)^2) := by
  obtain ⟨c,hc,hgap⟩ := compact_boundary_quadratic_gap hb hQ hB
  refine ⟨c,hc,?_⟩
  intro v hv N q hq
  have hf (i : Fin N) : ‖edgeRoot b v.1 (q i)‖≤Real.exp (-c*(q i)^2) := by
    have hh := Real.add_one_le_exp (-c*(q i)^2)
    linarith [hgap v hv (q i) (hq i)]
  rw [norm_prod]
  calc
    _ ≤ ∏i,Real.exp (-c*(q i)^2) := Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>hf i)
    _ = _ := by rw [←Real.exp_sum]; congr 1; rw [Finset.mul_sum]

/-- The entire outer region has one positive boundary resolvent gap before
all particle orders and all angular configurations. -/
theorem compact_outer_boundary_product_gap {b : ℝ} {Q : Set (ℂ × ℂ)} (hb : |b|<1) (hQ : IsCompact Q) (hB : ∀ v∈Q, 0<v.1.im)
    (σ : ℝ) (hσ : 0<σ) :
    ∃κ : ℝ,0<κ ∧ ∀v∈Q, ∀N : ℕ,∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      σ≤∑i,(q i)^2 → κ≤‖1-∏i,edgeRoot b v.1 (q i)‖ := by
  obtain ⟨c,hc,hprod⟩ := compact_boundary_product_gaussian hb hQ hB
  refine ⟨1-Real.exp (-c*σ),by have hh := Real.exp_lt_one_iff.mpr (by nlinarith : -c*σ<0); linarith,?_⟩
  intro v hv N q hq hS
  have hh := (hprod v hv N q hq).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hS (by linarith)))
  have hg := norm_sub_norm_le (1 : ℂ) (∏i,edgeRoot b v.1 (q i))
  rw [norm_one] at hg
  linarith


theorem compact_root_angular_quadratic {b : ℝ} {Q : Set (ℂ × ℂ)}
    (hb : |b|<1) (hQ : IsCompact Q) (hB : ∀v∈Q, 0<v.1.im) (hS : ∀v∈Q, v.2≠0) :
    ∃K : ℝ,0<K ∧ ∀v∈Q, ∀q : ℝ,
      ‖edgeRoot b v.1 q-continuedRoot (b:ℂ)‖≤K*q^2 := by
  obtain ⟨δ,L,hδ,hL,hroot⟩ := compact_root_lipschitz hb hQ hB hS
  obtain ⟨MC,hMC⟩ := hQ.exists_bound_of_continuousOn continuous_fst.continuousOn
  let M := max MC 0
  have hM : 0≤M := le_max_right _ _
  let σ := δ/(M+1)
  have hσ : 0<σ := by dsimp [σ]; positivity
  have hσeq : (M+1)*σ=δ := by dsimp [σ]; field_simp
  refine ⟨L*M+2/σ,by positivity,?_⟩
  intro v hv q
  have hBn : ‖v.1‖≤M := (hMC v hv).trans (le_max_left _ _)
  have hbase : ‖continuedRoot (b : ℂ)‖≤1 := by
    simpa [edgeRoot,edgeW] using (edgeRoot_bounds hb (hB v hv) 0).1
  by_cases hq : q^2≤σ
  · let u : ℂ := v.1*((1-Real.cos q : ℝ) : ℂ)
    have huNorm : ‖u‖=‖v.1‖*(1-Real.cos q) := by
      dsimp [u]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one q))]
    have hcos : 1-Real.cos q≤q^2/2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := q)]
    have hu : ‖u‖<δ := by
      rw [huNorm]
      have hh := mul_le_mul_of_nonneg_left hcos (norm_nonneg v.1)
      have hh' := mul_le_mul_of_nonneg_left hq (norm_nonneg v.1)
      nlinarith [norm_nonneg v.1,hBn]
    have hh := (hroot v hv (u,v) (by simpa using hu) 0 ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).2
    have he : independentRoot b (u,v) 0=edgeRoot b v.1 q := by
      simp [independentRoot,root,dispersion,edgeRoot,edgeW,u]
    have he0 : independentRoot b (0,v) 0=continuedRoot (b : ℂ) := by
      simp [independentRoot,root,dispersion]
    simp only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg u),sub_zero] at hh
    rw [he,he0,huNorm] at hh
    have hmul := mul_le_mul_of_nonneg_left hcos (mul_nonneg hL.le (norm_nonneg v.1))
    have hextra : 0≤(2/σ)*q^2 := by positivity
    have hbase' : 0≤L*M*q^2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hBn (mul_nonneg hL.le (sq_nonneg q))]
  · have hq' : σ≤q^2 := le_of_not_ge hq
    have hqgap : 2≤(2/σ)*q^2 := by
      have hh := mul_le_mul_of_nonneg_left hq' (show 0≤2/σ by positivity)
      have he : (2/σ)*σ=2 := by field_simp
      rwa [he] at hh
    have hdiff := norm_sub_le (edgeRoot b v.1 q) (continuedRoot (b : ℂ))
    have hnonneg : 0≤L*M*q^2 := by positivity
    nlinarith [(edgeRoot_bounds hb (hB v hv) q).1]


theorem compact_product_angular_variation {b : ℝ} {Q : Set (ℂ × ℂ)}
    (hb : |b|<1) (hQ : IsCompact Q) (hB : ∀v∈Q, 0<v.1.im) (hS : ∀v∈Q, v.2≠0) :
    ∃K : ℝ,0<K ∧ ∀v∈Q, ∀N : ℕ,∀q : Fin N→ℝ,
      ‖(∏i,edgeRoot b v.1 (q i))-continuedRoot (b:ℂ)^N‖≤K*∑i,(q i)^2 := by
  obtain ⟨K,hK,hq⟩ := compact_root_angular_quadratic hb hQ hB hS
  refine ⟨K,hK,?_⟩
  intro v hv N q
  have hbase : ‖continuedRoot (b:ℂ)‖≤1 := by
    simpa [edgeRoot,edgeW] using (edgeRoot_bounds hb (hB v hv) 0).1
  have hh := norm_prod_sub_prod_le_sum Finset.univ (fun i=>edgeRoot b v.1 (q i))
    (fun _=>continuedRoot (b:ℂ)) (fun i _=>(edgeRoot_bounds hb (hB v hv) (q i)).1) (fun _ _=>hbase)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  exact hh.trans (by rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _=>hq v hv (q i)))

/-- A fixed selected phase has one strictly positive nonresonant gap for the
whole compact anisotropy family, before all nonresonant particle orders. -/
theorem compact_nonresonant_boundary_product_gap {b : ℝ} {Q : Set (ℂ × ℂ)} {p : ℕ}
    (hb : |b|<1) (hQ : IsCompact Q) (hB : ∀v∈Q, 0<v.1.im) (hS : ∀v∈Q, v.2≠0)
    (hp : 2≤p) (hphase : IsPrimitiveRoot (continuedRoot (b:ℂ)) p) :
    ∃κ : ℝ,0<κ ∧ ∀v∈Q, ∀N : ℕ,¬p∣N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) → κ≤‖1-∏i,edgeRoot b v.1 (q i)‖ := by
  obtain ⟨κ,hκ,hphasegap⟩ := primitiveRoot_uniform_power_gap hp hphase
  obtain ⟨K,hK,hvariation⟩ := compact_product_angular_variation hb hQ hB hS
  let σ := κ/(2*K)
  have hσ : 0<σ := by dsimp [σ]; positivity
  obtain ⟨κout,hκout,houter⟩ := compact_outer_boundary_product_gap hb hQ hB σ hσ
  refine ⟨min κout (κ/2),lt_min hκout (by positivity),?_⟩
  intro v hv N hN q hq
  by_cases henergy : σ≤∑i,(q i)^2
  · exact (min_le_left _ _).trans (houter v hv N q hq henergy)
  · have hh := (hvariation v hv N q).trans
      (mul_le_mul_of_nonneg_left (le_of_not_ge henergy) hK.le)
    have he : K*σ=κ/2 := by dsimp [σ]; field_simp
    rw [he] at hh
    have htri := norm_add_le (1-∏i,edgeRoot b v.1 (q i))
      ((∏i,edgeRoot b v.1 (q i))-continuedRoot (b:ℂ)^N)
    rw [show (1-∏i,edgeRoot b v.1 (q i))+((∏i,edgeRoot b v.1 (q i))-continuedRoot (b:ℂ)^N)=
      1-continuedRoot (b:ℂ)^N by ring] at htri
    exact (min_le_right _ _).trans (by linarith [hphasegap N hN])

end
end IsingBulk.Joint.Negative
