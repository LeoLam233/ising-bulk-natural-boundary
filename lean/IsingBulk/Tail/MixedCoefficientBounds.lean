import IsingBulk.Tail.MixedSourceGeometry
import IsingBulk.Tail.MixedHybridChart

/-! Actual branch/compact coefficient envelopes and normalized finite sums
feeding the regular mixed residual cores. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators Topology

theorem mixed_branch_coefficient_bounds {s : ℂ} {b θ v inner : ℝ}
    (hb : 0<Real.sin b) (hi : 0< inner) (hi1 : inner≤1) (his : inner≤(Real.sin b)^2/4)
    (hprofile : |sectorDisplacement b θ|≤ inner)
    (hW : ‖sourceW s (radialAnglePoint v θ)-1‖≤2*inner)
    (hparam : ‖1-(s^2)⁻¹‖≤5) :
    ‖(mixedSourceSlope s (radialAnglePoint v θ))⁻¹‖≤8/Real.sin b ∧
      ‖mixedSourceA s (radialAnglePoint v θ)‖≤10/Real.sin b := by
  let y := radialAnglePoint v θ
  have hn : Real.sin b≤‖y-y⁻¹‖ := by
    have hh := sector_inner_sine_lower hb hi.le his hprofile
    exact (show Real.sin b≤2*|Real.sin θ| by linarith).trans (radialAnglePoint_difference_lower v θ)
  have hplus : ‖sourceW s y+1‖≤2*inner+2 := by
    have hh := norm_add_le (sourceW s y-1) (2:ℂ)
    rw [show sourceW s y-1+2=sourceW s y+1 by ring] at hh
    norm_num at hh
    linarith
  have hsin : ‖Complex.sin (mixedSourcePhase s y)‖≤4 := by
    have he := mixedSourcePhase_sin_norm_sq s y
    have hh : ‖1-(sourceW s y)^2‖≤8*inner := by
      rw [show 1-(sourceW s y)^2=-(sourceW s y-1)*(sourceW s y+1) by ring,norm_mul,norm_neg]
      have hm := mul_le_mul hW hplus (norm_nonneg _) (by positivity : 0≤2*inner)
      nlinarith
    nlinarith [norm_nonneg (Complex.sin (mixedSourcePhase s y))]
  constructor
  · change ‖(mixedSourceSlope s y)⁻¹‖≤_
    rw [mixedSourceSlope,inv_div,norm_div,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_I,one_mul]
    exact div_le_div₀ (by norm_num : (0:ℝ)≤8) (by linarith) hb hn
  · change ‖mixedSourceA s y‖≤_
    rw [mixedSourceA,norm_div,norm_div,norm_mul,norm_neg,Complex.norm_I,Complex.norm_ofNat,one_mul]
    have hh := div_le_div₀ (by norm_num : (0:ℝ)≤5) hparam (half_pos hb)
      (div_le_div_of_nonneg_right hn (by norm_num : (0:ℝ)≤2))
    exact hh.trans_eq (by ring)

theorem mixed_compact_coefficient_bounds {s : ℂ} {v θ g : ℝ}
    (hg : 0<g) (hv : |v|≤1) (hgap : g≤‖1-(sourceW s (radialAnglePoint v θ))^2‖)
    (hparam : ‖1-(s^2)⁻¹‖≤5) :
    ‖mixedSourceSlope s (radialAnglePoint v θ)‖≤Real.exp 1/Real.sqrt g ∧
      ‖mixedSourceTau s (radialAnglePoint v θ)‖≤5/Real.sqrt g := by
  let y := radialAnglePoint v θ
  have hsin : Real.sqrt g≤‖Complex.sin (mixedSourcePhase s y)‖ := by
    have he := mixedSourcePhase_sin_norm_sq s y
    have hs := Real.sq_sqrt hg.le
    nlinarith [norm_nonneg (Complex.sin (mixedSourcePhase s y)),Real.sqrt_nonneg g]
  have hspos : 0<Real.sqrt g := Real.sqrt_pos.mpr hg
  constructor
  · change ‖mixedSourceSlope s y‖≤_
    rw [mixedSourceSlope,norm_div,norm_mul,norm_mul,Complex.norm_I,Complex.norm_ofNat,one_mul]
    have hh := div_le_div₀ (by positivity : 0≤2*Real.exp 1) (radialAnglePoint_difference_upper hv θ)
      (by positivity : 0<2*Real.sqrt g) (mul_le_mul_of_nonneg_left hsin (by norm_num : (0:ℝ)≤2))
    exact hh.trans_eq (by ring)
  · change ‖mixedSourceTau s y‖≤_
    rw [mixedSourceTau,norm_div,norm_neg]
    exact div_le_div₀ (by norm_num : (0:ℝ)≤5) hparam hspos hsin

theorem normalized_subset_sum_norm_le {N : ℕ} (hN : 0<N) (J : Finset (Fin N))
    (f : Fin N → ℂ) {B : ℝ} (hB : 0≤B) (hf : ∀ i∈J,‖f i‖≤B) :
    ‖(∑ i∈J,f i)/(N:ℂ)‖≤B := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ hn).mpr
  have hh : ‖∑ i∈J,f i‖≤(J.card:ℝ)*B := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hf).trans_eq (by simp))
  have hcn : J.card≤N := by simpa using Finset.card_le_card (Finset.subset_univ J)
  have hc : (J.card:ℝ)≤N := by exact_mod_cast hcn
  exact hh.trans (by nlinarith)

def actualMixedResidualData {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (s : ℂ) (y : Fin N → ℂ) : MixedResidualData :=
  ((mixedSourceSlope s (y j))⁻¹,mixedSourceSlope s (y q),
    (∑ i∈J,mixedSourceA s (y i))/(N:ℂ),
    (∑ i∈Finset.univ.filter (fun i => i∉J),mixedSourceTau s (y i))/(N:ℂ))

theorem actualMixedResidualData_mem_of_bounds {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (s : ℂ) (y : Fin N → ℂ) {B : ℝ} (hB : 0≤B)
    (hβ : ‖(mixedSourceSlope s (y j))⁻¹‖≤B) (hb : ‖mixedSourceSlope s (y q)‖≤B)
    (hA : ∀ i∈J,‖mixedSourceA s (y i)‖≤B)
    (hD : ∀ i∉J,‖mixedSourceTau s (y i)‖≤B)
    (hsep : ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4) :
    actualMixedResidualData J j q s y ∈ mixedResidualCompact B := by
  have ha := normalized_subset_sum_norm_le hN J _ hB hA
  have hd := normalized_subset_sum_norm_le hN (Finset.univ.filter (fun i => i∉J)) _ hB
    (fun i hi => hD i (Finset.mem_filter.mp hi).2)
  constructor
  · simp only [Metric.mem_closedBall,dist_zero_right,actualMixedResidualData,Prod.norm_def,max_le_iff]
    exact ⟨hβ,hb,ha,hd⟩
  · exact mixed_denominator_margin (by simpa only [actualMixedResidualData,div_eq_mul_inv] using hsep)

theorem mixed_compact_sine_gap_from_profile {s y : ℂ} {b θ inner t : ℝ}
    (_hi : 0< inner) (hS : 0<1+Real.cos b)
    (hto : t≤ inner/4) (htS : t≤(1+Real.cos b)/2)
    (hp : inner/2≤|sectorDisplacement b θ|)
    (hd : ‖sourceW s y-(limitingAngularW b θ:ℂ)‖≤t) :
    inner*(1+Real.cos b)/8≤‖1-(sourceW s y)^2‖ := by
  have hm : inner/4≤‖sourceW s y-1‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (limitingAngularW b θ:ℂ) (sourceW s y) 1
    rw [limitingAngularW_sub_one_norm,norm_sub_rev (limitingAngularW b θ:ℂ)] at hh
    linarith
  have hp' : (1+Real.cos b)/2≤‖sourceW s y+1‖ := by
    have hbase : 1+Real.cos b≤‖(limitingAngularW b θ:ℂ)+1‖ := by
      have he : (limitingAngularW b θ:ℂ)+1=((limitingAngularW b θ+1:ℝ):ℂ) := by push_cast; rfl
      rw [he,Complex.norm_real,Real.norm_eq_abs]
      exact (show 1+Real.cos b≤limitingAngularW b θ+1 by unfold limitingAngularW; linarith [Real.cos_le_one θ]).trans (le_abs_self _)
    have hh := norm_sub_norm_le ((limitingAngularW b θ:ℂ)+1) (sourceW s y+1)
    rw [add_sub_add_right_eq_sub,norm_sub_rev] at hh
    linarith
  rw [show 1-(sourceW s y)^2=-(sourceW s y-1)*(sourceW s y+1) by ring,norm_mul,norm_neg]
  have hh := mul_le_mul hm hp' (by positivity : 0≤(1+Real.cos b)/2) (norm_nonneg _)
  nlinarith only [hh]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem mixed_actual_profile_coefficient_bounds (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (inner : ℝ) (hi : 0< inner)
    (hi1 : inner≤1) (his : inner≤(Real.sin d.thetaB)^2/4) :
    ∃ c e t₀ B : ℝ, 0<c ∧ 0<e ∧ 0<t₀ ∧ 0<B ∧
      ∀ η α : ℝ, 0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
        (∀ i, |sectorDisplacement d.thetaB (θ i)|≤ inner →
          ‖(mixedSourceSlope s (y i))⁻¹‖≤B ∧ ‖mixedSourceA s (y i)‖≤B) ∧
        (∀ i, inner/2≤|sectorDisplacement d.thetaB (θ i)| →
          ‖mixedSourceSlope s (y i)‖≤B ∧ ‖mixedSourceTau s (y i)‖≤B) := by
  have hb : 0<Real.sin d.thetaB := d.a_pos
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  let t := min inner (min (inner/4) ((1+Real.cos d.thetaB)/2))
  have ht : 0<t := lt_min hi (lt_min (by positivity) (by positivity))
  obtain ⟨c,e,t₀,hc,he,ht₀,hdata⟩ := mixed_actual_uniform_source_data d hcsmall t ht
  let g := inner*(1+Real.cos d.thetaB)/8
  have hg : 0<g := by dsimp [g]; positivity
  let B := max (8/Real.sin d.thetaB) (max (10/Real.sin d.thetaB)
    (max (Real.exp 1/Real.sqrt g) (5/Real.sqrt g)))
  have hB : 0<B := lt_of_lt_of_le (by positivity : 0<8/Real.sin d.thetaB) (le_max_left _ _)
  refine ⟨c,e,t₀,B,hc,he,ht₀,hB,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ s hN heps hepslt hτ hl0 hl1 htl hs
  obtain ⟨hparam,hcoords⟩ := hdata η α hη hηsmall hα N eps τ lam θ s hN heps hepslt hτ hl0 hl1 htl hs
  constructor
  · intro i hp
    obtain ⟨v,hv,hy,hd,_hphys⟩ := hcoords i
    have hWi : ‖sourceW s (radialAnglePoint v (θ i))-1‖≤2*inner := by
      rw [hy] at hd
      have hh := norm_sub_le_norm_sub_add_norm_sub (sourceW s (radialAnglePoint v (θ i))) (limitingAngularW d.thetaB (θ i):ℂ) 1
      rw [limitingAngularW_sub_one_norm] at hh
      have hti : t≤ inner := min_le_left _ _
      linarith
    rw [hy]
    obtain ⟨hβ,hA⟩ := mixed_branch_coefficient_bounds hb hi hi1 his hp hWi hparam
    exact ⟨hβ.trans (le_max_left _ _),hA.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  · intro i hp
    obtain ⟨v,hv,hy,hd,_hphys⟩ := hcoords i
    have hgap := mixed_compact_sine_gap_from_profile hi hS
      ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _)) hp hd
    rw [hy] at hgap ⊢
    obtain ⟨hb',hD⟩ := mixed_compact_coefficient_bounds hg hv hgap hparam
    exact ⟨hb'.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
      hD.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩


end
end IsingBulk.Tail
