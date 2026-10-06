import IsingBulk.Tail.MixedSourceGeometry
import IsingBulk.Tail.CompactPairUniform
import IsingBulk.Tail.SectorAssignmentPartition

/-! Any actual compact-left spectator supplies a fixed full Z-product gap.
The distinguished transport anchor need not itself be left. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology BigOperators

theorem coordinateProduct_norm_le_anchor {N : ℕ} (z : Fin N → ℂ) (a : Fin N)
    (hz : ∀ i,‖z i‖≤1) : ‖coordinateProduct z‖≤‖z a‖ := by
  rw [coordinateProduct,norm_prod,← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  exact mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀
    (fun i _ => norm_nonneg _) (fun i _ => hz i))

theorem compact_left_halfplane_uniform (inner : ℝ) (hi : 0< inner) :
    ∃ q : ℝ,0<q ∧ q<1 ∧ ∀ W : ℂ,
      1+inner/4≤W.re → ‖W‖≤4 → ‖compactLeftRoot W‖≤q := by
  let K : Set ℂ := closedBall 0 4 ∩ {W | 1+inner/4≤W.re}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hRe (W : ℂ) (hW : W∈K) : 1<W.re := by have := hW.2; change 1+inner/4≤W.re at this; linarith
  obtain ⟨q,hq,hq1,hbound⟩ := compact_norm_strict_bound K compactLeftRoot hK
    (fun W hW => (compactLeftRoot_analyticAt (hRe W hW)).continuousAt.continuousWithinAt)
    (fun W hW => compactLeftRoot_norm_lt_one (hRe W hW))
  exact ⟨q,hq,hq1,fun W hW hn => hbound W ⟨by simpa only [mem_closedBall,dist_zero_right] using hn,hW⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem left_actual_profile_Z_gap (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (inner : ℝ) (hi : 0< inner) :
    ∃ c e t₀ q : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<q ∧ q<1 ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (a : Fin N) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
        inner/2≤sectorDisplacement d.thetaB (θ a) →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
        (∀ i,‖globalRoot s (y i)‖≤1) ∧ ‖globalRoot s (y a)‖≤q ∧
          ‖coordinateProduct (fun i => globalRoot s (y i))‖≤q ∧
          1-q≤‖1-coordinateProduct (fun i => globalRoot s (y i))‖ := by
  let t := min (inner/4) 1
  have ht : 0<t := lt_min (by positivity) zero_lt_one
  obtain ⟨c,e,t₀,hc,he,ht₀,hdata⟩ := mixed_actual_uniform_source_data d hcsmall t ht
  obtain ⟨q,hq,hq1,hleft⟩ := compact_left_halfplane_uniform inner hi
  refine ⟨c,e,t₀,q,hc,he,ht₀,hq,hq1,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ a s hN heps hepslt hτ hl0 hl1 htl ha hs
  obtain ⟨_hparam,hcoords⟩ := hdata η α hη hηsmall hα N eps τ lam θ s hN heps hepslt hτ hl0 hl1 htl hs
  let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
  have hphys (i : Fin N) : 0<(sourceW s (y i)).im := (hcoords i).choose_spec.2.2.2
  have hall (i : Fin N) : ‖globalRoot s (y i)‖≤1 := (interiorRoot_norm_lt_one (hphys i)).le
  have hd : ‖sourceW s (y a)-(limitingAngularW d.thetaB (θ a):ℂ)‖≤t := (hcoords a).choose_spec.2.2.1
  have hRe : 1+inner/4≤(sourceW s (y a)).re := by
    have hh := Complex.abs_re_le_norm (sourceW s (y a)-(limitingAngularW d.thetaB (θ a):ℂ))
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    have hlo := (abs_le.mp (hh.trans hd)).1
    have ht' : t≤ inner/4 := min_le_left _ _
    unfold limitingAngularW sectorDisplacement at *
    linarith
  have hnorm : ‖sourceW s (y a)‖≤4 := by
    have hbase : ‖(limitingAngularW d.thetaB (θ a):ℂ)‖≤3 := by
      rw [Complex.norm_real,Real.norm_eq_abs]
      apply abs_le.mpr
      unfold limitingAngularW
      constructor <;> linarith [Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB,
        Real.cos_le_one (θ a),Real.neg_one_le_cos (θ a)]
    have hh := norm_le_norm_add_norm_sub (limitingAngularW d.thetaB (θ a):ℂ) (sourceW s (y a))
    rw [norm_sub_rev] at hh
    have ht' : t≤1 := min_le_right _ _
    linarith
  have hanchor : ‖globalRoot s (y a)‖≤q := by
    change ‖interiorRoot (sourceW s (y a))‖≤q
    rw [← compactLeftRoot_eq_interiorRoot (by linarith : 1<(sourceW s (y a)).re) (hphys a)]
    exact hleft _ hRe hnorm
  have hprod := (coordinateProduct_norm_le_anchor (fun i => globalRoot s (y i)) a hall).trans hanchor
  have hgap : 1-q≤‖1-coordinateProduct (fun i => globalRoot s (y i))‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (coordinateProduct (fun i => globalRoot s (y i)))
    rw [norm_one] at hh
    linarith
  exact ⟨hall,hanchor,hprod,hgap⟩

/-- Every fixed angular jet of the actual assignment retains the any-L gap. -/
theorem left_actual_sector_Z_gap (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (inner : ℝ) (hi : 0< inner) :
    ∃ c e t₀ q : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<q ∧ q<1 ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (a : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → sigma a=0 →
        θ ∈ tsupport (IsingBulk.Jets.cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
        ‖coordinateProduct (fun i => globalRoot s (y i))‖≤q ∧
          1-q≤‖1-coordinateProduct (fun i => globalRoot s (y i))‖ := by
  obtain ⟨c,e,t₀,q,hc,he,ht,hq,hq1,hbound⟩ := left_actual_profile_Z_gap d hcsmall inner hi
  refine ⟨c,e,t₀,q,hc,he,ht,hq,hq1,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ a sigma l s hN heps hepslt hτ hl0 hl1 htl hσ hsupp hs
  have hlabel := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp a
  rw [hσ] at hlabel
  have hfun : sectorLabel d.thetaB inner hi (0:Fin 3)=sectorLeft d.thetaB inner hi := by funext x; simp [sectorLabel]
  rw [hfun] at hlabel
  have hprof := (sector_labels_tsupport d.thetaB inner hi).1 hlabel
  exact (hbound η α hη hηsmall hα N eps τ lam θ a s hN heps hepslt hτ hl0 hl1 htl hprof hs).2.2

end
end IsingBulk.Tail
