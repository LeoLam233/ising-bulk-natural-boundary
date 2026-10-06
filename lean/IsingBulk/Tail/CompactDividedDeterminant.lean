import IsingBulk.Tail.CompactDeterminantMargin
import IsingBulk.Tail.DividedDeterminantIntegral

/-! Actual uniformly nonzero divided freezing determinant, with the correct
quantifier order on the intermediate window. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem transverse_update_mem_cube {N : ℕ} (x : Fin N → ℝ) (i j : Fin N) {lo hi t : ℝ}
    (hx : ∀ l, x l∈Icc lo hi) (ht : t∈Icc 0 1) :
    ∀ l, Function.update x i (x j+t*(x i-x j)) l∈Icc lo hi := by
  have hm := (convex_Icc lo hi) (hx j) (hx i) (sub_nonneg.mpr ht.2) ht.1
    (show (1-t)+t=1 by ring)
  have hm' : x j+t*(x i-x j)∈Icc lo hi := by
    convert hm using 1
    simp only [smul_eq_mul]
    ring
  intro l
  by_cases hli : l=i
  · subst l; simpa using hm'
  · simpa [Function.update_of_ne hli] using hx l

theorem actual_current_divided_determinant (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0≤D) (hβ : 0<β) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0<N → (N:ℝ)≤D*Real.sqrt H →
      ∀ τ lam : ℝ, 0≤τ → τ≤1 → 0≤lam → lam≤Real.exp (-β*H) →
      ∀ i j : Fin N, i≠j →
      let r := Real.exp (-d.c₀*Real.exp (-H))
      let s := radialParameter d.theta (Real.exp (-H))
      ContDiff ℝ ∞ (currentAngularDividedDifference (N := N) f r τ lam s i j) ∧
      (∀ θ, currentAngularDeterminant f r τ lam s i j θ=
        (θ i-θ j : ℝ) • currentAngularDividedDifference f r τ lam s i j θ) ∧
      ∀ θ : Fin N → ℝ,
      (∀ l, θ l∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      c≤‖currentAngularDividedDifference f r τ lam s i j θ‖ := by
  obtain ⟨c,hc,htrans⟩ := actual_current_determinant_transverse_margin d hcsmall f hf hp1 hδ hδsmall hD hβ
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨e,he,_,hmarginS⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨c,hc,?_⟩
  filter_upwards [htrans,Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he)] with H htransH hepsE
  intro N hN hND τ lam hτ hτ1 hlam hlamB i j hij
  let eps := Real.exp (-H)
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  have heps : 0<eps := Real.exp_pos _
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hmarg : r⁻¹-r<(sourceS s).im := by
    have hh := radialRadius_parameter_margin heps (hmarginS eps heps hepsE)
    change r⁻¹-r+Real.sin d.theta*eps<_ at hh
    linarith [mul_pos hsint heps]
  have hd := currentAngularDeterminant_smooth_division hN f hf hr hr1 hτ hlam hmarg i j
  refine ⟨hd.1,hd.2,?_⟩
  intro θ hθ
  have hF := unwrappedLogY_contDiff (N := N) f r τ lam hf.p_smooth hf.m_smooth
  have hG := currentComplexPhase_contDiff hN f hr hr1 hτ hlam hf.p_smooth hf.m_smooth
    hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmarg
  apply angularPairDividedDifference_im_margin _ _ hF hG i j θ c
  intro t ht
  exact htransH N hN hND τ lam hτ hτ1 hlam hlamB _ (transverse_update_mem_cube θ i j hθ ht) i j hij

end
end IsingBulk.Tail
