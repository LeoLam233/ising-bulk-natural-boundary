import IsingBulk.Tail.ProtectedRootProduct
import IsingBulk.Tail.ProtectedCompactCover

/-! Literal coupled-contour protected root product. The angular branch width
and the parameter threshold are deliberately separate. This prevents a
circular or incomplete support cover when compact gaps shrink quadratically.
The source's fixed cutoff partition supplies the explicit angular supports. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators

theorem deformedPoint_upper_anchor {N : ℕ} (f : SelectorFunctions)
    (c₀ eps τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N)
    (hp : f.p (θ q)=1) (hm : f.m (θ q)=0) :
    deformedPoint f (Real.exp (-c₀*eps)) τ lam θ q = upperAnchorY c₀ eps τ lam (θ q) := by
  rw [deformedPoint_polar f (Real.exp_pos _) τ lam θ q,Real.log_exp,
    retractionShift_named τ _ _ q hp hm]
  unfold upperAnchorY
  congr 1
  push_cast
  ring

theorem deformedPoint_true_branch {N : ℕ} (f : SelectorFunctions)
    (b c₀ eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N)
    (hp : f.p (θ i)=0) (hm : f.m (θ i)=1) :
    deformedPoint f (Real.exp (-c₀*eps)) τ lam θ i =
      plateauY c₀ eps τ (lam*occupancy (fun j => f.p (θ j))/(N:ℝ)) b (θ i+b) := by
  rw [deformedPoint_coupledRadialExponent]
  unfold radialAnglePoint coupledRadialExponent plateauY
  rw [hp,hm]
  congr 1
  push_cast
  ring

/-- Source-level root conclusion on every named-current angular support of
the explicit compact/true-branch kind. All constants precede particle number,
epsilon, lambda, occupancy and angles; no final product bound is assumed. -/
theorem protected_deformed_root_product (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {σ : ℝ} (hσ : 0 < σ) :
    ∃ h R r : ℝ, 0 < h ∧ h < R ∧ h < d.thetaB ∧ d.thetaB+h < Real.pi ∧ 0 < r ∧
      ∀ τ : ℝ, 0 < τ → τ < r → ∃ c cq : ℝ, 0 < c ∧ 0 < cq ∧
      ∀ (N : ℕ) (f : SelectorFunctions) (eps lamStar lam : ℝ) (θ : Fin N → ℝ)
        (q : Fin N) (s : ℂ),
        1 ≤ N → 0 < eps → eps < r → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
        (∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) → (∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1) →
        (∀ x, Real.sin x ≤ 0 → f.p x=0) → (∀ x, 0 ≤ Real.sin x → f.m x=0) →
        (∀ i, |θ i| ≤ Real.pi) → f.p (θ q)=1 → f.m (θ q)=0 → σ ≤ Real.sin (θ q) →
        h ≤ |(|θ q|-d.thetaB)| →
        (∀ i, h ≤ |(|θ i|-d.thetaB)| ∨
          (f.p (θ i)=0 ∧ f.m (θ i)=1 ∧ |θ i+d.thetaB| < R)) →
        ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
        (∀ i, sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i) ∈ continuedRootDomain) ∧
        ‖∏ i, continuedRoot (sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i))‖ ≤
          Real.exp (-(cq/2)*lam) := by
  obtain ⟨R,hR,hproduct⟩ := protected_root_product d
  let h := min (R/4) (min (d.thetaB/4) ((Real.pi-d.thetaB)/4))
  have hh : 0 < h := by dsimp [h]; have := d.thetaB_pos; have := d.thetaB_lt; positivity
  have hhR : h < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hhb : h < d.thetaB := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_left _ _)) (by have := d.thetaB_pos; linarith)
  have hhbπ : d.thetaB+h < Real.pi := by
    have hb := (min_le_right (R/4) _).trans (min_le_right (d.thetaB/4) ((Real.pi-d.thetaB)/4))
    change h ≤ (Real.pi-d.thetaB)/4 at hb
    have := d.thetaB_lt
    linarith
  obtain ⟨K,hK,hKD,rC,hrC,hcover⟩ := deformed_nonbranch_compact_cover d hcsmall hh hhb hhbπ
  have hsin : 0 < Real.sin d.theta :=
    Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by have := d.theta_lt; linarith [Real.pi_pos])
  obtain ⟨δ,e,hδ,_,he,_,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsin d.c₀_pos hcsmall
  let r := min R (min rC e)
  have hr : 0 < r := lt_min hR (lt_min hrC he)
  have hrR : r ≤ R := min_le_left _ _
  have hrC' : r ≤ rC := (min_le_right _ _).trans (min_le_left _ _)
  have hre : r ≤ e := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨h,R,r,hh,hhR,hhb,hhbπ,hr,?_⟩
  intro τ hτ hτr
  obtain ⟨c,cq,hc,hcq,hpd⟩ := hproduct K hK hKD σ hσ τ hτ (hτr.trans_le hrR)
  refine ⟨c,cq,hc,hcq,?_⟩
  intro N f eps lamStar lam θ q s hN heps hepsr hls hl hl1 hp hm hps hms hθ hpq hmq hσq hqsep htypes hsd
  have hN0 : 0 < N := by omega
  have hl0 : 0 ≤ lam := hls.le.trans hl
  let P := occupancy (fun j => f.p (θ j))
  have hP1 : 1 ≤ P := occupancy_named (fun j => (hp (θ j)).1) q hpq
  have hPN : P ≤ N := occupancy_le (fun j => (hp (θ j)).2)
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  have hcenter (i : Fin N) : 0 < (sourceW (radialParameter d.theta eps) (y i)).im := by
    have hu0 : 0 < (sourceW (radialParameter d.theta eps)
        (deformedPoint f (Real.exp (-d.c₀*eps)) τ 0 θ i)).im := by
      rw [deformedPoint_polar f (Real.exp_pos _) τ 0 θ i,Real.log_exp]
      simpa only [zero_mul,add_zero,radialAnglePoint] using
        hupper eps heps (hepsr.trans_le hre) (radialParameter d.theta eps)
          (by simp; positivity) (θ i)
    exact hu0.trans_le (deformed_sourceW_im_ge hN0 f (Real.exp_pos _) hτ.le hl0 θ
      (radialParameter d.theta eps) (fun x => (hp x).1) (fun x => (hm x).1) hps hms i)
  have hcompact (i : Fin N) (hi : h ≤ |(|θ i|-d.thetaB)|) :
      sourceW (radialParameter d.theta eps) (y i) ∈ K :=
    hcover N hN0 f eps τ lam θ heps (hepsr.trans_le hrC') hτ.le (hτr.trans_le hrC')
      hl0 hl1 hp hm hps hms i (hθ i) hi
  have htypes' (i : Fin N) : sourceW (radialParameter d.theta eps) (y i) ∈ K ∨
      ∃ u : ℝ, |u| < R ∧ y i=plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u := by
    rcases htypes i with hi | ⟨hip,him,hir⟩
    · exact Or.inl (hcompact i hi)
    · exact Or.inr ⟨θ i+d.thetaB,hir,deformedPoint_true_branch f d.thetaB d.c₀ eps τ lam θ i hip him⟩
  exact hpd N eps lamStar lam P (θ q) y q s hN heps (hepsr.trans_le hrR) hls hl hl1
    hP1 hPN hσq (deformedPoint_upper_anchor f d.c₀ eps τ lam θ q hpq hmq)
    hcenter (hcompact q hqsep) htypes' hsd

/-- The other global product has a uniform gap from the exact occupancy sum. -/
theorem deformed_y_named_attenuation {N : ℕ} (hN : 0 < N) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (θ : Fin N → ℝ) (q : Fin N) (hp : ∀ x, 0 ≤ f.p x) (hm : ∀ x, f.m x ≤ 1)
    (hpq : f.p (θ q)=1) :
    ‖coordinateProduct (deformedPoint f r τ lam θ)‖ ≤ Real.exp (-(3*τ/2)*lam) := by
  rw [deformed_product_norm f hr]
  have hP := occupancy_named (fun i => hp (θ i)) q hpq
  have hsum := sum_retractionShift_le hN hτ (fun i => hp (θ i)) (fun i => hm (θ i))
  have hmul := mul_le_mul_of_nonneg_left hsum hlam
  have hocc := mul_le_mul_of_nonneg_left hP (show 0 ≤ 3*τ*lam/2 by positivity)
  have he : lam*∑ i, retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i ≤
      -(3*τ/2)*lam := by nlinarith
  exact (mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ hr hr1)).trans
    (Real.exp_le_exp.mpr he)

/-- Modulus attenuation gives the source's linear lambda product gap. -/
theorem exponential_attenuation_linear_gap {z : ℂ} {a lam : ℝ} (ha : 0 ≤ a)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hz : ‖z‖ ≤ Real.exp (-a*lam)) :
    (a*Real.exp (-a))*lam ≤ ‖1-z‖ := by
  have hh := Real.add_one_le_exp (a*lam)
  have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(a*lam))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hmul
  have he : Real.exp (-a) ≤ Real.exp (-(a*lam)) := Real.exp_le_exp.mpr (by nlinarith)
  have hmul' := mul_le_mul_of_nonneg_left he (mul_nonneg ha hlam)
  have hgap := norm_sub_norm_le (1:ℂ) z
  norm_num at hgap
  rw [neg_mul] at hz
  nlinarith

end
end IsingBulk.Tail
