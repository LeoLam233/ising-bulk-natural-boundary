import IsingBulk.Tail.CompactRootContinuation
import IsingBulk.Tail.SelectorRegularity
import IsingBulk.First.DominatedAnalyticIntegral
import IsingBulk.First.FormFactorAnalytic

/-! Literal selected-F continuation using the globally compatible physical
root charts. Pair denominators are excluded algebraically without asserting
that every compact continued root remains inside the unit disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Filter
open scoped Topology BigOperators

theorem continuedRootDomain_ne_one {W : ℂ} (hW : W ∈ continuedRootDomain) : W ≠ 1 := by
  intro h
  norm_num [continuedRootDomain,h] at hW

theorem continuedRootDomain_ne_neg_one {W : ℂ} (hW : W ∈ continuedRootDomain) : W ≠ -1 := by
  intro h
  norm_num [continuedRootDomain,h] at hW

theorem continuedRoot_residue_gap {W : ℂ} (hW : W ∈ continuedRootDomain) :
    1-(continuedRoot W)^2 ≠ 0 := by
  intro h
  have hs : (continuedRoot W)^2=1 := (sub_eq_zero.mp h).symm
  have hq := continuedRoot_quadratic W
  rcases sq_eq_one_iff.mp hs with hz | hz
  · rw [hz] at hq
    have he : W=1 := by linear_combination -hq/2
    exact continuedRootDomain_ne_one hW he
  · rw [hz] at hq
    have he : W = -1 := by linear_combination hq/2
    exact continuedRootDomain_ne_neg_one hW he

/-- Reciprocity of two compatible continued roots forces equal dispersion,
then a branch point. The domain excludes the branch points. -/
theorem continuedRoot_pair_gap {W V : ℂ} (hW : W ∈ continuedRootDomain)
    (_hV : V ∈ continuedRootDomain) : 1-continuedRoot W*continuedRoot V ≠ 0 := by
  intro h
  have hp : continuedRoot W*continuedRoot V=1 := (sub_eq_zero.mp h).symm
  have hv : continuedRoot V=(continuedRoot W)⁻¹ := (inv_eq_of_mul_eq_one_right hp).symm
  have htW := quadratic_root_trace (continuedRoot_quadratic W)
  have htV := quadratic_root_trace (continuedRoot_quadratic V)
  rw [hv,inv_inv] at htV
  have he : W=V := by linear_combination (htV-htW)/2
  rw [← he] at h
  exact continuedRoot_residue_gap hW (by simpa only [pow_two] using h)

def selectedContinuedRoot (s y : ℂ) : ℂ := continuedRoot (sourceW s y)

theorem selectedContinuedRoot_analyticAt {s y : ℂ} (hs : s ≠ 0)
    (hW : sourceW s y ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun t => selectedContinuedRoot t y) s := by
  have ha : AnalyticAt ℂ (fun t => sourceW t y) s :=
    (analyticAt_id.add (analyticAt_id.inv hs)).sub analyticAt_const
  exact (continuedRoot_analyticAt hW).comp (f := fun t => sourceW t y) ha

theorem canceledReducedDensity_differentiableAt_of_gaps {N : ℕ}
    (y : Fin N → ℂ) (hy : ∀ i, y i ≠ 0) (hY : 1-coordinateProduct y ≠ 0)
    (z : ℂ → Fin N → ℂ) (s : ℂ)
    (hz : ∀ i, DifferentiableAt ℂ (fun t => z t i) s)
    (hz0 : ∀ i, z s i ≠ 0) (hZ : 1-coordinateProduct (z s) ≠ 0)
    (hpair : ∀ i j, 1-z s i*z s j ≠ 0) :
    DifferentiableAt ℂ (fun t => canceledReducedDensity (z t) y) s := by
  have hProd : DifferentiableAt ℂ (fun t => coordinateProduct (z t)) s := by
    unfold coordinateProduct
    exact DifferentiableAt.fun_finsetProd (fun i _ => hz i)
  have hZ0 : coordinateProduct (z s) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)
  have hPairs : DifferentiableAt ℂ (fun t => canceledPairProduct (z t) y) s := by
    unfold canceledPairProduct
    apply DifferentiableAt.fun_finsetProd
    intro i _
    apply DifferentiableAt.fun_finsetProd
    intro j _
    exact canceledPair_differentiableAt (mul_ne_zero (hy i) (hy j))
      (fun t => z t i) (fun t => z t j) (hz i) (hz j) (hpair i j)
  have hres : DifferentiableAt ℂ (fun t => ∏ i, residueFactor (z t i)) s := by
    apply DifferentiableAt.fun_finsetProd
    intro i _
    unfold residueFactor
    exact ((differentiableAt_const (2:ℂ)).mul ((hz i).pow 2)).div
      ((differentiableAt_const (1:ℂ)).sub ((hz i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  unfold canceledReducedDensity
  exact ((((hProd.inv hZ0).add_const ((coordinateProduct y)⁻¹)).div
    (((differentiableAt_const (1:ℂ)).sub hProd).mul_const (1-coordinateProduct y))
      (mul_ne_zero hZ hY)).mul hPairs).mul hres

def continuedPulledDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * (2*(Real.pi:ℂ)*Complex.I)^(- (N:ℤ)) *
    (angularJacobian f τ lam θ).det * (∏ i, deformedPoint f r τ lam θ i) *
    canceledReducedDensity (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)

def continuedSelectedIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, ((1-angularSelector f θ:ℝ):ℂ)*continuedPulledDensity f r τ 1 s θ

theorem continuedPulledDensity_eq_original {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0 < (sourceW s (deformedPoint f r τ lam θ i)).im) :
    continuedPulledDensity f r τ lam s θ = pulledDensity f r τ lam s θ := by
  have he : (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) =
      (fun i => globalRoot s (deformedPoint f r τ lam θ i)) := by
    funext i
    exact continuedRoot_eq_interiorRoot (hW i)
  simp only [continuedPulledDensity,pulledDensity,he]

theorem continuedPulledDensity_differentiableAt {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (θ : Fin N → ℝ) {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : 1-coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : 1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    DifferentiableAt ℂ (fun t => continuedPulledDensity f r τ lam t θ) s := by
  have hd := canceledReducedDensity_differentiableAt_of_gaps
    (deformedPoint f r τ lam θ) (deformedPoint_nonzero f hr τ lam θ) hY
    (fun t i => selectedContinuedRoot t (deformedPoint f r τ lam θ i)) s
    (fun i => (selectedContinuedRoot_analyticAt hs (hW i)).differentiableAt)
    (fun i => continuedRoot_nonzero _) hZ (fun i j => continuedRoot_pair_gap (hW i) (hW j))
  exact hd.const_mul _

/-- The enlarged-disk expression is the same actual selected-F germ at
any legal radial center. The equality holds on one neighborhood for every
angle; no exchange of infinitely many pointwise neighborhoods is used. -/
theorem continuedSelectedIntegral_eventually_original (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    {s : ℂ} (hmarg : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    continuedSelectedIntegral N f r τ =ᶠ[𝓝 s] selectedIntegral N f r τ := by
  have hsD := dampingDomain_of_margin hr hr1 hmarg
  filter_upwards [dampingDomain_mem_nhds hsD] with t ht
  apply MeasureTheory.setIntegral_congr_fun (measurableSet_Icc)
  intro θ _hθ
  dsimp only
  congr 1
  apply continuedPulledDensity_eq_original
  intro i
  exact (sourceW_upper_of_margin hr hr1 ht.2 (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
    (deformed_sourceW_im_ge hN f hr hτ (by norm_num) θ t hp hm0 hps hms i)

end
end IsingBulk.Tail
