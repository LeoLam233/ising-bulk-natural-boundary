import IsingBulk.HT.Contour.OnsiteContinuation
import IsingBulk.HT.Final.OnsiteResidue
import IsingBulk.Tail.SelectedFDensityEstimate
import IsingBulk.Tail.SelectedGlobalEnvelope

/-! Actual onsite inverse-product and complete paired selected-density
estimates. The global factor is bounded as a product, not by incorrectly
bounding it through the offsite sum of two complex inverse products. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch IsingBulk.HT.Final
open scoped BigOperators

theorem onsite_canceledReducedDensity_continued_eq {N : ℕ} (s : ℂ) (y : Fin N → ℂ)
    (hy : ∀ i,y i≠0) (hW : ∀ i,sourceW s (y i)∈continuedRootDomain)
    (hygap : ∀ i j,1-y i*y j≠0) :
    onsiteCanceledDensity (fun i => selectedContinuedRoot s (y i)) y=
      reducedOnsiteDensity (fun i => selectedContinuedRoot s (y i)) y := by
  unfold onsiteCanceledDensity reducedOnsiteDensity selectedContinuedRoot
  rw [canceledPairProduct_eq s _ y hy (fun i => continuedRoot_nonzero _)
    (fun i => by
      have h := continuedRoot_quadratic (sourceW s (y i))
      dsimp [selectedContinuedRoot,sourceW,sourceS] at h ⊢
      linear_combination h)
    hygap (fun i j => continuedRoot_pair_gap (hW i) (hW j))]
  ring

theorem onsite_selected_actual_inverse_product {N : ℕ} (hN : 1≤N)
    (f : SelectorFunctions) {c₀ τ ε c θ₀ : ℝ} (hc₀ : 0≤c₀) (hτ : 0≤τ)
    (hε : 0≤ε) (hε1 : ε≤1) (hc : c≤1/4)
    (hp0 : ∀ x,0≤f.p x) (hp1 : ∀ x,f.p x≤1)
    (hm0 : ∀ x,0≤f.m x) (hm1 : ∀ x,f.m x≤1)
    (θ : Fin N → ℝ) {s : ℂ} (hs : ‖s-radialParameter θ₀ ε‖≤c/(N:ℝ)) :
    let y := deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ
    let z := fun i => selectedContinuedRoot s (y i)
    ‖(coordinateProduct z*coordinateProduct y)⁻¹‖≤((21+4*Real.exp (c₀+2*τ))^2)^N := by
  dsimp only
  obtain ⟨hs0,hs1⟩ := selected_disk_parameter_envelope hN hε hε1 hc hs
  let E := Real.exp (c₀+2*τ)
  let A := 21+4*E
  have hE : 0<E := Real.exp_pos _
  have hy := selected_y_norm_envelope (by omega : 0<N) f hc₀ hτ hε hε1 hp0 hp1 hm0 hm1 θ
  have hz (i : Fin N) :
      ‖(selectedContinuedRoot s (deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i))⁻¹‖≤A := by
    have hW := selected_sourceW_envelope hs0 hs1 (hy i).1 (hy i).2
    have hh := quadratic_inverse_norm_envelope
      (continuedRoot_quadratic (sourceW s (deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i))) hW
    change ‖(selectedContinuedRoot s (deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i))⁻¹‖≤4*(5+E)+1 at hh
    dsimp [A]
    linarith
  have hyi (i : Fin N) : ‖(deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i)⁻¹‖≤A := by
    have hh := (hy i).2
    change ‖(deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i)⁻¹‖≤E at hh
    dsimp [A]
    linarith
  have hb (v : Fin N → ℂ) (hv : ∀ i,‖(v i)⁻¹‖≤A) : ‖(coordinateProduct v)⁻¹‖≤A^N := by
    simp only [coordinateProduct,← Finset.prod_inv_distrib,norm_prod]
    calc
      _ ≤ ∏ _i : Fin N,A := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
      _ = _ := by simp
  rw [mul_inv_rev,norm_mul]
  calc
    _ ≤ A^N*A^N := mul_le_mul (hb _ hyi) (hb _ hz) (norm_nonneg _) (by dsimp [A]; positivity)
    _ = _ := by dsimp [A,E]; rw [← mul_pow,pow_two]

theorem onsite_reducedDensity_discounted_bound {N : ℕ} (z y : Fin N → ℂ)
    (b η C eps : ℝ) (θ : Fin N → ℝ) {A B a L : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (ha : 0<a) (hL : 0<L)
    (hnum : ‖(coordinateProduct z*coordinateProduct y)⁻¹‖≤A^N)
    (hp : ‖First.pairProduct z‖≤B^N*Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2))
    (hv : ∀ i,‖residueFactor (z i)‖≤selectedOneBodyBound b η C eps (θ i)) :
    ‖reducedOnsiteDensity z y‖≤(A*B)^N*Real.exp ((Real.log L)^2/(4*a))*
      ((∏ i,discountedSelectedWeight b η C eps L (θ i))*‖First.pairProduct y‖) := by
  have hres : ∏ i,‖residueFactor (z i)‖≤∏ i,selectedOneBodyBound b η C eps (θ i) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
  have hd := gaussian_selected_weight_product b η C eps hC ha hL θ
  calc
    _ ≤ A^N*(B^N*Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2))*
        ‖First.pairProduct y‖*(∏ i,selectedOneBodyBound b η C eps (θ i)) := by
      simp only [reducedOnsiteDensity,norm_mul,norm_prod]
      gcongr
    _ = (A*B)^N*(Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2)*
        (∏ i,selectedOneBodyBound b η C eps (θ i)))*‖First.pairProduct y‖ := by rw [mul_pow]; ring
    _ ≤ (A*B)^N*(Real.exp ((Real.log L)^2/(4*a))*
        (∏ i,discountedSelectedWeight b η C eps L (θ i)))*‖First.pairProduct y‖ := by gcongr
    _ = _ := by ring

theorem onsite_continuedPulledDensity_norm {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    ‖onsiteContinuedPulledDensity f r τ lam s θ‖=
      ((N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N)*‖(angularJacobian f τ lam θ).det‖*
        (∏ i,‖deformedPoint f r τ lam θ i‖)*
        ‖onsiteCanceledDensity (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
          (deformedPoint f r τ lam θ)‖ := by
  simp only [onsiteContinuedPulledDensity,norm_mul,norm_inv,Complex.norm_natCast,norm_prod,
    zpow_neg,zpow_natCast,norm_pow,Complex.norm_I,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_one,inv_pow]

end
end IsingBulk.HT.Contour
