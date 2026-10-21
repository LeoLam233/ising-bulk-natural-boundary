import IsingBulk.HT.Contour.SignedProtectedGeometry
import IsingBulk.Tail.OriginalCurrentGlobalFactors
import IsingBulk.Tail.OriginalDiskGlobalFactors

/-! Actual global current factors on the ORIGINAL c*epsilon disk, uniformly
for every real homotopy parameter in [0,1]. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch
open scoped BigOperators

 theorem signed_original_current_global_factors (σ : ℂ) (hσ : ‖σ‖ = 1) (theta c τ : ℝ)
    (hθ : 0 < Real.sin theta) (hc : 0 < c) (hcs : c < Real.sin theta/2) (hτ : 0 ≤ τ)
    (f : SelectorFunctions) (hp : ∀ x, 0 ≤ f.p x) (hp1 : ∀ x, f.p x ≤ 1)
    (hm : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    ∃ δ e A G : ℝ, 0 < δ ∧ δ ≤ 1/16 ∧ 0 < e ∧ e ≤ 1 ∧ 0 < A ∧ 0 < G ∧
      ∀ N : ℕ, 1 ≤ N → ∀ eps lam : ℝ, 0 < eps → eps < e →
      0 ≤ lam → lam ≤ 1 → ∀ θ : Fin N → ℝ, ∀ s : ℂ,
      ‖s-radialParameter theta eps‖ ≤ δ*eps →
      let y := deformedPoint f (Real.exp (-c*eps)) τ lam θ
      let z := fun i => selectedContinuedRoot s (y i)
      (Real.exp (-c*eps))⁻¹-Real.exp (-c*eps)<(sourceS s).im ∧
      ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖ ≤ 2*A^N ∧
      G*eps^2 ≤ ‖(1-σ*coordinateProduct z)*(1-σ*coordinateProduct y)‖ := by
  obtain ⟨δ,e,hδ,hδs,he,he1,hmargin⟩ := original_disk_trace_margin theta c hθ hc hcs
  let E := Real.exp (c+2*τ)
  let M := 5+E
  let a := c/(2*M+1)
  let A := 21+4*E
  let G := a*c*Real.exp (-(a+c))
  have hE : 0 < E := Real.exp_pos _
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨δ,e,A,G,hδ,hδs,he,he1,hA,hG,?_⟩
  intro N hN eps lam heps hepslt hl hl1 θ s hs
  dsimp only
  have heps1 : eps ≤ 1 := hepslt.le.trans he1
  have hmar := hmargin eps heps hepslt s hs
  have hmar' : (Real.exp (-c*eps))⁻¹-Real.exp (-c*eps)<(sourceS s).im := by
    simpa only [neg_mul,Real.exp_neg,inv_inv] using hmar
  refine ⟨hmar',?_⟩
  let y := deformedPoint f (Real.exp (-c*eps)) τ lam θ
  let z := fun i => selectedContinuedRoot s (y i)
  have hys := current_y_norm_envelope (by omega : 0<N) f hc.le hτ heps.le heps1 hl hl1 hp hp1 hm hm1 θ
  have hsn : 1/2 ≤ ‖s‖ := norm_ge_half_of_near_unit (t := radialParameter theta eps)
    (by rw [radialParameter_norm heps.le]; linarith) (by nlinarith)
  have hs3 : ‖s‖ ≤ 3 := by
    have hh := norm_le_norm_add_norm_sub (radialParameter theta eps) s
    rw [radialParameter_norm heps.le,norm_sub_rev] at hh
    nlinarith
  have hWnorm (i : Fin N) : ‖sourceW s (y i)‖ ≤ M :=
    selected_sourceW_envelope hsn hs3 (hys i).1 (hys i).2
  have hWmargin (i : Fin N) : c*eps ≤ (sourceW s (y i)).im :=
    original_current_dispersion_margin (by omega) f hc heps hτ hl θ hp hm hps hms hmar i
  have hWpos (i : Fin N) : 0 < (sourceW s (y i)).im := (mul_pos hc heps).trans_le (hWmargin i)
  have hzEq (i : Fin N) : z i=interiorRoot (sourceW s (y i)) := continuedRoot_eq_interiorRoot (hWpos i)
  have hzinv (i : Fin N) : ‖(z i)⁻¹‖ ≤ A := by
    have hh := quadratic_inverse_norm_envelope (continuedRoot_quadratic (sourceW s (y i))) (hWnorm i)
    change ‖(z i)⁻¹‖ ≤ 4*M+1 at hh
    dsimp [A,M]
    dsimp [M] at hh
    linarith
  have hyinv (i : Fin N) : ‖(y i)⁻¹‖ ≤ A := by
    have hh := (hys i).2
    change ‖(y i)⁻¹‖ ≤ E at hh
    dsimp [A]
    linarith
  have hnum := inverse_global_numerator_norm_le hA.le hA.le hzinv hyinv
  refine ⟨by simpa only [max_self] using hnum,?_⟩
  have hz1 (i : Fin N) : ‖z i‖ ≤ 1 := by rw [hzEq i]; exact (interiorRoot_norm_lt_one (hWpos i)).le
  have hzexp (i : Fin N) : ‖z i‖ ≤ Real.exp (-a*eps) := by
    rw [hzEq i]
    have hh := interiorRoot_exponential_attenuation (hWpos i) (hWnorm i) (hWmargin i)
    convert hh using 1
    dsimp [a]
    congr 1
    ring
  let q : Fin N := ⟨0,by omega⟩
  have hZ : ‖coordinateProduct z‖ ≤ Real.exp (-a*eps) :=
    (coordinateProduct_norm_le_anchor z q hz1).trans (hzexp q)
  have hY : ‖coordinateProduct y‖ ≤ Real.exp (-c*eps) :=
    original_current_y_product_bound hN f hc.le heps.le hτ hl θ hp hm1
  exact signed_current_global_denominator_lower hσ ha hc heps.le heps1 hZ hY

end
end IsingBulk.HT.Contour
