import IsingBulk.Tail.OriginalCurrentGlobalFactors

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch
open scoped BigOperators

/-- Uniform actual root modulus on the original epsilon disk, for the whole
coupled homotopy. The product retains all N attenuation factors. -/
theorem original_current_root_modulus (theta c τ : ℝ)
    (hθ : 0 < Real.sin theta) (hc : 0 < c) (hcs : c < Real.sin theta/2) (hτ : 0 ≤ τ)
    (f : SelectorFunctions) (hp : ∀ x, 0 ≤ f.p x) (hp1 : ∀ x, f.p x ≤ 1)
    (hm : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    ∃ δ e a : ℝ, 0 < δ ∧ δ ≤ 1/16 ∧ 0 < e ∧ e ≤ 1 ∧ 0 < a ∧
      ∀ N : ℕ, 1 ≤ N → ∀ eps lam : ℝ, 0 < eps → eps < e →
      0 ≤ lam → lam ≤ 1 → ∀ θ : Fin N → ℝ, ∀ s : ℂ,
      ‖s-radialParameter theta eps‖ ≤ δ*eps →
      let z := fun i => selectedContinuedRoot s (deformedPoint f (Real.exp (-c*eps)) τ lam θ i)
      (∀ i, ‖z i‖ ≤ Real.exp (-a*eps)) ∧
      ‖coordinateProduct z‖ ≤ Real.exp (-a*(N:ℝ)*eps) := by
  obtain ⟨δ,e,hδ,hδs,he,he1,hmargin⟩ := original_disk_trace_margin theta c hθ hc hcs
  let E := Real.exp (c+2*τ)
  let M := 5+E
  let a := c/(2*M+1)
  have hE : 0 < E := Real.exp_pos _
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨δ,e,a,hδ,hδs,he,he1,ha,?_⟩
  intro N hN eps lam heps hepslt hl hl1 θ s hs
  dsimp only
  let y := deformedPoint f (Real.exp (-c*eps)) τ lam θ
  let z := fun i => selectedContinuedRoot s (y i)
  have heps1 : eps ≤ 1 := hepslt.le.trans he1
  have hmar := hmargin eps heps hepslt s hs
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
  have hzexp (i : Fin N) : ‖z i‖ ≤ Real.exp (-a*eps) := by
    have hzEq : z i=interiorRoot (sourceW s (y i)) := continuedRoot_eq_interiorRoot (hWpos i)
    rw [hzEq]
    have hh := interiorRoot_exponential_attenuation (hWpos i) (hWnorm i) (hWmargin i)
    convert hh using 1
    dsimp [a]
    congr 1
    ring
  refine ⟨hzexp,?_⟩
  change ‖coordinateProduct z‖ ≤ _
  rw [coordinateProduct,norm_prod]
  have hh := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => norm_nonneg (z i))
    (fun i (_ : i ∈ Finset.univ) => hzexp i)
  apply hh.trans_eq
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]
  congr 1
  ring

end
end IsingBulk.Tail
