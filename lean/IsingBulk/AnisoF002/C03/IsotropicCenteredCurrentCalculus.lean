import IsingBulk.AnisoF002.C03.IsotropicTransportDensity
import IsingBulk.AnisoF002.C03.IsotropicRadialDifferential

/-!
# Exact current calculus on the centered original constraint chart

The independent real variables have Jacobian e_i-e_last. The physical
time derivative carries the actual radial factor, while the same factor
multiplies each angular flux. Compact angular support gives literal zero
values outside the corresponding independent-coordinate box.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem centeredConstraintAngles_eq_linear_add {n : ℕ} (ρ : ℝ) (x : Fin n → ℝ) :
    centeredConstraintAngles ρ x = constrainedTangentMap n x + fun _ => ρ := by
  have hh := centeredConstraintAngles_sub_const ρ x
  funext i
  have hi := congrFun hh i
  change centeredConstraintAngles ρ x i = constrainedTangentMap n x i + ρ
  change centeredConstraintAngles ρ x i - ρ = constrainedTangentMap n x i at hi
  linarith

theorem centeredConstraintAngles_hasFDerivAt {n : ℕ} (ρ : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (centeredConstraintAngles ρ) (constrainedTangentMap n) x := by
  have he : centeredConstraintAngles (d := n) ρ =
      fun y => constrainedTangentMap n y + fun _ => ρ := funext (centeredConstraintAngles_eq_linear_add ρ)
  rw [he]
  exact (constrainedTangentMap n).hasFDerivAt.add_const _

theorem centered_joint_hasFDerivAt {n : ℕ} (s : ℂ) (ρ : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => (s, centeredConstraintAngles ρ y))
      ((0 : (Fin n → ℝ) →L[ℝ] ℂ).prod (constrainedTangentMap n)) x :=
  (hasFDerivAt_const s x).prodMk (centeredConstraintAngles_hasFDerivAt ρ x)

theorem centered_current_flux_partial {n : ℕ} (s c : ℂ) (ρ : ℝ)
    (f : (ℂ × (Fin (n + 1) → ℝ)) → ℂ) (x : Fin n → ℝ) (i : Fin n)
    (hf : DifferentiableAt ℝ f (s, centeredConstraintAngles ρ x)) :
    fderiv ℝ (fun y => c * f (s, centeredConstraintAngles ρ y)) x (Pi.single i 1) =
      c * scalarPartial f (actualAngularDirection i.castSucc - actualAngularDirection (Fin.last n))
        (s, centeredConstraintAngles ρ x) := by
  have hh := (hf.hasFDerivAt.comp x (centered_joint_hasFDerivAt s ρ x)).const_mul c
  simp only [Function.comp_def] at hh
  rw [hh.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, smul_eq_mul,
    constrainedTangentMap_single, scalarPartial, actualAngularDirection]
  congr 2
  ext <;> simp

theorem sum_erase_last_eq_castSucc {n : ℕ} (f : Fin (n + 1) → ℂ) :
    (∑ k ∈ Finset.univ.erase (Fin.last n), f k) = ∑ i : Fin n, f i.castSucc := by
  have hh := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) f (Finset.mem_univ (Fin.last n))
  rw [Fin.sum_univ_castSucc] at hh
  exact add_right_cancel hh

theorem centered_radial_current_identity {n : ℕ} (s p' : ℂ) (ρ : ℝ)
    (density nextDensity : (ℂ × (Fin (n + 1) → ℝ)) → ℂ)
    (flux : Fin (n + 1) → (ℂ × (Fin (n + 1) → ℝ)) → ℂ)
    (x : Fin n → ℝ)
    (hflux : ∀ i, DifferentiableAt ℝ (flux i) (s, centeredConstraintAngles ρ x))
    (hcurrent : scalarPartial density actualTimeDirection (s, centeredConstraintAngles ρ x) -
      (∑ k ∈ Finset.univ.erase (Fin.last n), scalarPartial (flux k)
        (actualAngularDirection k - actualAngularDirection (Fin.last n)) (s, centeredConstraintAngles ρ x)) =
      nextDensity (s, centeredConstraintAngles ρ x)) :
    p' * scalarPartial density actualTimeDirection (s, centeredConstraintAngles ρ x) -
      (∑ i : Fin n, fderiv ℝ (fun y => p' * flux i.castSucc (s, centeredConstraintAngles ρ y)) x
        (Pi.single i 1)) = p' * nextDensity (s, centeredConstraintAngles ρ x) := by
  simp_rw [centered_current_flux_partial s p' ρ _ x _ (hflux _)]
  rw [← Finset.mul_sum, ← mul_sub]
  rw [sum_erase_last_eq_castSucc] at hcurrent
  rw [hcurrent]

theorem centered_supported_zero_off_box {n : ℕ} (L U ρ : ℝ) (s : ℂ)
    (f : (ℂ × (Fin (n + 1) → ℝ)) → ℂ)
    (hsupport : ∀ q ∈ tsupport f, ∀ i, q.2 i ∈ Icc L U)
    (x : Fin n → ℝ) (hx : x ∉ Icc (fun _ => L - ρ) (fun _ => U - ρ)) :
    f (s, centeredConstraintAngles ρ x) = 0 := by
  by_contra hn
  have ht := hsupport _ (subset_closure hn)
  apply hx
  constructor
  · intro i
    have hi := (ht i.castSucc).1
    simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc] at hi
    linarith
  · intro i
    have hi := (ht i.castSucc).2
    simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc] at hi
    linarith

theorem centered_transport_density_zero_off_box {n : ℕ} (L U ρ : ℝ) (s σ : ℂ)
    (η τ ξ : ℝ) (g : (Fin (n + 1) → ℝ) → ℂ) (j : ℕ)
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc L U)
    (x : Fin n → ℝ) (hx : x ∉ Icc (fun _ => L - ρ) (fun _ => U - ρ)) :
    actualTransportedDensity σ η τ ξ g j (s, centeredConstraintAngles ρ x) = 0 :=
  centered_supported_zero_off_box L U ρ s _
    (fun q hq => hsupport q.2 (actualTransportedDensity_tsupport σ η τ ξ g j hq)) x hx

theorem centered_transport_flux_zero_off_box {n : ℕ} (L U ρ : ℝ) (s σ : ℂ)
    (η τ ξ : ℝ) (g : (Fin (n + 1) → ℝ) → ℂ) (j : ℕ) (i : Fin (n + 1))
    (hsupport : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc L U)
    (x : Fin n → ℝ) (hx : x ∉ Icc (fun _ => L - ρ) (fun _ => U - ρ)) :
    actualTransportedFlux σ η τ ξ g j i (s, centeredConstraintAngles ρ x) = 0 :=
  centered_supported_zero_off_box L U ρ s _
    (fun q hq => hsupport q.2 (actualTransportedFlux_tsupport σ η τ ξ g j i hq)) x hx

end
end IsingBulk.AnisoF002.Isotropic
