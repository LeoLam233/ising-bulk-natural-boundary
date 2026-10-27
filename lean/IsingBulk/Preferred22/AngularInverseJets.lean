import IsingBulk.Preferred22.ContourInverseBounds
import IsingBulk.Preferred22.ContourJetBounds

/-! All real angular jets of the literal inverse occupancy matrix. The
threshold is fixed before the derivative order and particle count. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem contourMatrix_eq_full {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) :
    preferredContourMatrix τ p m θ=fullAngularJacobian 1 τ p m θ := by
  ext i j
  unfold preferredContourMatrix fullAngularJacobian shiftJacobian
  push_cast
  ring

theorem preferredContourMatrix_contDiff_angular {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (@preferredContourMatrix N τ p m) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simpa only [contourMatrix_eq_full] using
    fullAngularJacobian_entry_contDiff 1 τ p m hp hm i j

theorem matrix_iteratedFDeriv_entry_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : ℕ} (f : E → Matrix (Fin N) (Fin N) ℂ)
    (hf : ContDiff ℝ ∞ f) (x : E) (r : ℕ) {C : ℝ} (hC : 0≤C)
    (he : ∀ i j, ‖iteratedFDeriv ℝ r (fun y => f y i j) x‖≤C) :
    ‖iteratedFDeriv ℝ r f x‖≤C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro j
  let L : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj i : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → ℂ))
  have hid : (iteratedFDeriv ℝ r (fun y => f y i j) x) v =
      ((iteratedFDeriv ℝ r f x) v) i j := by
    change (iteratedFDeriv ℝ r (L ∘ f) x) v = _
    rw [L.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
    rfl
  rw [← hid]
  exact ((iteratedFDeriv ℝ r (fun y => f y i j) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (he i j) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

/-- Actual angular Jacobian jets are bounded independently of N, including
the two occupancy derivatives. -/
theorem preferredContourMatrix_uniform_angular_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (τ₀ : ℝ) (hτ₀ : 0≤τ₀) (J : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ τ : ℝ, 0≤τ → τ≤τ₀ → ∀ N : ℕ, 0<N →
      ∀ θ : Fin N → ℝ, ∀ r≤J,
        ‖iteratedFDeriv ℝ r (@preferredContourMatrix N τ p m) θ‖≤C := by
  obtain ⟨A,hA,hjets⟩ := jacobianCoefficients_uniform_jets p m hp hm hpp hmp J
  have hpos : 0≤τ₀*A := mul_nonneg hτ₀ hA.le
  refine ⟨1+2*τ₀*A,by linarith,?_⟩
  intro τ hτ hτmax N hN θ r hr
  apply matrix_iteratedFDeriv_entry_bound _ (preferredContourMatrix_contDiff_angular τ p m hp hm)
    θ r (by positivity)
  intro i j
  have hcoeff := hjets N hN i j θ r hr
  have hh := fullAngularJacobian_entry_jet_bound 1 τ p m hp hm θ i j r hcoeff.1 hcoeff.2
  simp_rw [← contourMatrix_eq_full] at hh
  apply hh.trans
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hdiv : τ*A/(N:ℝ)≤τ*A := div_le_self (mul_nonneg hτ hA.le) hn
  have hτA : τ*A≤τ₀*A := mul_le_mul_of_nonneg_right hτmax hA.le
  simp only [contourJetWeight,abs_of_nonneg hτ,abs_one,mul_one]
  split_ifs <;> linarith

/-- All real angular derivatives of the actual inverse M. There is no
inverse-matrix hypothesis, and the deformation threshold precedes all orders. -/
theorem preferredContourMatrix_inverse_uniform_angular_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hp1 : ∀ x, |p x|≤1) (hm1 : ∀ x, |m x|≤1) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ ∀ J : ℕ, ∃ C : ℝ, 0<C ∧
      ∀ τ : ℝ, 0≤τ → τ≤τ₀ → ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ,
        ‖iteratedFDeriv ℝ J (fun x => (preferredContourMatrix τ p m x)⁻¹) θ‖≤C*(N:ℝ)^J := by
  obtain ⟨τ₀,hτ₀,hrow⟩ := preferredContourMatrix_uniform_half_row p m hp hm hpp hmp hp1 hm1
  refine ⟨τ₀,hτ₀,?_⟩
  intro J
  choose K hK hKjet using preferred_matrix_inverse_all_real_jets
  let B := 1+∑ j ∈ Finset.range (J+1), K j
  have hB : 0<B := by
    have hh : 0≤∑ j ∈ Finset.range (J+1), K j := Finset.sum_nonneg (fun j _ => (hK j).le)
    dsimp [B]
    linarith
  have hKB (j : ℕ) (hj : j≤J) : K j≤B := by
    have hh := Finset.single_le_sum (fun r (_ : r∈Finset.range (J+1)) => (hK r).le)
      (show j∈Finset.range (J+1) from Finset.mem_range.mpr (by omega))
    dsimp [B]
    linarith
  obtain ⟨D,hD,hDjet⟩ := preferredContourMatrix_uniform_angular_jets p m hp hm hpp hmp τ₀ hτ₀.le J
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨(J.factorial:ℝ)*B*D^J,by positivity,?_⟩
  intro τ hτ hτmax N hN θ
  let f := @preferredContourMatrix N τ p m
  let t : Set (Matrix (Fin N) (Fin N) ℂ) := {A | A.det≠0}
  have ht : IsOpen t := isOpen_ne.preimage continuous_id.matrix_det
  have hft : Set.range f⊆t := by
    rintro A ⟨x,rfl⟩
    exact (preferred_matrix_inverse_of_row_half (f x) (hrow τ hτ hτmax N hN x)).1
  have hg : ContDiffOn ℝ ∞ (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) t := by
    intro A hA
    have hh : ContDiffAt ℂ ∞ (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) A :=
      (preferred_matrix_inv_analyticAt A hA).contDiffAt
    exact (hh.restrict_scalars ℝ).contDiffWithinAt
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hjet (i : ℕ) (hi : i≤J) :
      ‖iteratedFDerivWithin ℝ i (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) t (f θ)‖≤B*(N:ℝ)^J := by
    rw [iteratedFDerivWithin_of_isOpen i ht (hft ⟨θ,rfl⟩)]
    exact (hKjet i N hN (f θ) (hrow τ hτ hτmax N hN θ)).trans
      (mul_le_mul (hKB i hi) (pow_le_pow_right₀ hn hi) (by positivity) hB.le)
  have hh := norm_iteratedFDeriv_comp_le' hft ht.uniqueDiffOn hg
    (preferredContourMatrix_contDiff_angular τ p m hp hm) (by simp : (J:ℕ∞ω)≤∞) θ hjet
    (fun i hi hiJ => (hDjet τ hτ hτmax N hN θ i hiJ).trans
      (le_self_pow₀ hD (by omega : i≠0)))
  change ‖iteratedFDeriv ℝ J (fun x => (f x)⁻¹) θ‖≤_
  apply hh.trans_eq
  ring

end
end IsingBulk.Preferred22
