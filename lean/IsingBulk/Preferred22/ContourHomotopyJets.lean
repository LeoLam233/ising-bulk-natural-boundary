import IsingBulk.Preferred22.ContourFinalJets

/-! The Jacobian jet constants also hold uniformly over the entire homotopy
parameter interval. This supplies both clauses of LT22 Lemma 5.1. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem fullAngularJacobian_homotopy_uniform_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (τ : ℝ) (J : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ lam : ℝ, |lam| ≤ 1 →
      ∀ N : ℕ, 0<N → ∀ (θ : Fin N → ℝ) (r : ℕ), r≤J →
        ‖iteratedFDeriv ℝ r (fun x => (fullAngularJacobian τ lam p m x).det) θ‖ ≤
          C^N*(N:ℝ)^r := by
  obtain ⟨A,hA,hcoeff⟩ := jacobianCoefficients_uniform_jets p m hp hm hpp hmp J
  refine ⟨1 + 2 * |τ| * A,by positivity,?_⟩
  intro lam hlam N hN θ r hr
  let L := |lam| * |τ|
  have hL : 0≤L := by dsimp [L]; positivity
  have hLτ : L ≤ |τ| := by
    dsimp [L]
    exact mul_le_of_le_one_left (abs_nonneg τ) hlam
  let w := contourJetWeight N L A
  have hw : ∀ i j, 0≤w i j := by
    intro i j
    dsimp [w, contourJetWeight]
    split_ifs <;> positivity
  have hcol (j : Fin N) : ∑ i, w i j ≤ 1 + 2 * |τ| * A := by
    have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
    have he : (∑ i, w i j)=1+2*L*A := by
      simp only [w, contourJetWeight, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hn]
      ring
    rw [he]
    gcongr
  apply norm_iteratedFDeriv_determinant_column_bound
    (fun x => fullAngularJacobian τ lam p m x) θ r w hw
    (fullAngularJacobian_entry_contDiff τ lam p m hp hm) _ (by positivity) hcol
  intro i j l hl
  have h := hcoeff N hN i j θ l (hl.trans hr)
  exact fullAngularJacobian_entry_jet_bound τ lam p m hp hm θ i j l h.1 h.2

/-- Exact dimension and homotopy uniform angular Jacobian jets. -/
theorem constrainedAngularJacobian_homotopy_uniform_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (τ : ℝ) (J : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ lam : ℝ, |lam| ≤ 1 →
      ∀ (n : ℕ) (θ : Fin n → ℝ) (r : ℕ), r≤J →
        ‖iteratedFDeriv ℝ r (fun x => (constrainedAngularJacobian τ lam p m x).det) θ‖ ≤
          C^(n+1)*((n+1:ℕ):ℝ)^(2*r) := by
  obtain ⟨C,hC,hbound⟩ := fullAngularJacobian_homotopy_uniform_jets p m hp hm hpp hmp τ J
  refine ⟨C,hC,?_⟩
  intro lam hlam n θ r hr
  let L := constrainedAnglesCLM n
  let f : (Fin (n+1) → ℝ) → ℂ := fun x => (fullAngularJacobian τ lam p m x).det
  have hf : ContDiff ℝ ∞ f := fullAngularJacobian_det_contDiff τ lam p m hp hm
  have he : (fun x : Fin n → ℝ => (constrainedAngularJacobian τ lam p m x).det) = f ∘ L := by
    funext x
    simpa only [Function.comp_apply, L, constrainedAnglesCLM_apply, f] using
      constrainedAngularJacobian_det_eq_full τ lam p m hp hm x
  rw [he, L.iteratedFDeriv_comp_right hf θ (by simp)]
  apply ((iteratedFDeriv ℝ r f (L θ)).norm_compContinuousLinearMap_le _).trans
  have hprod : (∏ _k : Fin r, ‖L‖) ≤ ((n+1:ℕ):ℝ)^r := by
    simpa using Finset.prod_le_prod₀ (fun _ (_ : _∈(Finset.univ : Finset (Fin r))) => norm_nonneg L)
      (fun _ (_ : _∈(Finset.univ : Finset (Fin r))) => constrainedAnglesCLM_norm_le n)
  have hfbound := hbound lam hlam (n+1) (by omega) (L θ) r hr
  calc
    _ ≤ (C^(n+1)*((n+1:ℕ):ℝ)^r)*((n+1:ℕ):ℝ)^r :=
      mul_le_mul hfbound hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg L)) (by positivity)
    _ = _ := by rw [two_mul, pow_add]; ring

end
end IsingBulk.Preferred22
