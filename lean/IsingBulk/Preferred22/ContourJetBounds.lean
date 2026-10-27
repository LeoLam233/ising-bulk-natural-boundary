import IsingBulk.Preferred22.ContourJets

/-! Uniform fixed jets of the actual balanced Jacobian determinant. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem complexJet_const_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℂ) (x : E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun _ : E => c) x‖≤‖c‖ := by
  cases j with
  | zero => simp
  | succ j => simp [iteratedFDeriv_succ_const]

theorem complexJet_const_mul_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℂ) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x : E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => c*f y) x‖ = ‖c‖*‖iteratedFDeriv ℝ j f x‖ := by
  change ‖iteratedFDeriv ℝ j (fun y => c • f y) x‖ = _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)).contDiffAt, norm_smul]

theorem complexJet_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (j : ℕ) {B D : ℝ}
    (hb : ‖iteratedFDeriv ℝ j f x‖≤B) (hd : ‖iteratedFDeriv ℝ j g x‖≤D) :
    ‖iteratedFDeriv ℝ j (fun y => f y+g y) x‖≤B+D := by
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add hb hd)

theorem complexJet_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (j : ℕ) {B D : ℝ}
    (hb : ‖iteratedFDeriv ℝ j f x‖≤B) (hd : ‖iteratedFDeriv ℝ j g x‖≤D) :
    ‖iteratedFDeriv ℝ j (fun y => f y-g y) x‖≤B+D := by
  rw [fun_iteratedFDeriv_sub_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add hb hd)

theorem fullAngularJacobian_entry_contDiff {N : ℕ}
    (τ lam : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (i j : Fin N) : ContDiff ℝ ∞ (fun θ => fullAngularJacobian τ lam p m θ i j) := by
  have hd : ContDiff ℝ ∞ (fun θ => (jacobianDiagonalCoefficient p m i θ:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (jacobianDiagonalCoefficient_contDiff p m hp hm i)
  have hr : ContDiff ℝ ∞ (fun θ => (jacobianRankCoefficient p m i j θ:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (jacobianRankCoefficient_contDiff p m hp hm i j)
  simp_rw [fullAngularJacobian_entry_decomposition]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    exact contDiff_const.sub ((hd.add (hr.const_smul ((N:ℂ)⁻¹))).const_smul
      (Complex.I*(lam:ℂ)*(τ:ℂ)))
  · simp only [hij, ite_false]
    exact contDiff_const.sub ((contDiff_const.add (hr.const_smul ((N:ℂ)⁻¹))).const_smul
      (Complex.I*(lam:ℂ)*(τ:ℂ)))

theorem fullAngularJacobian_det_contDiff {N : ℕ}
    (τ lam : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => (fullAngularJacobian τ lam p m θ).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  exact (contDiff_prod (fun j _ => fullAngularJacobian_entry_contDiff τ lam p m hp hm (σ j) j)).const_smul
    ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))

def contourJetWeight (N : ℕ) (L A : ℝ) (i j : Fin N) : ℝ :=
  (if i=j then 1+L*A else 0) + L*A/N

theorem fullAngularJacobian_entry_jet_bound {N : ℕ}
    (τ lam : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (θ : Fin N → ℝ) (i j : Fin N) (r : ℕ) {A : ℝ}
    (hdiag : ‖iteratedFDeriv ℝ r (jacobianDiagonalCoefficient p m i) θ‖≤A)
    (hrank : ‖iteratedFDeriv ℝ r (jacobianRankCoefficient p m i j) θ‖≤A) :
    ‖iteratedFDeriv ℝ r (fun x => fullAngularJacobian τ lam p m x i j) θ‖ ≤
      contourJetWeight N (|lam| * |τ|) A i j := by
  let D : (Fin N → ℝ) → ℂ := fun x => (jacobianDiagonalCoefficient p m i x:ℂ)
  let R : (Fin N → ℝ) → ℂ := fun x => (jacobianRankCoefficient p m i j x:ℂ)
  have hD : ContDiff ℝ ∞ D :=
    Complex.ofRealCLM.contDiff.comp (jacobianDiagonalCoefficient_contDiff p m hp hm i)
  have hR : ContDiff ℝ ∞ R :=
    Complex.ofRealCLM.contDiff.comp (jacobianRankCoefficient_contDiff p m hp hm i j)
  have hd : ‖iteratedFDeriv ℝ r D θ‖≤A :=
    ofReal_jet_le _ (jacobianDiagonalCoefficient_contDiff p m hp hm i) θ r hdiag
  have hr : ‖iteratedFDeriv ℝ r R θ‖≤A :=
    ofReal_jet_le _ (jacobianRankCoefficient_contDiff p m hp hm i j) θ r hrank
  let U : (Fin N → ℝ) → ℂ := fun x => if i=j then D x else 0
  let V : (Fin N → ℝ) → ℂ := fun x => (N:ℂ)⁻¹*R x
  have hU : ContDiff ℝ ∞ U := by
    by_cases hij : i=j
    · simpa only [U, hij, ite_true] using hD
    · simpa only [U, hij, ite_false] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin N → ℝ => (0:ℂ)))
  have hV : ContDiff ℝ ∞ V := hR.const_smul ((N:ℂ)⁻¹)
  have hu : ‖iteratedFDeriv ℝ r U θ‖≤ if i=j then A else 0 := by
    by_cases hij : i=j
    · simpa only [U, hij, ite_true] using hd
    · simp [U, hij]
  have hv : ‖iteratedFDeriv ℝ r V θ‖≤(N:ℝ)⁻¹*A := by
    rw [show V=(fun x => (N:ℂ)⁻¹*R x) from rfl, complexJet_const_mul_norm _ _ hR]
    simp only [norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  have hx := complexJet_add_le U V hU hV θ r hu hv
  let c : ℂ := Complex.I*(lam:ℂ)*(τ:ℂ)
  have hc : ‖c‖=|lam| * |τ| := by
    simp [c, Complex.norm_real, Real.norm_eq_abs]
  have hg : ‖iteratedFDeriv ℝ r (fun x => c*(U x+V x)) θ‖≤
      (|lam| * |τ|)*((if i=j then A else 0)+(N:ℝ)⁻¹*A) := by
    rw [complexJet_const_mul_norm _ _ (hU.add hV), hc]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have hconst : ‖iteratedFDeriv ℝ r
      (fun _ : Fin N → ℝ => (if i=j then 1 else 0 : ℂ)) θ‖≤ if i=j then 1 else 0 := by
    exact (complexJet_const_bound _ θ r).trans_eq (by split_ifs <;> simp)
  have he : (fun x => fullAngularJacobian τ lam p m x i j) =
      fun x => (if i=j then 1 else 0)-c*(U x+V x) := by
    funext x
    exact fullAngularJacobian_entry_decomposition τ lam p m x i j
  rw [he]
  apply (complexJet_sub_le _ _ contDiff_const ((hU.add hV).const_smul c) θ r hconst hg).trans_eq
  unfold contourJetWeight
  by_cases hij : i=j <;> simp only [hij, ite_true, ite_false, div_eq_mul_inv] <;> ring

/-- Uniform full-dimension determinant jets. No factorial loss is present. -/
theorem fullAngularJacobian_determinant_uniform_jets (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (τ lam : ℝ) (J : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N →
      ∀ (θ : Fin N → ℝ) (r : ℕ), r≤J →
        ‖iteratedFDeriv ℝ r (fun x => (fullAngularJacobian τ lam p m x).det) θ‖ ≤
          C^N*(N:ℝ)^r := by
  obtain ⟨A,hA,hcoeff⟩ := jacobianCoefficients_uniform_jets p m hp hm hpp hmp J
  let L := |lam| * |τ|
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨1+2*L*A,by positivity,?_⟩
  intro N hN θ r hr
  let w := contourJetWeight N L A
  have hw : ∀ i j, 0≤w i j := by
    intro i j
    dsimp [w, contourJetWeight]
    split_ifs <;> positivity
  have hcol (j : Fin N) : ∑ i, w i j ≤ 1+2*L*A := by
    have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
    have he : (∑ i, w i j)=1+2*L*A := by
      simp only [w, contourJetWeight, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hn]
      ring
    exact he.le
  apply norm_iteratedFDeriv_determinant_column_bound
    (fun x => fullAngularJacobian τ lam p m x) θ r w hw
    (fullAngularJacobian_entry_contDiff τ lam p m hp hm) _ (by positivity) hcol
  intro i j l hl
  have h := hcoeff N hN i j θ l (hl.trans hr)
  exact fullAngularJacobian_entry_jet_bound τ lam p m hp hm θ i j l h.1 h.2

end
end IsingBulk.Preferred22
