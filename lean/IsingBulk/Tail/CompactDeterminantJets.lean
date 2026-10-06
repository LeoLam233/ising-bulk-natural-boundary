import IsingBulk.Tail.CompactFreezingDeterminant
import IsingBulk.Tail.CompactComplexFirstJet
import IsingBulk.Tail.CompactLogYJets
import IsingBulk.Tail.CompactPairCoordinates

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem angularPairDeterminant_fderiv {N : ℕ} {F G : (Fin N → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i j : Fin N) (x v : Fin N → ℝ) :
    fderiv ℝ (angularPairDeterminant F G i j) x v=
      fderiv ℝ (fderiv ℝ F) x v (Pi.single i 1)*fderiv ℝ G x (Pi.single j 1)+
      fderiv ℝ F x (Pi.single i 1)*fderiv ℝ (fderiv ℝ G) x v (Pi.single j 1)-
      fderiv ℝ (fderiv ℝ F) x v (Pi.single j 1)*fderiv ℝ G x (Pi.single i 1)-
      fderiv ℝ F x (Pi.single j 1)*fderiv ℝ (fderiv ℝ G) x v (Pi.single i 1) := by
  have hd (H : (Fin N → ℝ) → ℂ) (hH : ContDiff ℝ ∞ H) (l : Fin N) :
      HasFDerivAt (fun y => fderiv ℝ H y (Pi.single l 1))
        ((fderiv ℝ (fderiv ℝ H) x).flip (Pi.single l 1)) x := by
    have hHd : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
    have hh := (hHd.differentiable (by simp) x).hasFDerivAt.clm_apply
      (hasFDerivAt_const (Pi.single l (1:ℝ)) x)
    simpa only [ContinuousLinearMap.comp_zero,zero_add] using hh
  have hh := (((hd F hF i).mul (hd G hG j)).sub ((hd F hF j).mul (hd G hG i))).fderiv
  change fderiv ℝ (angularPairDeterminant F G i j) x=_ at hh
  rw [hh]
  simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

theorem complex_product_perturbation {z z0 w w0 : ℂ} {a B b : ℝ}
    (ha : 0≤a) (_hB : 0≤B) (hz : ‖z-z0‖≤a) (hw : ‖w‖≤B)
    (hz0 : ‖z0‖≤1) (hdw : ‖w-w0‖≤b) : ‖z*w-z0*w0‖≤a*B+b := by
  have he : z*w-z0*w0=(z-z0)*w+z0*(w-w0) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (mul_le_mul hz hw (norm_nonneg _) ha)
    ((mul_le_mul_of_nonneg_right hz0 (norm_nonneg _)).trans (by simpa using hdw))

theorem complex_determinant_transverse_perturbation
    {ai aj api apj bi bj bpi bpj c : ℂ} {eA eA2 B1 B2 eB : ℝ}
    (heA : 0≤eA) (hB2 : 0≤B2)
    (hai : ‖ai-Complex.I‖≤eA) (haj : ‖aj-Complex.I‖≤eA)
    (hapi : ‖api‖≤eA2) (hapj : ‖apj‖≤eA2)
    (hbi : ‖bi‖≤B1) (hbj : ‖bj‖≤B1)
    (hbpi : ‖bpi‖≤B2) (hbpj : ‖bpj‖≤B2)
    (hbpic : ‖bpi-c‖≤eB) (hbpj0 : ‖bpj‖≤eB) :
    ‖api*bj+ai*bpj-apj*bi-aj*bpi-(-Complex.I*c)‖≤
      2*eA2*B1+2*eA*B2+2*eB := by
  have hA2 : 0≤eA2 := (norm_nonneg api).trans hapi
  have h1 : ‖api*bj‖≤eA2*B1 := by rw [norm_mul]; exact mul_le_mul hapi hbj (norm_nonneg _) hA2
  have h2 : ‖apj*bi‖≤eA2*B1 := by rw [norm_mul]; exact mul_le_mul hapj hbi (norm_nonneg _) hA2
  have h3 : ‖ai*bpj-Complex.I*0‖≤eA*B2+eB :=
    complex_product_perturbation heA hB2 hai hbpj (by simp) (by simpa using hbpj0)
  have h4 : ‖aj*bpi-Complex.I*c‖≤eA*B2+eB :=
    complex_product_perturbation heA hB2 haj hbpi (by simp) hbpic
  have he : api*bj+ai*bpj-apj*bi-aj*bpi-(-Complex.I*c)=
      (api*bj-apj*bi)+(ai*bpj-Complex.I*0)-(aj*bpi-Complex.I*c) := by ring
  rw [he]
  have hh : ‖(api*bj-apj*bi)+(ai*bpj-Complex.I*0)-(aj*bpi-Complex.I*c)‖≤
      (‖api*bj‖+‖apj*bi‖)+‖ai*bpj-Complex.I*0‖+‖aj*bpi-Complex.I*c‖ :=
    (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  exact hh.trans (by linarith)

def logYBaselineLinear (N : ℕ) : (Fin N → ℝ) →L[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM.comp (coordinateSumLinear N))

theorem logYBaselineLinear_apply {N : ℕ} (x : Fin N → ℝ) :
    logYBaselineLinear N x=logYBaseline N x := by
  simp [logYBaselineLinear,logYBaseline,coordinateSumLinear_apply]

theorem logYBaseline_fderiv (N : ℕ) (x : Fin N → ℝ) :
    fderiv ℝ (logYBaseline N) x=logYBaselineLinear N := by
  have he : logYBaseline N=(logYBaselineLinear N : (Fin N → ℝ) → ℂ) :=
    funext (fun x => (logYBaselineLinear_apply x).symm)
  rw [he]
  exact (logYBaselineLinear N).fderiv

theorem logYBaseline_second_fderiv (N : ℕ) (x : Fin N → ℝ) :
    fderiv ℝ (fderiv ℝ (logYBaseline N)) x=0 := by
  have he : fderiv ℝ (logYBaseline N)=(fun _ => logYBaselineLinear N) := funext (logYBaseline_fderiv N)
  rw [he]
  exact (hasFDerivAt_const (logYBaselineLinear N) x).fderiv

theorem logYBaseline_single {N : ℕ} (x : Fin N → ℝ) (i : Fin N) :
    fderiv ℝ (logYBaseline N) x (Pi.single i 1)=Complex.I := by
  rw [logYBaseline_fderiv,logYBaselineLinear_apply]
  unfold logYBaseline
  rw [← Complex.ofReal_sum]
  simp


theorem unwrappedLogY_coordinate_jet_perturbation (f : SelectorFunctions) (hf : RegularSelector f) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N → ∀ r τ lam : ℝ, 0≤τ → τ≤1 → 0≤lam →
      ∀ (θ : Fin N → ℝ) (i p : Fin N),
      ‖fderiv ℝ (unwrappedLogY f r τ lam) θ (Pi.single i 1)-Complex.I‖≤C*N*lam ∧
      ‖fderiv ℝ (fderiv ℝ (unwrappedLogY f r τ lam)) θ (Pi.single p 1) (Pi.single i 1)‖≤C*N*lam := by
  obtain ⟨C1,hC1,h1⟩ := unwrappedLogY_positive_jet_perturbation f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic 1 (by decide)
  obtain ⟨C2,hC2,h2⟩ := unwrappedLogY_positive_jet_perturbation f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic 2 (by decide)
  refine ⟨max C1 C2,lt_of_lt_of_le hC1 (le_max_left _ _),?_⟩
  intro N hN r τ lam hτ hτ1 hlam θ i p
  let F := unwrappedLogY (N := N) f r τ lam
  have hfirst := (iteratedFDeriv ℝ 1 F θ-iteratedFDeriv ℝ 1 (logYBaseline N) θ).le_opNorm
    (fun _ : Fin 1 => Pi.single i (1:ℝ))
  simp only [sub_apply,iteratedFDeriv_one_apply,logYBaseline_single,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Pi.norm_single] at hfirst
  have hsecond := (iteratedFDeriv ℝ 2 F θ-iteratedFDeriv ℝ 2 (logYBaseline N) θ).le_opNorm
    ![Pi.single p (1:ℝ),Pi.single i (1:ℝ)]
  simp only [sub_apply,iteratedFDeriv_two_apply,logYBaseline_second_fderiv,zero_apply,sub_zero,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Pi.norm_single,norm_one,mul_one] at hsecond
  constructor
  · have hb := h1 N hN r τ lam hτ hτ1 hlam θ
    have hh : C1*N*lam≤max C1 C2*N*lam := by gcongr; exact le_max_left _ _
    exact hfirst.trans (by simpa using hb.trans hh)
  · have hb := h2 N hN r τ lam hτ hτ1 hlam θ
    have hh : C2*N*lam≤max C1 C2*N*lam := by gcongr; exact le_max_right _ _
    exact hsecond.trans (hb.trans hh)


theorem currentPhase_coordinate_jet_perturbation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB)) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ N : ℕ, 0<N → ∀ eps τ lam : ℝ,
      0<eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 → eps+lam≤r →
      ∀ θ : Fin N → ℝ,
      (∀ i, θ i∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      ∀ i p : Fin N,
      let G := currentComplexPhase (N := N) f (Real.exp (-d.c₀*eps)) τ lam (radialParameter d.theta eps)
      ‖fderiv ℝ G θ (Pi.single i 1)-((deriv (compactRightPhase (1+Real.cos d.thetaB)) (θ i):ℝ):ℂ)‖≤
        C*N*(eps+lam) ∧
      ‖fderiv ℝ (fderiv ℝ G) θ (Pi.single p 1) (Pi.single i 1)-
        (if p=i then ((deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i):ℝ):ℂ) else 0)‖≤
        C*N*(eps+lam) := by
  obtain ⟨r1,C1,hr1,hC1,h1⟩ := actual_compact_complex_first_perturbation d hcsmall f hf hp1 hδ hδsmall
  obtain ⟨r2,C2,hr2,hC2,h2⟩ := actual_compact_complex_hessian_perturbation d hcsmall f hf hp1 hδ hδsmall
  refine ⟨min r1 r2,max C1 C2,lt_min hr1 hr2,lt_of_lt_of_le hC1 (le_max_left _ _),?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 hsmall θ hθ i p
  have hnorm (l : Fin N) : ‖(Pi.single l (1:ℝ) : Fin N → ℝ)‖≤1 := by
    rw [Pi.norm_single]; norm_num
  have h1b := h1 N hN eps τ lam heps hτ hτ1 hlam hlam1 (hsmall.trans (min_le_left _ _))
    θ (Pi.single i 1) (hnorm i) hθ
  have h2b := h2 N hN eps τ lam heps hτ hτ1 hlam hlam1 (hsmall.trans (min_le_right _ _))
    θ (Pi.single p 1) (Pi.single i 1) (hnorm p) (hnorm i) hθ
  dsimp only at h1b h2b ⊢
  have hs1 : (∑ l : Fin N, ((deriv (compactRightPhase (1+Real.cos d.thetaB)) (θ l)*((Pi.single i (1:ℝ) : Fin N → ℝ) l):ℝ):ℂ))=
      ((deriv (compactRightPhase (1+Real.cos d.thetaB)) (θ i):ℝ):ℂ) := by
    rw [← Complex.ofReal_sum]
    simp [Pi.single_apply,mul_ite]
  have hs2 : (∑ l : Fin N, ((deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ l)*
      ((Pi.single p (1:ℝ) : Fin N → ℝ) l)*((Pi.single i (1:ℝ) : Fin N → ℝ) l):ℝ):ℂ))=
      if p=i then ((deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i):ℝ):ℂ) else 0 := by
    by_cases hpi : p=i
    · subst p; rw [← Complex.ofReal_sum]; simp [Pi.single_apply,mul_ite]
    · rw [← Complex.ofReal_sum]; simp [Pi.single_apply,mul_ite,hpi,Ne.symm hpi]
  rw [hs1] at h1b
  rw [hs2] at h2b
  constructor
  · apply h1b.trans
    calc
      (N:ℝ)*C1*(eps+lam)≤(N:ℝ)*max C1 C2*(eps+lam) := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  · apply h2b.trans
    calc
      (N:ℝ)*C2*(eps+lam)≤(N:ℝ)*max C1 C2*(eps+lam) := by gcongr; exact le_max_right _ _
      _ = _ := by ring

end
end IsingBulk.Tail
