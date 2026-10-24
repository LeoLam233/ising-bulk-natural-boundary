import IsingBulk.Anisotropic.NegativeNormalForm.CapErrorAlgebra
import IsingBulk.Anisotropic.NegativeNormalForm.CentralResidueSequence
import IsingBulk.Anisotropic.NegativeCycles.ActualModelTail

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- The exact split normalized cap, with its actual physical center, is
approximated by M. The integral cap identity attaches this expression to the
literal transformed residue cap without any change of constants. -/
theorem exists_actual_normalized_model_error (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (hrBn : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0:ℂ),rootB t^2=B t) :
    ∃delta R r Cp A : ℝ, 0<delta ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<A ∧
      delta≤R/4 ∧ 4*R≤r ∧
      ∀ b : ContDiffBump (0:ℝ), b.rOut<delta^2 →
      ∃Ct : ℝ,0<Ct ∧ ∀ᶠ m : ℕ in atTop, Odd (m+1) →
      let d : ℂ := ((Real.pi/(m+1:ℕ):ℝ):ℂ)
      let H := centralHessian B phi d
      let c := H/((2*(m+1:ℕ):ℝ):ℂ)
      ∃ P : UniformProjectedWitness B phi hphi (m+1) d r Cp,
      ∃ J : UniformCorrectionWitness B phi hphi (m+1) d r Cp P R,
      regularResidue B rootB phi hphi d P.T 0≠0 ∧
      ∀j : ℕ,8*(m+1)^2≤j →
      let M := model (B (tau (m+1))) (rootB (tau (m+1))) H (Real.sin phi) (m+1) j
      let cut := ∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*quadraticModelKernel m j (tau (m+1)) c q
      let error := ∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*
        (normalizedFullDensity B rootB phi hphi d P.T (fun y=>P.V (J.W y)) (complexify m q)-1)*
        quadraticModelKernel m j (tau (m+1)) c q
      ‖2*(regularResidue B rootB phi hphi d P.T 0*(cut+error))-M‖≤
        (A*((m+1:ℕ)/Real.sqrt j+(m+1:ℕ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))+
          Ct*(1/2:ℝ)^j)*‖M‖ := by
  obtain ⟨delta,R,r,Cp,A,hd,hR,hr,hCp,hA,hdR,hRr,hdens⟩ :=
    exists_actual_density_beta_uniform B rootB phi hphi hB hBn hrB hrBn
  have hcent := (tendsto_add_atTop_nat 1).eventually
    (central_residue_sequence_eventually B rootB phi hphi hB hBn hrB hrBn hsq)
  refine ⟨delta,R,r,Cp,A,hd,hR,hr,hCp,hA,hdR,hRr,?_⟩
  intro b hb
  obtain ⟨Ct,hCt,htail⟩ := actual_model_cutoff_eventually B phi hB b
  have htails := (tendsto_add_atTop_nat 1).eventually htail
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hdens b hb,hcent,htails,eventually_ge_atTop (2:ℕ)] with m hdens hcent htail hm ho
  dsimp only
  obtain ⟨P,J,hdens⟩ := hdens ho
  have hcenter := hcent ho P.T P.t_zero
  refine ⟨P,J,hcenter.2.1,?_⟩
  intro j hj
  have ha := (alpha_pos_and_twice_le (m+1) (by omega)).2
  have haj : 2*alpha (m+1)≤j := by nlinarith
  have hperiod := hcenter.2.2 j (by omega)
  have htailj := htail ho j haj
  simp only [Nat.add_sub_cancel] at hperiod htailj
  have hc : (centralHessian B phi ((Real.pi/(m+1:ℕ):ℝ):ℂ)/(2*(m+1:ℕ):ℂ))=
      centralHessian B phi ((Real.pi/(m+1:ℕ):ℝ):ℂ)/((2*(m+1:ℕ):ℝ):ℂ) := by
    congr 1
    push_cast
    rfl
  rw [hc] at hperiod htailj
  exact centered_cap_model_error _ _ _ _ _ _ _ _ rfl hperiod (hdens j hj) htailj

end
end IsingBulk.Anisotropic.NegativeNormalForm
