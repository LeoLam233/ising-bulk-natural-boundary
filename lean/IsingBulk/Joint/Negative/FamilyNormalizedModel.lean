import IsingBulk.Joint.Negative.FamilyDensityBetaUniform
import IsingBulk.Joint.Negative.FamilyCentralResidue
import IsingBulk.Joint.Negative.FamilyModelTail
import IsingBulk.Anisotropic.NegativeNormalForm.ActualNormalizedModel

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open MeasureTheory Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- The exact split normalized cap, with its actual physical center, is
approximated by M. The integral cap identity attaches this expression to the
literal transformed residue cap without any change of constants. -/
theorem compact_family_normalized_model_error (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0)
    (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hrootn : ∀eta∈Q,rootB (0,eta)≠0)
    (hsq : ∃s : ℝ,0<s ∧ ∀eta∈Q,∀t : ℂ,‖t‖<s → rootB (t,eta)^2=B (t,eta)) :
    ∃delta R r Cp A : ℝ, 0<delta ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<A ∧
      delta≤R/4 ∧ 4*R≤r ∧
      ∀ b : ContDiffBump (0:ℝ), b.rOut<delta^2 →
      ∃Ct : ℝ,0<Ct ∧ ∀ᶠ m : ℕ in atTop, ∀eta∈Q, Odd (m+1) →
      let d : ℂ := ((Real.pi/(m+1:ℕ):ℝ):ℂ)
      let H := centralHessian (familyMember B eta) phi d
      let c := H/((2*(m+1:ℕ):ℝ):ℂ)
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi (m+1) d r Cp,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi (m+1) d r Cp P R,
      regularResidue (familyMember B eta) (familyMember rootB eta) phi hphi d P.T 0≠0 ∧
      ∀j : ℕ,8*(m+1)^2≤j →
      let M := model (familyMember B eta (tau (m+1))) (familyMember rootB eta (tau (m+1))) H (Real.sin phi) (m+1) j
      let cut := ∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*quadraticModelKernel m j (tau (m+1)) c q
      let error := ∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*
        (normalizedFullDensity (familyMember B eta) (familyMember rootB eta) phi hphi d P.T (fun y=>P.V (J.W y)) (complexify m q)-1)*
        quadraticModelKernel m j (tau (m+1)) c q
      ‖2*(regularResidue (familyMember B eta) (familyMember rootB eta) phi hphi d P.T 0*(cut+error))-M‖≤
        (A*((m+1:ℕ)/Real.sqrt j+(m+1:ℕ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))+
          Ct*(1/2:ℝ)^j)*‖M‖ := by
  obtain ⟨delta,R,r,Cp,A,hd,hR,hr,hCp,hA,hdR,hRr,hdens⟩ :=
    compact_family_density_beta_uniform B rootB phi hphi hQ hB hBn hroot hrootn
  have hcent := (tendsto_add_atTop_nat 1).eventually
    (compact_family_central_residue_sequence B rootB phi hphi hQ hB hBn hroot hrootn hsq)
  refine ⟨delta,R,r,Cp,A,hd,hR,hr,hCp,hA,hdR,hRr,?_⟩
  intro b hb
  obtain ⟨Ct,hCt,htail⟩ := compact_family_model_cutoff B phi hQ hB b
  have htails := (tendsto_add_atTop_nat 1).eventually htail
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hdens b hb,hcent,htails,eventually_ge_atTop (2:ℕ)] with m hdens hcent htail hm eta heta ho
  have hdens := hdens eta heta
  have hcent := hcent eta heta
  have htail := htail eta heta
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
  have hc : (centralHessian (familyMember B eta) phi ((Real.pi/(m+1:ℕ):ℝ):ℂ)/(2*(m+1:ℕ):ℂ))=
      centralHessian (familyMember B eta) phi ((Real.pi/(m+1:ℕ):ℝ):ℂ)/((2*(m+1:ℕ):ℝ):ℂ) := by
    congr 1
    push_cast
    rfl
  rw [hc] at hperiod htailj
  exact centered_cap_model_error _ _ _ _ _ _ _ _ rfl hperiod (hdens j hj) htailj

end
end IsingBulk.Joint.Negative
