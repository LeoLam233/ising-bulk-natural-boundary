import IsingBulk.Joint.Negative.FamilyDensityBeta
import IsingBulk.Joint.Negative.FamilyPeriodLoss
import IsingBulk.Joint.Negative.FamilyBetaAbsorption
import IsingBulk.Anisotropic.NegativeNormalForm.ActualDensityBetaUniform

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open MeasureTheory Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- Dimension-uniform complete-density error in the actual central normal form.
The fixed cutoff is chosen before N. Its only eventual order condition is
j≥8N², and the error tends to zero whenever j/N² tends to infinity. -/
theorem compact_family_density_beta_uniform (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0)
    (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hrootn : ∀eta∈Q,rootB (0,eta)≠0) :
    ∃delta R r Cp A : ℝ, 0<delta ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<A ∧
      delta≤R/4 ∧ 4*R≤r ∧
      ∀ b : ContDiffBump (0:ℝ), b.rOut<delta^2 →
      ∀ᶠ m : ℕ in atTop, ∀eta∈Q, Odd (m+1:ℕ) →
      let d : ℂ := ((Real.pi/((m+1:ℕ):ℝ):ℝ):ℂ)
      let c := centralHessian (familyMember B eta) phi d/((2*((m+1:ℕ):ℝ):ℝ):ℂ)
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi (m+1:ℕ) d r Cp,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi (m+1:ℕ) d r Cp P R,
      ∀ j : ℕ,8*(m+1:ℕ)^2≤j →
      ‖∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*
        (normalizedFullDensity (familyMember B eta) (familyMember rootB eta) phi hphi d P.T (fun y=>P.V (J.W y)) (complexify m q)-1)*
        quadraticModelKernel m j (tau (m+1:ℕ)) c q‖≤
          A*(((m+1:ℕ):ℝ)/Real.sqrt j+((m+1:ℕ):ℝ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))*
            ‖shapePeriod m j (tau (m+1:ℕ)) c‖ := by
  obtain ⟨delta,R,r,Cp,C,hd,hR,hr,hCp,hC,hdR,hRr,hex⟩ :=
    compact_family_density_beta_bound B rootB phi hphi hQ hB hBn hroot hrootn
  obtain ⟨F,hF,hphase⟩ := compact_family_central_period_loss B phi hQ hB
  let e := expErrorConstant C 1
  have he : 0<e := by dsimp [e,expErrorConstant]; positivity
  let A := F*(e+1)
  have hA : 0<A := mul_pos hF (by linarith)
  refine ⟨delta,R,r,Cp,A,hd,hR,hr,hCp,hA,hdR,hRr,?_⟩
  intro b hb
  have hab := compact_family_beta_absorption B phi hQ hB C b.rOut hC.le b.rOut_pos
  have hnear : ∀ᶠ N : ℕ in atTop, ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<delta := by
    have hh := winding_angle_complex_tendsto_zero (Metric.ball_mem_nhds (0:ℂ) hd)
    change ∀ᶠ N : ℕ in atTop, ((Real.pi/(N:ℝ):ℝ):ℂ)∈Metric.ball 0 delta at hh
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  have habs := (tendsto_add_atTop_nat 1).eventually hab
  have hphases := (tendsto_add_atTop_nat 1).eventually hphase
  have hnears := (tendsto_add_atTop_nat 1).eventually hnear
  filter_upwards [habs,hphases,hnears,eventually_ge_atTop (2:ℕ)] with m hab hphase hnear hm eta heta ho
  have hab := hab eta heta
  have hphase := hphase eta heta
  dsimp only
  let N := m+1
  have hN : 3≤N := by dsimp [N]; omega
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hangle : Real.pi/(N:ℝ)<delta := by
    change ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<delta at hnear
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<Real.pi/(N:ℝ))] using hnear
  have hfinite := hex eta heta m ho hm hangle
  obtain ⟨P,J,_hhalf,hint⟩ := hfinite
  refine ⟨P,J,?_⟩
  intro j hj
  have ha := (alpha_pos_and_twice_le N hN).2
  have hjN : 8*N^2≤j := hj
  have hj4 : 4*alpha N+4≤j := by nlinarith
  have hh := hint b hb j (j/4) hj4 (by omega) (hab j hj).2
  have hbeta := betaDensityError_dimension N j hN hj C hC.le
  have hden : 0<(j:ℝ)-alpha N := by
    have hjR : (alpha N:ℝ)<j := by exact_mod_cast (show alpha N<j by omega)
    linarith
  have hb0 : 0≤betaDensityErrorBound N j (j/4) C := by
    unfold betaDensityErrorBound expErrorConstant
    positivity
  have hm := mul_le_mul hphase.2 hbeta hb0 hF.le
  have hterm : 0≤(N:ℝ)/Real.sqrt j+(N:ℝ)^2/j := by positivity
  have hscale : F*(expErrorConstant C 1*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j)+
      Real.exp (-(j:ℝ)*Real.log 2/8))≤
      A*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8)) := by
    change F*(e*_+_)≤_
    dsimp [A]
    have hmul := mul_nonneg he.le (Real.exp_pos (-(j:ℝ)*Real.log 2/8)).le
    apply (mul_le_mul_of_nonneg_left (show e*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j)+
      Real.exp (-(j:ℝ)*Real.log 2/8)≤(e+1)*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j+
        Real.exp (-(j:ℝ)*Real.log 2/8)) by nlinarith) hF.le).trans_eq
    ring
  exact hh.trans (mul_le_mul_of_nonneg_right (hm.trans hscale) (norm_nonneg _))

end
end IsingBulk.Joint.Negative
