import IsingBulk.Joint.Negative.FamilyCentralCap
import IsingBulk.Joint.Negative.FamilyCycleTransport
import IsingBulk.Anisotropic.NegativeNormalForm.ActualCentralWinding

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open MeasureTheory Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- Actual positive central winding kernel coefficients, not just transformed
caps: the vanishing relative model error and all three genuine analytic error
envelopes hold on one common inner region. The same constructed normal form is
used in the density estimate, Stokes comparison, and real localization. -/
theorem compact_family_central_winding_model_error (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0)
    (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hrootn : ∀eta∈Q,rootB (0,eta)≠0)
    (hsq : ∃s : ℝ,0<s ∧ ∀eta∈Q,∀t : ℂ,‖t‖<s → rootB (t,eta)^2=B (t,eta)) :
    ∃delta sigma cR KR MR Ma ca La rc Mc cc Lc : ℝ,
      0<delta ∧ 0<sigma ∧ 0<cR ∧ 0<KR ∧ 1≤MR ∧ 1≤Ma ∧ 0<ca ∧ 0<La ∧
      0<rc ∧ 1≤Mc ∧ 0<cc ∧ 0<Lc ∧
      ∀b : ContDiffBump (0:ℝ),b.rOut<delta^2 →
      ∃A K : ℝ,0<A ∧ 0<K ∧ ∀s : ℝ,0<s → s<sigma → b.rOut≤s/2 →
      ∀ᶠ m : ℕ in atTop, ∀eta∈Q, ∀j : ℕ,8*(2*m+1)^2≤j →
      let N := 2*m+1
      let d : ℝ := Real.pi/(N:ℝ)
      let M := model (familyMember B eta (tau N)) (familyMember rootB eta (tau N)) (centralHessian (familyMember B eta) phi (d:ℂ)) (Real.sin phi) N j
      ‖2*(iteratedDeriv j (centeredKernelIntegral (familyMember B eta) (familyMember rootB eta) phi hphi m d s) 0/(j.factorial:ℂ))-M‖≤
        A*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))*‖M‖+
        2*(annularErrorEnvelope Ma ca La b.rIn m j+
          cycleErrorEnvelope rc Mc cc Lc K b.rIn m j+
          centeredRemainderEnvelope KR MR cR m j d s) := by
  obtain ⟨delta₀,R,r,Cp,hd₀,hR,hr,hCp,_hdR,hRr,hcap⟩ :=
    compact_family_central_cap_model_error B rootB phi hphi hQ hB hBn hroot hrootn hsq
  obtain ⟨rho,sigma,cR,KR,MR,Ma,ca,La,rc,Mc,cc,Lc,hrho,hsigma,hcR,hKR,hMR,hMa,hca,hLa,
    hrc,hMc,hcc,hLc,htransport⟩ :=
    compact_family_central_transport B rootB phi hphi hQ hB hroot hBn r Cp R hr hR (by linarith)
  let delta := min delta₀ rho
  have hd : 0<delta := lt_min hd₀ hrho
  have hdold : delta≤delta₀ := min_le_left _ _
  have hdrho : delta≤rho := min_le_right _ _
  refine ⟨delta,sigma,cR,KR,MR,Ma,ca,La,rc,Mc,cc,Lc,hd,hsigma,hcR,hKR,hMR,hMa,hca,hLa,
    hrc,hMc,hcc,hLc,?_⟩
  intro b hb
  have hbold := hb.trans_le ((sq_le_sq₀ hd.le hd₀.le).2 hdold)
  have hbrho := hb.le.trans ((sq_le_sq₀ hd.le hrho.le).2 hdrho)
  obtain ⟨A,hA,hcaps⟩ := hcap b hbold
  obtain ⟨K,hK,htransport⟩ := htransport b hbrho
  have htwice : Tendsto (fun m : ℕ=>2*m) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with m hm
    omega
  have hN := (tendsto_add_atTop_nat 1).comp htwice
  have hcaps' := htwice.eventually hcaps
  have hnear : ∀ᶠ N : ℕ in atTop, ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<rho := by
    have hh := winding_angle_complex_tendsto_zero (Metric.ball_mem_nhds (0:ℂ) hrho)
    change ∀ᶠ N : ℕ in atTop, ((Real.pi/(N:ℝ):ℝ):ℂ)∈Metric.ball 0 rho at hh
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hnears := hN.eventually hnear
  refine ⟨A,K+1,hA,by linarith,?_⟩
  intro s hs hsigma' hbs
  have hlarge := (tendsto_natCast_atTop_atTop.comp hN).eventually_ge_atTop (2*Real.pi^2/s)
  filter_upwards [hcaps',hnears,hlarge,eventually_ge_atTop (1:ℕ)] with m hcaps hnear hlarge hm eta heta
  have hcaps := hcaps eta heta
  simp only [Function.comp_def] at hnear hlarge
  intro j hj
  dsimp only
  have ho : Odd (2*m+1) := ⟨m,by omega⟩
  obtain ⟨P,J,hcapj⟩ := hcaps ho
  have hnpos : (0:ℝ)<(2*m+1:ℕ) := by positivity
  have hdpos : 0<Real.pi/(2*m+1:ℕ) := by positivity
  have hdnear : |Real.pi/(2*m+1:ℕ)|<rho := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hnear
  have hshift : (2*m+1:ℕ)*(Real.pi/(2*m+1:ℕ))^2≤s/2 := by
    have hsn := (div_le_iff₀ hs).mp hlarge
    have he : (2*m+1:ℕ)*(Real.pi/(2*m+1:ℕ))^2=Real.pi^2/(2*m+1:ℕ) := by
      field_simp
    rw [he]
    apply (div_le_iff₀ hnpos).2
    nlinarith
  have ht := htransport eta heta m j (by omega) (Real.pi/(2*m+1:ℕ)) hdnear (ne_of_gt hdpos) P J s
    hsigma' (by linarith) (model (familyMember B eta (tau (2*m+1))) (familyMember rootB eta (tau (2*m+1)))
      (centralHessian (familyMember B eta) phi ((Real.pi/(2*m+1:ℕ):ℝ):ℂ)) (Real.sin phi) (2*m+1) j)
  have hcy0 : 0≤cycleErrorEnvelope rc Mc cc Lc 1 b.rIn m j := by
    have hMc0 : 0<Mc := lt_of_lt_of_le zero_lt_one hMc
    have hbin := b.rIn_pos
    unfold cycleErrorEnvelope
    positivity
  have hcy : cycleErrorEnvelope rc Mc cc Lc K b.rIn m j≤
      cycleErrorEnvelope rc Mc cc Lc (K+1) b.rIn m j := by
    have he : cycleErrorEnvelope rc Mc cc Lc (K+1) b.rIn m j=
        cycleErrorEnvelope rc Mc cc Lc K b.rIn m j+
        cycleErrorEnvelope rc Mc cc Lc 1 b.rIn m j := by
      unfold cycleErrorEnvelope
      ring
    rw [he]
    linarith
  exact (ht.trans (add_le_add (hcapj j hj) (le_refl _))).trans (by linarith)

end
end IsingBulk.Joint.Negative
