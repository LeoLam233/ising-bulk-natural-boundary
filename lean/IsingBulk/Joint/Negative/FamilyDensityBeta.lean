import IsingBulk.Joint.Negative.FamilyDensityFull
import IsingBulk.Joint.Negative.FamilyHessianBounds
import IsingBulk.Anisotropic.NegativeNormalForm.ActualDensityBeta

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open MeasureTheory IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
/-- Actual complete central density integrated against the true complex model
kernel. All normal-form witnesses and all pointwise bounds are constructed;
the only order restriction beyond convergence is the explicit beta-tail
absorption inequality. The cutoff radius is fixed before the dimension. -/
theorem compact_family_density_beta_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0)
    (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hrootn : ∀eta∈Q,rootB (0,eta)≠0) :
    ∃delta R r Cp C : ℝ, 0<delta ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<C ∧
      delta≤R/4 ∧ 4*R≤r ∧
      ∀eta∈Q,∀ m : ℕ,Odd (m+1) → 2≤m → Real.pi/(m+1:ℕ)<delta →
      let d : ℂ := ((Real.pi/(m+1:ℕ):ℝ):ℂ)
      let c := centralHessian (familyMember B eta) phi d/((2*(m+1:ℕ):ℝ):ℂ)
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi (m+1) d r Cp,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi (m+1) d r Cp P R,
      (1:ℝ)/2≤(centralHessian (familyMember B eta) phi d).re ∧
      ∀ b : ContDiffBump (0:ℝ), b.rOut<delta^2 →
      let L := 1+c.re*b.rOut/tau (m+1)
      ∀ j k : ℕ,4*alpha (m+1)+4≤j → k≤j-j/2 →
        C*(Real.sqrt L+L)≤(k:ℝ)*Real.log 2 →
      ‖∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*
        (normalizedFullDensity (familyMember B eta) (familyMember rootB eta) phi hphi d P.T (fun y=>P.V (J.W y)) (complexify m q)-1)*
        quadraticModelKernel m j (tau (m+1)) c q‖≤
          (‖c‖/c.re)^alpha (m+1)*betaDensityErrorBound (m+1) j k C*
            ‖shapePeriod m j (tau (m+1)) c‖ := by
  obtain ⟨delta0,R,r,Cp,K,hd0,hR,hr,hCp,hK,hd0R,hRr,hex⟩ :=
    compact_family_full_density_envelope B rootB phi hphi hQ hB hBn hroot hrootn Real.pi Real.pi_pos.le
  obtain ⟨rh,Lh,hrh,_hLh,hH⟩ := compact_family_hessian_period_loss B phi hQ hB
  let delta := min delta0 rh
  have hd : 0<delta := lt_min hd0 hrh
  have hdd : delta≤delta0 := min_le_left _ _
  have hdr : delta≤rh := min_le_right _ _
  let C := 2*K*(2*Real.pi^2+1)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨delta,R,r,Cp,C,hd,hR,hr,hCp,hC,hdd.trans hd0R,hRr,?_⟩
  intro eta heta m ho hm hang
  let d : ℂ := ((Real.pi/(m+1:ℕ):ℝ):ℂ)
  let c := centralHessian (familyMember B eta) phi d/((2*(m+1:ℕ):ℝ):ℂ)
  have hnorm : ‖d‖=Real.pi/(m+1:ℕ) := by
    dsimp [d]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hdsmall : ‖d‖<delta := hnorm ▸ hang
  have hnd : (m+1:ℕ)*‖d‖≤Real.pi := by rw [hnorm]; field_simp; rfl
  obtain ⟨P,J,hfull⟩ := hex eta heta m d (hdsmall.trans_le hdd) hnd
  have hhalf := (hH eta heta (m+1) (by omega) d (hdsmall.trans_le hdr)).1
  refine ⟨P,J,hhalf,?_⟩
  intro b hb
  dsimp only
  intro j k hj hkj habs
  have hc : 0<c.re := by
    dsimp [c]
    rw [Complex.div_ofReal_re]
    exact div_pos (by linarith) (by positivity)
  have ht := tau_pos (m+1) (by omega)
  have hL : 1≤1+c.re*b.rOut/tau (m+1) := by
    have hbpos := b.rOut_pos
    have hp : 0≤c.re*b.rOut/tau (m+1) := by positivity
    linarith
  apply complexDensityError_beta_bound ho hm j k hj hkj (tau (m+1)) c C
    (1+c.re*b.rOut/tau (m+1)) ht hc hC.le hL habs
  intro q
  have he := fullDensity_beta_pointwise (familyMember B eta) (familyMember rootB eta) phi hphi d r Cp R delta K P J hd hK.le
    (centralHessian (familyMember B eta) phi d) hhalf
    (fun u hu => (hfull u (hu.trans_le hdd)).2) b hb q
  exact he

end
end IsingBulk.Joint.Negative
