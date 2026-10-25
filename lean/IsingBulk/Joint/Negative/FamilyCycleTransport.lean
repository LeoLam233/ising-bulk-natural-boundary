import IsingBulk.Joint.Negative.FamilyCycleKernelTaylor
import IsingBulk.Joint.Negative.FamilyCycleLocalization
import IsingBulk.Joint.Negative.FamilyCycleComparison
import IsingBulk.Anisotropic.NegativeCycles.ActualCentralTransport

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_central_transport (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ σ cR KR MR Ma ca La rc Mc cc Lc : ℝ,
      0<ρ ∧ 0<σ ∧ 0<cR ∧ 0<KR ∧ 1≤MR ∧ 1≤Ma ∧ 0<ca ∧ 0<La ∧
      0<rc ∧ 1≤Mc ∧ 0<cc ∧ 0<Lc ∧
      ∀b : ContDiffBump (0:ℝ),b.rOut≤ρ^2 →
      ∃K : ℝ,0≤K ∧ ∀ eta∈Q, ∀m j : ℕ,0<m → ∀d : ℝ,|d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀s : ℝ,s<σ → b.rOut≤s-(2*m+1:ℕ)*d^2 → ∀z : ℂ,
      ‖2*(iteratedDeriv j (centeredKernelIntegral (familyMember B eta) (familyMember rootB eta) phi hphi m d s) 0/(j.factorial:ℂ))-z‖≤
        ‖2*transformedResidueCap (familyMember B eta) (familyMember rootB eta) phi hphi m j d P.T (fun y=>P.V (J.W y)) b-z‖+
        2*(annularErrorEnvelope Ma ca La b.rIn m j+
          cycleErrorEnvelope rc Mc cc Lc K b.rIn m j+
          centeredRemainderEnvelope KR MR cR m j d s) := by
  obtain ⟨R₀,a,cR,sigma,KR,MR,ha,hcR,hsigma,hKR,hMR,htaylor⟩ :=
    compact_family_centered_kernel_taylor B rootB phi hphi hQ hB hBn hroot r C R hr hR hRr
  obtain ⟨ra,Ma,ca,La,hra,hMa,hca,hLa,hann⟩ :=
    compact_family_inner_cutoff_localization B rootB phi hphi hQ hB hroot hBn r C R hr hR hRr
  obtain ⟨rc,Mc,cc,Lc,hrc,hMc,hcc,hLc,hcycle⟩ :=
    compact_family_cycle_comparison B rootB phi hphi hQ hB hroot hBn r C R hr hR hRr
  let ρ := min a (min ra rc)
  have hρ : 0<ρ := lt_min ha (lt_min hra hrc)
  have hρa : ρ≤a := min_le_left _ _
  have hρra : ρ≤ra := (min_le_right _ _).trans (min_le_left _ _)
  have hρrc : ρ≤rc := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,min sigma (ra^2),cR,KR,MR,Ma,ca,La,rc,Mc,cc,Lc,hρ,
    lt_min hsigma (sq_pos_of_pos hra),hcR,hKR,hMR,hMa,hca,hLa,hrc,hMc,hcc,hLc,?_⟩
  intro b hb
  have hbcycle : b.rOut≤rc^2 := hb.trans ((sq_le_sq₀ hρ.le hrc.le).2 hρrc)
  obtain ⟨K,hK,hcy⟩ := hcycle b hbcycle
  refine ⟨K,hK,?_⟩
  intro eta heta m j hm d hd hd0 P J s hs hbs z
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  have ht := htaylor eta heta m d (hd.trans_le hρa) hd0 P J s (hs.trans_le (min_le_left _ _))
  have hsra : s-(2*m+1:ℕ)*d^2≤ra^2 := by
    have hs' := hs.le.trans (min_le_right sigma (ra^2))
    have hn : 0≤(2*m+1:ℕ)*d^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith
  have hloc := hann eta heta m j d (hd.trans_le hρra) hd0 P J b (s-(2*m+1:ℕ)*d^2) hbs hsra
  have hcy' := hcy eta heta m j hm d (hd.trans_le hρrc) hd0 P J
  dsimp only at hloc hcy'
  have hbox (g : (Fin (2*m)→ℝ)→ℂ) := shape_cutoff_integral_box b rc hrc.le hbcycle g
  have hcapbox : (∫q in Icc (fun _ : Fin (2*m)=>-rc) (fun _=>rc),
      (shapeSpatialCutoff b q:ℂ)*constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
        (constrainedMap (fun y=>P.V (J.W y)) (complexify (2*m) q))*
        constrainedJacobian (fun y=>P.V (J.W y)) (complexify (2*m) q))=
      transformedResidueCap B rootB phi hphi m j d P.T (fun y=>P.V (J.W y)) b := by
    simpa only [transformedResidueCap,mul_assoc] using
      hbox (fun q=>constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
        (constrainedMap (fun y=>P.V (J.W y)) (complexify (2*m) q))*
        constrainedJacobian (fun y=>P.V (J.W y)) (complexify (2*m) q))
  rw [hcapbox,hbox] at hcy'
  rw [(ht.2.2 j).2]
  have hn := norm_two_transport_le
    (∫q in centeredInnerSet (2*m) d s,constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q))
    (∫q,(shapeSpatialCutoff b q:ℂ)*constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q))
    (transformedResidueCap B rootB phi hphi m j d P.T (fun y=>P.V (J.W y)) b)
    (iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m d s P.T) 0/(j.factorial:ℂ)) z
  have hrem := ht.2.1 j
  dsimp only [centeredInnerSet,annularErrorEnvelope,cycleErrorEnvelope,centeredRemainderEnvelope] at hn ⊢
  simp only [centeredInnerSet,mul_assoc] at hrem hcy' hloc ⊢
  linarith

end
end IsingBulk.Joint.Negative
