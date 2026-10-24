import IsingBulk.Anisotropic.NegativeCycles.CenteredKernelTaylor
import IsingBulk.Anisotropic.NegativeCycles.ActualCutoffLocalization
import IsingBulk.Anisotropic.NegativeCycles.NormalizedCapIntegralAlgebra
import IsingBulk.Anisotropic.NegativeDominance.CycleEnvelope

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open Set MeasureTheory Metric
set_option maxHeartbeats 1500000

def annularErrorEnvelope (M c L a : ℝ) (m j : ℕ) : ℝ :=
  (2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
    ((8*(2*m+1:ℕ):ℝ)/a)^(j+1)*(2*L)^(2*m)

def centeredRemainderEnvelope (K M c : ℝ) (m j : ℕ) (d s : ℝ) : ℝ :=
  ((volume (centeredInnerSet (2*m) d s)).toReal*(K*remainderGaussianEnvelope M m))/
    ((c/(2*m+1:ℕ))/2)^j

def transformedResidueCap (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (m j : ℕ) (d : ℝ) (T : Config (2*m+1)→ℂ) (Phi : Config (2*m+1)→Config (2*m+1))
    (b : ContDiffBump (0:ℝ)) : ℂ :=
  ∫q : Fin (2*m)→ℝ,(shapeSpatialCutoff b q:ℂ)*
    constrainedResidueDensity B rootB phi hphi (d:ℂ) T j (constrainedMap Phi (complexify (2*m) q))*
      constrainedJacobian Phi (complexify (2*m) q)

theorem norm_two_transport_le (I O C R z : ℂ) :
    ‖2*(I+R)-z‖≤‖2*C-z‖+2*(‖I-O‖+‖C-O‖+‖R‖) := by
  have he : 2*(I+R)-z=(2*C-z)+2*((I-O)-(C-O)+R) := by ring
  rw [he]
  have h1 := norm_add_le (2*C-z) (2*((I-O)-(C-O)+R))
  have h2 := norm_add_le ((I-O)-(C-O)) R
  have h3 := norm_sub_le (I-O) (C-O)
  rw [norm_mul] at h1
  norm_num only [Complex.norm_ofNat] at h1
  linarith

/-- Actual kernel-to-cap comparison. The cap, real localization, genuine Stokes
transport and SAME-R0 remainder are all attached with their exact envelopes. -/
theorem actual_central_transport (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ σ cR KR MR Ma ca La rc Mc cc Lc : ℝ,
      0<ρ ∧ 0<σ ∧ 0<cR ∧ 0<KR ∧ 1≤MR ∧ 1≤Ma ∧ 0<ca ∧ 0<La ∧
      0<rc ∧ 1≤Mc ∧ 0<cc ∧ 0<Lc ∧
      ∀b : ContDiffBump (0:ℝ),b.rOut≤ρ^2 →
      ∃K : ℝ,0≤K ∧ ∀m j : ℕ,0<m → ∀d : ℝ,|d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀s : ℝ,s<σ → b.rOut≤s-(2*m+1:ℕ)*d^2 → ∀z : ℂ,
      ‖2*(iteratedDeriv j (centeredKernelIntegral B rootB phi hphi m d s) 0/(j.factorial:ℂ))-z‖≤
        ‖2*transformedResidueCap B rootB phi hphi m j d P.T (fun y=>P.V (J.W y)) b-z‖+
        2*(annularErrorEnvelope Ma ca La b.rIn m j+
          cycleErrorEnvelope rc Mc cc Lc K b.rIn m j+
          centeredRemainderEnvelope KR MR cR m j d s) := by
  obtain ⟨R₀,a,cR,sigma,KR,MR,ha,hcR,hsigma,hKR,hMR,htaylor⟩ :=
    exists_centered_kernel_taylor B rootB phi hphi hB hBn hroot r C R hr hR hRr
  obtain ⟨ra,Ma,ca,La,hra,hMa,hca,hLa,hann⟩ :=
    actual_inner_cutoff_localization B rootB phi hphi hB hroot hBn r C R hr hR hRr
  obtain ⟨rc,Mc,cc,Lc,hrc,hMc,hcc,hLc,hcycle⟩ :=
    actual_cycle_comparison B rootB phi hphi hB hroot hBn r C R hr hR hRr
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
  intro m j hm d hd hd0 P J s hs hbs z
  have ht := htaylor m d (hd.trans_le hρa) hd0 P J s (hs.trans_le (min_le_left _ _))
  have hsra : s-(2*m+1:ℕ)*d^2≤ra^2 := by
    have hs' := hs.le.trans (min_le_right sigma (ra^2))
    have hn : 0≤(2*m+1:ℕ)*d^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith
  have hloc := hann m j d (hd.trans_le hρra) hd0 P J b (s-(2*m+1:ℕ)*d^2) hbs hsra
  have hcy' := hcy m j hm d (hd.trans_le hρrc) hd0 P J
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

end IsingBulk.Anisotropic.NegativeCycles
