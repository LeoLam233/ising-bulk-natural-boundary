import IsingBulk.Anisotropic.NegativeCycles.ActualAnnularIntegralBound

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory

/-- Genuine dimension-uniform complex-cycle comparison with explicit Gaussian error. -/
theorem actual_cycle_comparison (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ M c L : ℝ,0<ρ ∧ 1≤M ∧ 0<c ∧ 0<L ∧
      ∀bump : ContDiffBump (0:ℝ), bump.rOut≤ρ^2 →
      ∃K : ℝ,0≤K ∧ ∀m j : ℕ,0<m → ∀d : ℝ, |d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      let Phi := fun y => P.V (J.W y)
      let f := constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
      ‖(∫q in Icc (fun _ : Fin (2*m) => -ρ) (fun _ => ρ),
        (shapeSpatialCutoff bump q:ℂ)*f (constrainedMap Phi (complexify (2*m) q))*
          constrainedJacobian Phi (complexify (2*m) q))-
      (∫q in Icc (fun _ : Fin (2*m) => -ρ) (fun _ => ρ),
        (shapeSpatialCutoff bump q:ℂ)*f (complexify (2*m) q))‖≤
        ((((2*m:ℕ):ℝ)+1)*K*
          ((2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
            ((8*(2*m+1:ℕ):ℝ)/bump.rIn)^(j+1))*
          Real.sqrt (((2*m:ℕ)*L^2)^(2*m)))*(2*ρ)^(2*m) := by
  obtain ⟨a,ha,htransport⟩ := actual_residue_integral_transport B rootB phi hphi hB hroot hBn r C R hr hR hRr
  obtain ⟨b,M,c,hb,hM,hc,hbound⟩ := actual_annular_integral_uniform_bound B rootB phi hphi hB hroot hBn r C R hr hR hRr
  let ρ := min a b
  have hρ : 0<ρ := lt_min ha hb
  have hρa : ρ≤a := min_le_left _ _
  have hρb : ρ≤b := min_le_right _ _
  have hqa : ρ^2≤a^2 := by nlinarith
  have hqb : ρ^2≤b^2 := by nlinarith
  refine ⟨ρ,M,c,2+b,hρ,hM,hc,by linarith,?_⟩
  intro bump hbump
  obtain ⟨K,hK,herror⟩ := hbound bump (hbump.trans hqb)
  refine ⟨K,hK,?_⟩
  intro m j hm d hd hd0 P J
  dsimp only
  let lo : ParameterSpace (2*m) := Fin.cons 0 (fun _ => -ρ)
  let hi : ParameterSpace (2*m) := Fin.cons 1 (fun _ => ρ)
  have hlo : lo≤hi := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · norm_num [lo,hi]
    · simp only [lo,hi,Fin.cons_succ]; linarith
  have ht := htransport m d (hd.trans_le hρa) hd0 P J j bump (hbump.trans hqa) lo hi hlo rfl rfl
    (fun _ => hbump) (fun _ => by simpa only [lo,Fin.cons_succ,neg_sq] using hbump)
  have he := herror m j hm d (hd.trans_le hρb) P J lo hi rfl rfl
  have hv : (volume (Icc lo hi)).toReal=(2*ρ)^(2*m) := by
    rw [Real.volume_Icc_pi_toReal hlo,Fin.prod_univ_succ]
    simp [lo,hi,sub_neg_eq_add,two_mul]
  rw [hv] at he
  dsimp only at ht he
  simpa only [lo,hi,Fin.cons_succ] using (ht.symm ▸ he)

end IsingBulk.Anisotropic.NegativeCycles
