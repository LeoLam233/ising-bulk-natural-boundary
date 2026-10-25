import IsingBulk.Joint.Negative.FamilyCycleIntegralTransport
import IsingBulk.Joint.Negative.FamilyCycleAnnularIntegral
import IsingBulk.Anisotropic.NegativeCycles.ActualCycleComparison

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_cycle_comparison (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ M c L : ℝ,0<ρ ∧ 1≤M ∧ 0<c ∧ 0<L ∧
      ∀bump : ContDiffBump (0:ℝ), bump.rOut≤ρ^2 →
      ∃K : ℝ,0≤K ∧ ∀ eta∈Q, ∀m j : ℕ,0<m → ∀d : ℝ, |d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C P R,
      let Phi := fun y => P.V (J.W y)
      let f := constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j
      ‖(∫q in Icc (fun _ : Fin (2*m) => -ρ) (fun _ => ρ),
        (shapeSpatialCutoff bump q:ℂ)*f (constrainedMap Phi (complexify (2*m) q))*
          constrainedJacobian Phi (complexify (2*m) q))-
      (∫q in Icc (fun _ : Fin (2*m) => -ρ) (fun _ => ρ),
        (shapeSpatialCutoff bump q:ℂ)*f (complexify (2*m) q))‖≤
        ((((2*m:ℕ):ℝ)+1)*K*
          ((2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
            ((8*(2*m+1:ℕ):ℝ)/bump.rIn)^(j+1))*
          Real.sqrt (((2*m:ℕ)*L^2)^(2*m)))*(2*ρ)^(2*m) := by
  obtain ⟨a,ha,htransport⟩ := compact_family_residue_integral_transport B rootB phi hphi hQ hB hroot hBn r C R hr hR hRr
  obtain ⟨b,M,c,hb,hM,hc,hbound⟩ := compact_family_annular_integral_bound B rootB phi hphi hQ hB hroot hBn r C R hr hR hRr
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
  intro eta heta m j hm d hd hd0 P J
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  dsimp only
  let lo : ParameterSpace (2*m) := Fin.cons 0 (fun _ => -ρ)
  let hi : ParameterSpace (2*m) := Fin.cons 1 (fun _ => ρ)
  have hlo : lo≤hi := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · norm_num [lo,hi]
    · simp only [lo,hi,Fin.cons_succ]; linarith
  have ht := htransport eta heta m d (hd.trans_le hρa) hd0 P J j bump (hbump.trans hqa) lo hi hlo rfl rfl
    (fun _ => hbump) (fun _ => by simpa only [lo,Fin.cons_succ,neg_sq] using hbump)
  have he := herror eta heta m j hm d (hd.trans_le hρb) P J lo hi rfl rfl
  have hv : (volume (Icc lo hi)).toReal=(2*ρ)^(2*m) := by
    rw [Real.volume_Icc_pi_toReal hlo,Fin.prod_univ_succ]
    simp [lo,hi,sub_neg_eq_add,two_mul]
  rw [hv] at he
  dsimp only at ht he
  simpa only [lo,hi,Fin.cons_succ] using (ht.symm ▸ he)


end
end IsingBulk.Joint.Negative
