import IsingBulk.Joint.Negative.FamilyCycleScalar

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 800000

theorem compact_family_cycle_density_joint_analytic (B rootB : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta)) :
    ∃r : ℝ,0<r ∧ ∀ eta∈Q, ∀m : ℕ, ∀d T : ℂ, ∀v : Config (2*m+1),
      ‖T‖<r → (∀i, ‖d+v i‖<r) →
      AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi d z.2 z.1) (v,T) ∧
      AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => poleEquation (familyMember B eta) phi hphi d z.2 z.1) (v,T) := by
  obtain ⟨r,hr,hall⟩ := compact_family_cycle_scalar_analytic B rootB phi hphi hQ hB hroot
  refine ⟨r,hr,?_⟩
  intro eta heta m d T v hT hv
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  have hscalar : AnalyticAt ℂ B T ∧ AnalyticAt ℂ rootB T := (hall eta heta).1 T hT
  have hphase (i : Fin (2*m+1)) : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => negativePhase B phi hphi z.2 (d+z.1 i)) (v,T) := by
    exact ((hall eta heta).2.1 T (d+v i) hT (hv i)).1.comp_of_eq (f := fun z : Config (2*m+1) × ℂ => (z.2,d+z.1 i)) (analyticAt_snd.prod (analyticAt_const.add ((ContinuousLinearMap.proj i : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst))) rfl
  have hone (i : Fin (2*m+1)) : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => (Complex.sinh (negativePhase B phi hphi z.2 (d+z.1 i)))⁻¹) (v,T) := by
    exact ((hall eta heta).2.1 T (d+v i) hT (hv i)).2.comp_of_eq (f := fun z : Config (2*m+1) × ℂ => (z.2,d+z.1 i)) (analyticAt_snd.prod (analyticAt_const.add ((ContinuousLinearMap.proj i : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst))) rfl
  have hpair (i j : Fin (2*m+1)) :
      AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => localCompletePair B phi hphi z.2 (d+z.1 i) (d+z.1 j)) (v,T) := by
    exact ((hall eta heta).2.2 T (d+v i) (d+v j) hT (hv i) (hv j)).comp_of_eq (f := fun z : Config (2*m+1) × ℂ => (z.2,d+z.1 i,d+z.1 j)) (analyticAt_snd.prod ((analyticAt_const.add ((ContinuousLinearMap.proj i : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst)).prod (analyticAt_const.add ((ContinuousLinearMap.proj j : Config (2*m+1) →L[ℂ] ℂ).analyticAt _ |>.comp (f := fun z : Config (2*m+1) × ℂ => z.1) analyticAt_fst)))) rfl
  constructor
  · have hpre : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => rootB z.2*B z.2^m / (((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))) (v,T) :=
      by
        have hb : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => B z.2) (v,T) := hscalar.1.comp_of_eq analyticAt_snd rfl
        have hr : AnalyticAt ℂ (fun z : Config (2*m+1) × ℂ => rootB z.2) (v,T) := hscalar.2.comp_of_eq analyticAt_snd rfl
        exact (hr.mul (hb.pow m)).div_const
    have ha := hpre.mul
      (Finset.univ.analyticAt_fun_prod (fun i _ => hone i))
    have hh := ha.mul ((firstStrictPairs (2*m+1)).analyticAt_fun_prod (fun p _ => hpair p.1 p.2))
    apply hh.congr
    exact Filter.Eventually.of_forall (fun z => (formFactorNumerator_odd_complete_pairs m B rootB phi hphi d z.2 z.1).symm)
  · unfold poleEquation
    exact Finset.univ.analyticAt_fun_sum (fun i _ => (hphase i).sub analyticAt_const)


end
end IsingBulk.Joint.Negative
