import IsingBulk.Anisotropic.NegativeCycles.WindingSectors
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory
open scoped BigOperators

theorem wrapAngle_measurable : Measurable wrapAngle := by
  unfold wrapAngle
  simp_rw [Real.Angle.toReal_coe,toIocMod,toIocDiv_eq_neg_floor,zsmul_eq_mul]
  fun_prop

theorem negativeShiftedAngles_measurable (n : ℕ) (i : Fin (n+1)) :
    Measurable (fun v : Fin n→ℝ => negativeShiftedAngles n v i) := by
  unfold negativeShiftedAngles
  apply wrapAngle_measurable.comp
  apply Continuous.measurable
  exact (((continuous_apply i).comp (physicalDependentAngles_continuous n)).comp
    (continuous_pi (fun j => (continuous_apply j).add continuous_const))).sub continuous_const

def windingSector (n : ℕ) (k : Fin (n+2)) : Set (Fin n→ℝ) :=
  {v | (∑i,negativeShiftedAngles n v i)=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi}

theorem windingSector_measurable (n : ℕ) (k : Fin (n+2)) : MeasurableSet (windingSector n k) := by
  apply measurableSet_eq_fun
  · exact Finset.measurable_sum _ (fun i _ => negativeShiftedAngles_measurable n i)
  · exact measurable_const

theorem windingSector_pairwise_disjoint (n : ℕ) : Pairwise (fun k l => Disjoint (windingSector n k) (windingSector n l)) := by
  intro k l hkl
  apply disjoint_left.mpr
  intro v hk hl
  have hk' := hk
  have hl' := hl
  change (∑i,negativeShiftedAngles n v i)=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi at hk'
  change (∑i,negativeShiftedAngles n v i)=(2*(l.val:ℝ)-(n+1:ℕ))*Real.pi at hl'
  have he : (k.val:ℝ)=(l.val:ℝ) := by nlinarith [Real.pi_pos]
  apply hkl
  apply Fin.ext
  exact_mod_cast he

theorem windingSector_iUnion (n : ℕ) : (⋃k, windingSector n k)=univ := by
  apply eq_univ_of_forall
  intro v
  obtain ⟨k,hk0,hkN,hk⟩ := negativeShiftedAngles_finite_winding n v
  have hcast : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hk0
  have hkR : (k.toNat:ℝ)=(k:ℝ) := by exact_mod_cast hcast
  apply mem_iUnion.mpr
  refine ⟨⟨k.toNat,by omega⟩,?_⟩
  change (∑i,negativeShiftedAngles n v i)=(2*(k.toNat:ℝ)-(n+1:ℕ))*Real.pi
  rw [hkR,hk]

/-- Exact finite winding decomposition of any integrable localized physical integral. -/
theorem integral_winding_partition (n : ℕ) {U : Set (Fin n→ℝ)} (hU : MeasurableSet U)
    {f : (Fin n→ℝ)→ℂ} (hf : IntegrableOn f U) :
    (∫v in U,f v)=∑k : Fin (n+2),∫v in U∩windingSector n k,f v := by
  have hu : (⋃k : Fin (n+2), U∩windingSector n k)=U := by
    rw [←inter_iUnion,windingSector_iUnion,inter_univ]
  nth_rw 1 [←hu]
  apply integral_iUnion_fintype
  · intro k
    exact hU.inter (windingSector_measurable n k)
  · intro k l hkl
    exact ((windingSector_pairwise_disjoint n) hkl).mono inter_subset_right inter_subset_right
  · intro k
    exact hf.mono_set inter_subset_left

end IsingBulk.Anisotropic.NegativeCycles
