import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedAngles
import IsingBulk.First.MeanCoordinates

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators

theorem wrapAngle_sub_int_period (a : ℝ) (k : ℤ) :
    wrapAngle (a-(k:ℝ)*(2*Real.pi))=wrapAngle a := by
  simp [wrapAngle,Real.Angle.coe_sub,Real.Angle.intCast_mul_eq_zsmul,Real.Angle.coe_two_pi]

/-- Exact dependent-angle arithmetic, retaining the winding integer. -/
theorem physicalDependentAngles_winding (n : ℕ) (d : ℝ) (k : ℤ)
    (hk : (n+1:ℕ)*(Real.pi+d)=(k:ℝ)*(2*Real.pi))
    (v : Fin n→ℝ) (i : Fin (n+1)) :
    wrapAngle (physicalDependentAngles n (fun j => v j+Real.pi+d) i)=
      wrapAngle (Real.pi+d+shapeExtend v i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [physicalDependentAngles,Fin.snoc_last,shapeExtend_last,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have he : -((∑j,v j)+(n:ℝ)*Real.pi+(n:ℝ)*d)=
        Real.pi+d+(-(∑j,v j))-(k:ℝ)*(2*Real.pi) := by
      push_cast at hk
      linarith
    rw [he,wrapAngle_sub_int_period]
  · simp only [physicalDependentAngles,Fin.snoc_castSucc,shapeExtend_castSucc]
    congr 1
    ring

/-- The shifted physical family has center d, not zero, in an odd winding sector. -/
theorem negativeShiftedAngles_winding (n : ℕ) (d : ℝ) (k : ℤ)
    (hk : (n+1:ℕ)*(Real.pi+d)=(k:ℝ)*(2*Real.pi))
    (v : Fin n→ℝ) (i : Fin (n+1)) :
    negativeShiftedAngles n (fun j => d+v j) i=wrapAngle (d+shapeExtend v i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [negativeShiftedAngles_last,shapeExtend_last]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have he : -((n:ℝ)*d+(∑j,v j))-(n+1:ℕ)*Real.pi=
        d+(-(∑j,v j))-(k:ℝ)*(2*Real.pi) := by
      push_cast at hk ⊢
      linarith
    rw [he,wrapAngle_sub_int_period]
  · simp

/-- The two nearest winding centers for odd N. -/
theorem odd_winding_centers (m : ℕ) :
    (2*m+1:ℕ)*(Real.pi+Real.pi/(2*m+1:ℕ))=((m+1:ℕ):ℝ)*(2*Real.pi) ∧
    (2*m+1:ℕ)*(Real.pi-Real.pi/(2*m+1:ℕ))=(m:ℝ)*(2*Real.pi) := by
  have hn : ((2*m+1:ℕ):ℝ)≠0 := by positivity
  constructor <;> push_cast <;> field_simp <;> ring

end IsingBulk.Anisotropic.NegativeCycles
