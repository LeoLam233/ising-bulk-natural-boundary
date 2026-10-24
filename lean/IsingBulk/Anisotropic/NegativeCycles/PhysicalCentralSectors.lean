import IsingBulk.Anisotropic.NegativeCycles.PhysicalIntegralPartition
import IsingBulk.Anisotropic.NegativeCycles.FullWindingReflection

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 800000

def negativeCentralIndex (m : ℕ) : Fin (2*m+2) := ⟨m,by omega⟩
def positiveCentralIndex (m : ℕ) : Fin (2*m+2) := ⟨m+1,by omega⟩

theorem negativeCentralIndex_ne_positive (m : ℕ) : negativeCentralIndex m≠positiveCentralIndex m := by
  intro he
  have := congrArg Fin.val he
  simp only [negativeCentralIndex,positiveCentralIndex] at this
  omega

theorem negativeCentral_windingMean (m : ℕ) :
    windingMean (2*m) (negativeCentralIndex m)= -(Real.pi/(2*m+1:ℕ)) := by
  simp only [windingMean,negativeCentralIndex,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  ring

theorem positiveCentral_windingMean (m : ℕ) :
    windingMean (2*m) (positiveCentralIndex m)=Real.pi/(2*m+1:ℕ) := by
  simp only [windingMean,positiveCentralIndex,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  ring

theorem centeredKernelIntegral_neg (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (m : ℕ) (d s : ℝ) :
    centeredKernelIntegral B rootB phi hphi m (-d) s=centeredKernelIntegral B rootB phi hphi m d s := by
  funext t
  simpa only [centeredKernelIntegral,centeredInnerSet,neg_sq,Complex.ofReal_neg,shapeExtend_complexify] using
    opposite_winding_kernel_integral (2*m) B rootB phi hphi (d:ℂ) t (s-(2*m+1:ℕ)*d^2)

def noncentralWindingIndices (m : ℕ) : Finset (Fin (2*m+2)) :=
  (Finset.univ.erase (negativeCentralIndex m)).erase (positiveCentralIndex m)

/-- The two actual central physical sectors have identical full kernel jets.
This reflection precedes residue extraction, so no independent pole witnesses are identified. -/
theorem winding_kernel_sum_two_centers (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (m j : ℕ) (s : ℝ) :
    (∑k : Fin (2*m+2),iteratedDeriv j
      (centeredKernelIntegral B rootB phi hphi m (windingMean (2*m) k) s) 0/(j.factorial:ℂ))=
    2*(iteratedDeriv j (centeredKernelIntegral B rootB phi hphi m (Real.pi/(2*m+1:ℕ)) s) 0/(j.factorial:ℂ))+
    ∑k∈noncentralWindingIndices m,iteratedDeriv j
      (centeredKernelIntegral B rootB phi hphi m (windingMean (2*m) k) s) 0/(j.factorial:ℂ) := by
  let f : Fin (2*m+2)→ℂ := fun k=>iteratedDeriv j
    (centeredKernelIntegral B rootB phi hphi m (windingMean (2*m) k) s) 0/(j.factorial:ℂ)
  have h1 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (negativeCentralIndex m))
  have h2 := Finset.sum_erase_add (Finset.univ.erase (negativeCentralIndex m)) f
    (Finset.mem_erase.mpr ⟨(negativeCentralIndex_ne_positive m).symm,Finset.mem_univ _⟩)
  have hm : f (negativeCentralIndex m)=f (positiveCentralIndex m) := by
    dsimp only [f]
    rw [negativeCentral_windingMean,positiveCentral_windingMean,centeredKernelIntegral_neg]
  change (∑k,f k)=2*(_)+_
  rw [←h1,←h2,hm]
  dsimp only [f,noncentralWindingIndices]
  rw [positiveCentral_windingMean]
  ring

end IsingBulk.Anisotropic.NegativeCycles
