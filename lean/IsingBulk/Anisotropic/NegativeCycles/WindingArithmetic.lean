import IsingBulk.Anisotropic.NegativeCycles.PhysicalCentralSectors

namespace IsingBulk.Anisotropic.NegativeCycles
open scoped BigOperators

theorem windingMean_abs_formula (m : ℕ) (k : Fin (2*m+2)) :
    |windingMean (2*m) k|=|2*(k.val:ℝ)-(2*m+1:ℕ)| *Real.pi/(2*m+1:ℕ) := by
  simp only [windingMean,abs_div,abs_mul,abs_of_pos Real.pi_pos,
    abs_of_pos (show (0:ℝ)<(2*m+1:ℕ) by positivity)]

theorem windingMean_abs_le_pi (m : ℕ) (k : Fin (2*m+2)) :
    |windingMean (2*m) k|≤Real.pi := by
  rw [windingMean_abs_formula,div_le_iff₀ (show (0:ℝ)<(2*m+1:ℕ) by positivity)]
  have hk : (k.val:ℝ)≤(2*m+1:ℕ) := by exact_mod_cast (by omega : k.val≤2*m+1)
  have hk0 : (0:ℝ)≤k.val := Nat.cast_nonneg _
  have hh : |2*(k.val:ℝ)-(2*m+1:ℕ)|≤(2*m+1:ℕ) := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [Real.pi_pos]

theorem windingMean_abs_lower (m : ℕ) (k : Fin (2*m+2)) :
    Real.pi/(2*m+1:ℕ)≤|windingMean (2*m) k| := by
  have hh : (1:ℝ)≤|2*(k.val:ℝ)-(2*m+1:ℕ)| := by
    by_cases hk : k.val≤m
    · have he : 2*(k.val:ℝ)+1≤(2*m+1:ℕ) := by exact_mod_cast (by omega : 2*k.val+1≤2*m+1)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have he : (2*m+1:ℕ)+1≤2*(k.val:ℝ) := by exact_mod_cast (by omega : 2*m+1+1≤2*k.val)
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [windingMean_abs_formula]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith [Real.pi_pos]

theorem noncentral_windingMean_abs_lower (m : ℕ) (k : Fin (2*m+2))
    (hk : k∈noncentralWindingIndices m) :
    3*Real.pi/(2*m+1:ℕ)≤|windingMean (2*m) k| := by
  have hkp := (Finset.mem_erase.mp hk).1
  have hkm := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkvp : k.val≠m+1 := by
    intro he
    apply hkp
    apply Fin.ext
    exact he
  have hkvm : k.val≠m := by
    intro he
    apply hkm
    apply Fin.ext
    exact he
  have hh : (3:ℝ)≤|2*(k.val:ℝ)-(2*m+1:ℕ)| := by
    by_cases hle : k.val≤m
    · have he : 2*(k.val:ℝ)+3≤(2*m+1:ℕ) := by exact_mod_cast (by omega : 2*k.val+3≤2*m+1)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have he : (2*m+1:ℕ)+3≤2*(k.val:ℝ) := by exact_mod_cast (by omega : 2*m+1+3≤2*k.val)
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [windingMean_abs_formula]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh Real.pi_pos.le) (Nat.cast_nonneg _)


theorem active_windingMean_lt (m : ℕ) (k : Fin (2*m+2)) {s R : ℝ}
    (hR : 0<R) (hs : s≤R^2) (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) :
    |windingMean (2*m) k|<R := by
  have hN : (1:ℝ)≤(2*m+1:ℕ) := by exact_mod_cast (by omega : 1≤2*m+1)
  have hq := sq_nonneg (windingMean (2*m) k)
  rw [abs_lt]
  constructor <;> nlinarith

end IsingBulk.Anisotropic.NegativeCycles
