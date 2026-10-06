import IsingBulk.Tail.ExteriorConvergenceBounds
import IsingBulk.Tail.UltraHighPairs
import IsingBulk.Tail.UltraHighMatchings
import IsingBulk.Tail.ExteriorPairBridge
import IsingBulk.First.ResidueIntegral

/-! Direct estimates for the actual residue-reduced normalized observable.
The upper-sheet pair contraction is combined with only one Pfaffian expansion. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem subdisk_pairKernel_bound {a b : ℂ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) :
    ‖pairKernel a b‖ ≤ (2*r)/(1-r^2) := by
  have hg : 0 < 1-r^2 := by nlinarith
  have hprod : ‖a*b‖ ≤ r^2 := by rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b]
  have hd := norm_sub_norm_le (1:ℂ) (a*b)
  simp only [norm_one] at hd
  have hden : 1-r^2 ≤ ‖1-a*b‖ := by linarith
  have hn : ‖a-b‖ ≤ 2*r := (norm_sub_le _ _).trans (by linarith)
  rw [pairKernel, norm_div]
  exact div_le_div₀ (by positivity) hn hg hden

theorem subdisk_residueFactor_bound {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hz : ‖z‖ ≤ r) : ‖residueFactor z‖ ≤ 2*r^2/(1-r^2) := by
  have hg : 0 < 1-r^2 := by nlinarith
  have hzp : ‖z‖^2 ≤ r^2 := pow_le_pow_left₀ (norm_nonneg _) hz _
  have hd := norm_sub_norm_le (1:ℂ) (z^2)
  simp only [norm_one, norm_pow] at hd
  have hden : 1-r^2 ≤ ‖1-z^2‖ := by linarith
  simp only [residueFactor, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
  exact div_le_div₀ (by positivity) (by nlinarith) hg hden

/-- A single actual y Pfaffian needs only the explicit matching expansion. -/
theorem circle_pairProduct_matching_bound (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (y : Fin (2*n) → ℂ) (hy : ∀ i, ‖y i‖=r) :
    ‖First.pairProduct y‖ ≤ (matchingCount n:ℝ)*(2*r/(1-r^2))^n := by
  have hg : 0 < 1-r^2 := by nlinarith
  rw [pairProduct_eq_schur]
  have he := Schur.schur_compact_exterior n y hr1 (fun i => (hy i).le)
  change Schur.pfaffian pairKernel n (List.ofFn y) =
    Schur.pairProduct pairKernel (List.ofFn y) at he
  rw [← he]
  apply pfaffian_norm_le_matchings pairKernel n (List.ofFn y) (by simp) (by positivity)
  intro a ha b hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  exact subdisk_pairKernel_bound hr hr1 (hy i).le (hy j).le

/-- Literal reduced-density estimate with explicit global and one-body losses.
Only the y-pair bound remains as a scalar argument to this algebraic lemma. -/
theorem reducedDensity_upper_bound {N : ℕ} (hN : 2 ≤ N) {r A P : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (z y : Fin N → ℂ) (hz : ∀ i, ‖z i‖ ≤ r) (hy : ∀ i, ‖y i‖=r)
    (hzi : ∀ i, ‖(z i)⁻¹‖ ≤ A)
    (hpairz : ‖First.pairProduct z‖ ≤ 1) (hpairy : ‖First.pairProduct y‖ ≤ P) :
    ‖reducedDensity z y‖ ≤
      (2*(max A r⁻¹)^N/(1-r^2)^2)*P*(2*r^2/(1-r^2))^N := by
  have hg : 0 < 1-r^2 := by nlinarith
  have hnum := inverse_global_numerator_norm_le hA (inv_nonneg.mpr hr.le) hzi
    (fun i => show ‖(y i)⁻¹‖ ≤ r⁻¹ by rw [norm_inv, hy i])
  have hdz := coordinateProduct_gap hN hr.le hr1 hz
  have hdy := coordinateProduct_gap hN hr.le hr1 (fun i => (hy i).le)
  have hden : (1-r^2)^2 ≤ ‖(1-coordinateProduct z)*(1-coordinateProduct y)‖ := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hdz hdy hg.le (norm_nonneg _)
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct z)*(1-coordinateProduct y))‖ ≤ 2*(max A r⁻¹)^N/(1-r^2)^2 := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hg) hden
  have hres : ‖∏ i, residueFactor (z i)‖ ≤ (2*r^2/(1-r^2))^N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, (2*r^2/(1-r^2)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => subdisk_residueFactor_bound hr.le hr1 (hz i))
      _ = _ := by simp [div_pow]
  simp only [reducedDensity, norm_mul]
  calc
    _ ≤ (2*(max A r⁻¹)^N/(1-r^2)^2)*1*P*(2*r^2/(1-r^2))^N := by
      gcongr
    _ = _ := by ring

/-- The actual normalized residue integral, with one matching count and all
N-dependent global factors retained. -/
theorem even_doubleFormFactor_matching_bound (n : ℕ) (hn : 0 < n)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im)
    (hi : ∀ y : ℂ, ‖y‖=r → ‖(globalRoot s y)⁻¹‖ ≤ A) :
    ‖doubleFormFactor (2*n) r s‖ ≤ ((2*n).factorial:ℝ)⁻¹ *
      (r^(2*n)*((2*(max A r⁻¹)^(2*n)/(1-r^2)^2)*
        ((matchingCount n:ℝ)*(2*r/(1-r^2))^n)*(2*r^2/(1-r^2))^(2*n))) := by
  have hg : 0 < 1-r^2 := by nlinarith
  have ha := globalRoot_admissible hr hr1 hm
  rw [residue_reduction (2*n) (by omega) r hr s (globalRoot s)
    (fun y hy => ha.toTuple (2*n) y hy)]
  have hb := multiCircleIntegral_norm_le (2*n) hr.le
    (fun y => reducedDensity (fun i => globalRoot s (y i)) y) (by
      intro y hy
      exact reducedDensity_upper_bound (by omega) hr hr1 hA (by positivity)
        _ y (fun i => (globalRoot_inside_radius hr hr1 hm (hy i)).le) hy
        (fun i => hi (y i) (hy i)) (original_root_pairProduct_norm hr hr1 hm y hy)
        (circle_pairProduct_matching_bound n hr.le hr1 y hy))
  simpa only [reducedFormFactor, norm_mul, norm_inv, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Nat.cast_nonneg (2*n).factorial))

/-- Exact factorial normalization turns the one-Pfaffian expansion into an
exponential-series majorant. -/
theorem matching_majorant_identity (n : ℕ) (r H D E g : ℝ) :
    ((2*n).factorial:ℝ)⁻¹ *
      (r^(2*n)*((2*H^(2*n)/g^2)*((matchingCount n:ℝ)*D^n)*E^(2*n))) =
      (2/g^2)*(((r*H*E)^2*D/2)^n/(n.factorial:ℝ)) := by
  have hf : (matchingCount n:ℝ)*((2:ℝ)^n*(n.factorial:ℝ)) = ((2*n).factorial:ℝ) := by
    exact_mod_cast matchingCount_factorial n
  have hm0 : (matchingCount n:ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hf
    exact (by positivity : (0:ℝ) < (2*n).factorial).ne' hf.symm
  rw [← hf]
  by_cases hg : g = 0
  · simp [hg]
  · simp only [pow_mul, mul_pow, div_pow]
    field_simp

theorem even_doubleFormFactor_exponential_bound (n : ℕ) (hn : 0 < n)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im)
    (hi : ∀ y : ℂ, ‖y‖=r → ‖(globalRoot s y)⁻¹‖ ≤ A) :
    ‖doubleFormFactor (2*n) r s‖ ≤ (2/(1-r^2)^2)*
      (((r*(max A r⁻¹)*(2*r^2/(1-r^2)))^2*(2*r/(1-r^2))/2)^n/(n.factorial:ℝ)) := by
  have hb := even_doubleFormFactor_matching_bound n hn hr hr1 hA hm hi
  rw [matching_majorant_identity] at hb
  exact hb

end
end IsingBulk.Tail
