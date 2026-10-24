import IsingBulk.Anisotropic.NegativeCycles.WindingAngles

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators

theorem negativeShiftedAngles_winding_sum (n : ℕ) (v : Fin n→ℝ) :
    ∃k : ℤ, (∑i, negativeShiftedAngles n v i)=(2*(k:ℝ)-(n+1:ℕ))*Real.pi := by
  have hi (i : Fin (n+1)) : ∃k : ℤ,
      negativeShiftedAngles n v i-
        (physicalDependentAngles n (fun j => v j+Real.pi) i-Real.pi)=2*Real.pi*k := by
    apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
    simp [negativeShiftedAngles,wrapAngle,Real.Angle.coe_toReal]
  choose k hk using hi
  refine ⟨∑i,k i,?_⟩
  have hs := congrArg (fun q : Fin (n+1)→ℝ => ∑i,q i) (funext hk)
  have hp : (∑i,physicalDependentAngles n (fun j => v j+Real.pi) i)=0 := by
    rw [Fin.sum_univ_castSucc]
    simp [physicalDependentAngles]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,←Finset.mul_sum] at hs
  rw [hp] at hs
  push_cast at hs ⊢
  nlinarith

/-- Subtracting the actual winding mean, rather than an artificial zero center,
gives the precise transverse radius identity. -/
theorem winding_mean_radius {N : ℕ} (hN : N≠0) (δ : Fin N→ℝ) (k : ℤ)
    (hk : (∑i,δ i)=(2*(k:ℝ)-(N:ℝ))*Real.pi) :
    let d := (2*(k:ℝ)-(N:ℝ))*Real.pi/(N:ℝ)
    (∑i,(δ i-d))=0 ∧ (∑i,(δ i)^2)=(N:ℝ)*d^2+∑i,(δ i-d)^2 := by
  dsimp only
  let d := (2*(k:ℝ)-(N:ℝ))*Real.pi/(N:ℝ)
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN
  have hd : (∑i,δ i)=(N:ℝ)*d := by dsimp [d]; rw [hk]; field_simp
  change (∑i,(δ i-d))=0 ∧ _
  constructor
  · rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hd]
    ring
  · change (∑i,δ i^2)=(N:ℝ)*d^2+∑i,(δ i-d)^2
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simp_rw [←Finset.sum_mul,←Finset.mul_sum]
    rw [hd]
    ring


/-- The actual wrapped constrained family has only finitely many winding sectors. -/
theorem negativeShiftedAngles_finite_winding (n : ℕ) (v : Fin n→ℝ) :
    ∃k : ℤ, 0≤k ∧ k≤(n+1:ℕ) ∧
      (∑i, negativeShiftedAngles n v i)=(2*(k:ℝ)-(n+1:ℕ))*Real.pi := by
  obtain ⟨k,hk⟩ := negativeShiftedAngles_winding_sum n v
  have hlo : -(n+1:ℕ)*Real.pi≤∑i,negativeShiftedAngles n v i := by
    have h := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (n+1)))) =>
      (wrapAngle_mem (physicalDependentAngles n (fun j => v j+Real.pi) i-Real.pi)).1)
    convert h using 1 <;> simp [negativeShiftedAngles]
    all_goals ring
  have hhi : (∑i,negativeShiftedAngles n v i)≤(n+1:ℕ)*Real.pi := by
    have h := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (n+1)))) =>
      (wrapAngle_mem (physicalDependentAngles n (fun j => v j+Real.pi) i-Real.pi)).2)
    simpa [negativeShiftedAngles] using h
  rw [hk] at hlo hhi
  have hk0 : (0:ℝ)≤k := by nlinarith [Real.pi_pos]
  have hkn : (k:ℝ)≤(n+1:ℕ) := by nlinarith [Real.pi_pos]
  exact ⟨k,by exact_mod_cast hk0,by exact_mod_cast hkn,hk⟩

/-- Apart from the two minimal sectors, every odd winding has squared size at least nine. -/
theorem odd_winding_gap (m : ℕ) (k : ℤ) :
    k=(m+1:ℕ) ∨ k=(m:ℤ) ∨ 9≤(2*(k:ℝ)-(2*m+1:ℕ))^2 := by
  by_cases hp : k=(m+1:ℕ)
  · exact Or.inl hp
  by_cases hm : k=(m:ℤ)
  · exact Or.inr (Or.inl hm)
  right; right
  have hgap : 2*k-(2*(m:ℤ)+1)≤ -3 ∨ 3≤2*k-(2*(m:ℤ)+1) := by
    push_cast at hp
    omega
  rcases hgap with h|h
  · have hh : 2*(k:ℝ)-(2*(m:ℝ)+1)≤ -3 := by exact_mod_cast h
    push_cast
    nlinarith
  · have hh : 3≤2*(k:ℝ)-(2*(m:ℝ)+1) := by exact_mod_cast h
    push_cast
    nlinarith

end IsingBulk.Anisotropic.NegativeCycles
