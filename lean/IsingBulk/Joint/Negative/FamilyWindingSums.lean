import IsingBulk.Joint.Negative.FamilyWindingBounds
import IsingBulk.Anisotropic.NegativeCycles.ActualWindingPoleSums
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open IsingBulk.Anisotropic.NegativeCycles
namespace IsingBulk.Joint.Negative
open Set Filter MeasureTheory IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
/-- All noncentral physical winding sectors, including their actual activity
conditions and exact P witnesses, have the required middle-range error. -/
theorem compact_family_noncentral_winding_sum (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) (hr0 : ∀eta∈Q,rootB (0,eta)≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ : ℝ,0<ρ ∧ ∃N0 : ℕ,∀ᶠj : ℕ in atTop,∀eta∈Q,∀m : ℕ,N0≤2*m → 1≤m →
      ((2*m+1:ℕ):ℝ)^2≤(j:ℝ)/Real.sqrt (Real.log j) →
      ∀s : ℝ,s≤ρ^2 →
      ∀P : (k : Fin (2*m+2))→(2*m+1:ℕ)*(windingMean (2*m) k)^2<s →
        UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (windingMean (2*m) k:ℂ) rP CP,
      (∑k∈noncentralWindingIndices m,‖actualWindingPole (familyMember B eta) (familyMember rootB eta) phi hphi m rP CP s P j k‖)≤
        Real.exp (-(j:ℝ)*Real.log 2/4)*
          ‖model (familyMember B eta (tau (2*m+1))) (familyMember rootB eta (tau (2*m+1)))
            (hessianFactor (familyMember B eta (tau (2*m+1))) (Real.cos phi) (Real.sin phi) (2*m+1))
            (Real.sin phi) (2*m+1) j‖ := by
  obtain ⟨ρ,C,hρ,hC,N0,hsector⟩ := compact_family_witness_higher_winding B rootB phi hphi hQ hB hrB hB0 hr0 rP CP hrP
  refine ⟨ρ,hρ,N0,?_⟩
  filter_upwards [eventually_higher_winding_middle C hC,eventually_finite_higher_winding_middle C hC] with j hj hsum
  intro eta heta m hm0 hm hcut s hs P
  have haj := (hj (2*m+1) hcut).1
  have hcard : (noncentralWindingIndices m).card≤(2*m+1)+1 := by
    simpa only [Fintype.card_fin,Nat.add_assoc] using (noncentralWindingIndices m).card_le_univ
  apply hsum (2*m+1) (by omega) hcut (Fin (2*m+2)) (noncentralWindingIndices m) hcard _ (norm_nonneg _)
  intro k hk
  dsimp only [actualWindingPole]
  split_ifs with ha
  · have hb := hsector eta heta (2*m) hm0 (by omega) ⟨m,by omega⟩ (windingMean (2*m) k)
      (active_windingMean_lt m k hρ hs ha) (windingMean_abs_le_pi m k)
      (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using noncentral_windingMean_abs_lower m k hk)
      (P k ha) s hs j haj
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hb
  · simp only [norm_zero]
    positivity

/-- The complete physical winding pole sum has the high-range entropy bound
at every Taylor order, for precisely the witnesses appearing in the decomposition. -/
theorem compact_family_all_winding_high_sum (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ C : ℝ,0<ρ ∧ 0<C ∧ ∀eta∈Q,∀m : ℕ,1≤m →
      ∀s : ℝ,s≤ρ^2 →
      ∀P : (k : Fin (2*m+2))→(2*m+1:ℕ)*(windingMean (2*m) k)^2<s →
        UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (windingMean (2*m) k:ℂ) rP CP,
      ∀j : ℕ,(∑k,‖actualWindingPole (familyMember B eta) (familyMember rootB eta) phi hphi m rP CP s P j k‖)≤
        Real.exp (2*j*Real.log (2*m+1:ℕ)-((2*m+1:ℕ):ℝ)^2/2*Real.log (2*m+1:ℕ)+C*((2*m+1:ℕ):ℝ)^2) := by
  obtain ⟨ρ,C,hρ,_hρ1,hC,hsector⟩ := compact_family_witness_high_entropy B rootB phi hphi hQ hB hrB hB0 rP CP hrP
  refine ⟨ρ,C+1,hρ,by linarith,?_⟩
  intro eta heta m hm s hs P j
  apply finite_winding_entropy (Finset.univ : Finset (Fin (2*m+2))) (2*m+1) j (by omega)
    (by simp only [Finset.card_univ,Fintype.card_fin]; omega) C
  intro k _
  dsimp only [actualWindingPole]
  split_ifs with ha
  · have hb := hsector eta heta (2*m) (by omega) (windingMean (2*m) k)
      (active_windingMean_lt m k hρ hs ha) (windingMean_abs_lower m k) (P k ha) s hs j
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hb
  · simp only [norm_zero]
    exact (Real.exp_pos _).le

end IsingBulk.Joint.Negative
