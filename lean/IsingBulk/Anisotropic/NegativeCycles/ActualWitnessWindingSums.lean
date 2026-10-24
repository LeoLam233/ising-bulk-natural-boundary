import IsingBulk.Anisotropic.NegativeCycles.ActualWitnessWindingBounds
import IsingBulk.Anisotropic.NegativeDominance.HigherWindingSum
import IsingBulk.Anisotropic.NegativeDominance.HighWindingSum

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open Set MeasureTheory Filter
open scoped Topology BigOperators

theorem activeWinding_card_le (n : ℕ) (A : Finset (Fin (n+2))) :
    (Finset.univ : Finset A).card≤(n+1)+1 := by
  have h := Fintype.card_le_of_injective (fun k : A=>(k:Fin (n+2))) Subtype.val_injective
  simpa only [Finset.card_univ,Fintype.card_fin,Nat.add_assoc] using h

/-- Every active noncentral sector is estimated with its original P.T. Summing
all sectors preserves the exponential middle-range loss and exact model scale. -/
theorem actualWitness_higher_winding_middle_sum (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) (hr0 : rootB 0≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ : ℝ,0<ρ ∧ ∃N0 : ℕ,∀ᶠj : ℕ in atTop,∀n : ℕ,N0≤n → 2≤n → Odd (n+1) →
      (n+1:ℝ)^2≤(j:ℝ)/Real.sqrt (Real.log j) →
      ∀A : Finset (Fin (n+2)), ∀d : A→ℝ,
      (∀k,|d k|<ρ ∧ |d k|≤Real.pi ∧ 3*Real.pi/(n+1)≤|d k|) →
      ∀P : (k : A)→UniformProjectedWitness B phi hphi (n+1) (d k:ℂ) rP CP,
      ∀s : ℝ,s≤ρ^2 →
        (∑k : A,‖∫q in centeredInnerSet n (d k) s,
          constrainedResidueDensity B rootB phi hphi (d k:ℂ) (P k).T j (complexify n q)‖)≤
          Real.exp (-(j:ℝ)*Real.log 2/4)*
            ‖model (B (tau (n+1))) (rootB (tau (n+1)))
              (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1))
              (Real.sin phi) (n+1) j‖ := by
  obtain ⟨ρ,C,hρ,hC,N0,hsector⟩ := actualWitness_higher_winding_bound B rootB phi hphi hB hrB hB0 hr0 rP CP hrP
  refine ⟨ρ,hρ,N0,?_⟩
  filter_upwards [eventually_higher_winding_middle C hC,eventually_finite_higher_winding_middle C hC] with j hj hsum
  intro n hn0 hn ho hcut A d hd P s hs
  have hcut' : ((n+1:ℕ):ℝ)^2≤(j:ℝ)/Real.sqrt (Real.log j) := by simpa using hcut
  have haj := (hj (n+1) hcut').1
  have hh := hsum (n+1) (by omega) hcut' A Finset.univ (activeWinding_card_le n A)
    ‖model (B (tau (n+1))) (rootB (tau (n+1)))
      (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1)) (Real.sin phi) (n+1) j‖
    (norm_nonneg _) (fun k=>∫q in centeredInnerSet n (d k) s,
      constrainedResidueDensity B rootB phi hphi (d k:ℂ) (P k).T j (complexify n q))
    (fun k _=>by
      have hb := hsector n hn0 hn ho (d k) (hd k).1 (hd k).2.1 (hd k).2.2 (P k) s hs j haj
      simpa only [Nat.cast_add,Nat.cast_one] using hb)
  simpa using hh

/-- Complete active winding pole sum at every Taylor order, with the sharp
negative N² log N/2 entropy term and no substituted pole witnesses. -/
theorem actualWitness_all_winding_high_sum (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ C : ℝ,0<ρ ∧ 0<C ∧ ∀n : ℕ,1≤n →
      ∀A : Finset (Fin (n+2)), ∀d : A→ℝ,
      (∀k,|d k|<ρ ∧ Real.pi/((n+1:ℕ):ℝ)≤|d k|) →
      ∀P : (k : A)→UniformProjectedWitness B phi hphi (n+1) (d k:ℂ) rP CP,
      ∀s : ℝ,s≤ρ^2 → ∀j : ℕ,
        (∑k : A,‖∫q in centeredInnerSet n (d k) s,
          constrainedResidueDensity B rootB phi hphi (d k:ℂ) (P k).T j (complexify n q)‖)≤
          Real.exp (2*j*Real.log (n+1)-(n+1:ℝ)^2/2*Real.log (n+1)+C*(n+1:ℝ)^2) := by
  obtain ⟨ρ,C,hρ,_hρ1,hC,hsector⟩ := actualWitness_high_pole_entropy_bound B rootB phi hphi hB hrB hB0 rP CP hrP
  refine ⟨ρ,C+1,hρ,by linarith,?_⟩
  intro n hn A d hd P s hs j
  have hh := finite_winding_entropy (Finset.univ : Finset A) (n+1) j (by omega)
    (activeWinding_card_le n A) C
    (fun k=>∫q in centeredInnerSet n (d k) s,
      constrainedResidueDensity B rootB phi hphi (d k:ℂ) (P k).T j (complexify n q))
    (fun k _=>by
      have hb := hsector n hn (d k) (hd k).1 (hd k).2 (P k) s hs j
      simpa only [Nat.cast_add,Nat.cast_one] using hb)
  simpa only [Nat.cast_add,Nat.cast_one] using hh

end IsingBulk.Anisotropic.NegativeCycles
