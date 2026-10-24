import IsingBulk.Anisotropic.NegativeNormalForm.CorrectedPairUniform
import IsingBulk.Anisotropic.NegativeNormalForm.FullDensityDomain

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem sum_norm_le_sqrt_energy {n : ℕ} (v : Config n) :
    (∑ i, ‖v i‖)≤Real.sqrt ((n:ℝ)*absoluteEnergy v) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin n => (1:ℝ)) (fun i => ‖v i‖)
  simpa [absoluteEnergy,Real.sqrt_mul (Nat.cast_nonneg n)] using h

 theorem sum_all_pair_energy {n : ℕ} (hn : n≠0) (f : Fin n → ℝ) (e d q : ℝ) :
    (∑ p : Fin n × Fin n, (e+d*(f p.1+f p.2)+(f p.1)^2+(f p.2)^2+q/(n:ℝ)))=
      (n:ℝ)^2*e+2*(n:ℝ)*d*(∑ i,f i)+2*(n:ℝ)*(∑ i,(f i)^2)+(n:ℝ)*q := by
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  simp [Fintype.sum_prod_type,Finset.sum_add_distrib,mul_add,Finset.mul_sum]
  simp only [← Finset.mul_sum]
  field_simp
  ring

 theorem pair_error_sum_bound {n : ℕ} (hn : n≠0) (v : Config n)
    (F : Fin n → Fin n → ℂ) (K e d : ℝ) (hK : 0≤K) (hd : 0≤d)
    (hF : ∀ i j, ‖F i j-1‖≤K*(e+d*(‖v i‖+‖v j‖)+‖v i‖^2+‖v j‖^2+absoluteEnergy v/(n:ℝ))) :
    (∑ p∈firstStrictPairs n, ‖F p.1 p.2-1‖)≤
      K*((n:ℝ)^2*e+2*(n:ℝ)*d*Real.sqrt ((n:ℝ)*absoluteEnergy v)+3*(n:ℝ)*absoluteEnergy v) := by
  calc
    _ ≤ ∑ p : Fin n × Fin n, ‖F p.1 p.2-1‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ p : Fin n × Fin n, K*(e+d*(‖v p.1‖+‖v p.2‖)+‖v p.1‖^2+‖v p.2‖^2+absoluteEnergy v/(n:ℝ)) :=
      Finset.sum_le_sum (fun p _ => hF p.1 p.2)
    _ = K*((n:ℝ)^2*e+2*(n:ℝ)*d*(∑ i,‖v i‖)+3*(n:ℝ)*absoluteEnergy v) := by
      rw [← Finset.mul_sum,sum_all_pair_energy hn (fun i => ‖v i‖) e d (absoluteEnergy v)]
      unfold absoluteEnergy
      ring
    _ ≤ _ := by gcongr; exact sum_norm_le_sqrt_energy v

 theorem correctedSeparablePairFactor_sum_uniform (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ n : ℕ, n≠0 → ∀ t d : ℂ, ∀ v : Config n,
      ‖t‖<r → ‖d‖<r → ‖v‖<r → ZeroMean v →
      (∑ p∈firstStrictPairs n, ‖correctedSeparablePairFactor B phi hphi t d v p.1 p.2-1‖)≤
        C*((n:ℝ)^2*‖t-(1-Complex.cos d)‖+
          2*(n:ℝ)*‖d‖*Real.sqrt ((n:ℝ)*absoluteEnergy v)+3*(n:ℝ)*absoluteEnergy v) := by
  obtain ⟨r,C,hr,hC,hpair⟩ := correctedSeparablePairFactor_uniform B phi hphi hB hBn
  refine ⟨r,C,hr,hC,?_⟩
  intro n hn t d v ht hd hv hzero
  exact pair_error_sum_bound hn v _ C _ ‖d‖ hC.le (norm_nonneg d) (hpair n hn t d v ht hd hv hzero)

 theorem pair_error_sum_bound_off_diagonal {n : ℕ} (hn : n≠0) (v : Config n)
    (F : Fin n → Fin n → ℂ) (K Cp d : ℝ) (hK : 0≤K) (hCp : 0≤Cp) (hd : 0≤d)
    (hF : ∀ i j, i≠j → ‖F i j-1‖≤K*((Cp+1)*absoluteEnergy v/(n:ℝ)+
      d*(‖v i‖+‖v j‖)+‖v i‖^2+‖v j‖^2)) :
    (∑ p∈firstStrictPairs n, ‖F p.1 p.2-1‖)≤
      K*((Cp+3)*(n:ℝ)*absoluteEnergy v+2*(n:ℝ)*d*Real.sqrt ((n:ℝ)*absoluteEnergy v)) := by
  let G : Fin n → Fin n → ℂ := fun i j => if i=j then 1 else F i j
  have hq := absoluteEnergy_nonneg v
  have hG (i j : Fin n) : ‖G i j-1‖≤K*(Cp*absoluteEnergy v/(n:ℝ)+
      d*(‖v i‖+‖v j‖)+‖v i‖^2+‖v j‖^2+absoluteEnergy v/(n:ℝ)) := by
    by_cases hij : i=j
    · simp only [G,ite_eq_left hij,sub_self,norm_zero]
      positivity
    · simp only [G,ite_eq_right hij]
      convert hF i j hij using 1; ring
  have h := pair_error_sum_bound hn v G K (Cp*absoluteEnergy v/(n:ℝ)) d hK hd hG
  have he : (∑ p∈firstStrictPairs n, ‖G p.1 p.2-1‖)=∑ p∈firstStrictPairs n, ‖F p.1 p.2-1‖ := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [G,ite_eq_right (ne_of_lt (mem_firstStrictPairs p |>.mp hp))]
  rw [he] at h
  convert h using 1
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  field_simp
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
