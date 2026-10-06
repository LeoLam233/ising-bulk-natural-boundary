import IsingBulk.Tail.MicrocoreJetTerms
import IsingBulk.Analysis.JetsBoundCalculus

/-! Combinatorial and finite regular-jet cost of the actual microcore
recurrence. Counts are derived from its generated action list. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

theorem microcoreJetTerms_length {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ) (j : ℕ) :
    (microcoreJetTerms F j).length=(N+1)^j := by
  induction j with
  | zero => simp [microcoreJetTerms]
  | succ j ih => simp [microcoreJetTerms,List.length_flatMap,microActions,ih,pow_succ]

theorem microcoreJetTerms_cutoff_length {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ) (j : ℕ) :
    ∀ T ∈ microcoreJetTerms F j, T.cutoff.length ≤ j := by
  induction j with
  | zero =>
    intro T hT
    have he : T=⟨[],F⟩ := by simpa only [microcoreJetTerms,List.mem_singleton] using hT
    subst T
    simp
  | succ j ih =>
    intro T hT
    obtain ⟨P,hP,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    have hh := ih P hP
    cases a <;> simp only [MicrocoreJetTerm.child,List.length_cons] <;> omega

theorem microcoreJetTerms_jet_budget {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) (J j : ℕ) (hj : j ≤ J) (C D : ℝ) (hC : 1 ≤ C)
    (hF : JetBound F z J D)
    (hA : ∀ i, JetBound (fun t : ℂ × (Fin N → ℂ) => regularA t.1 (t.2 i)) z J C) :
    ∀ T ∈ microcoreJetTerms F j,
      JetBound T.regularPart z (J-j) ((2^J*C)^j*D) := by
  induction j with
  | zero =>
    intro T hT
    have he : T=⟨[],F⟩ := by simpa only [microcoreJetTerms,List.mem_singleton] using hT
    subst T
    simpa using hF
  | succ j ih =>
    intro T hT
    obtain ⟨P,hP,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    have hPjet := ih (by omega) P hP
    have hC0 : 0 ≤ C := by linarith
    have hB : 1 ≤ (2:ℝ)^J*C := by
      have hp : 1 ≤ (2:ℝ)^J := one_le_pow₀ (by norm_num)
      nlinarith
    cases a with
    | none =>
      have he : J-j=(J-(j+1))+1 := by omega
      rw [he] at hPjet
      have hd := hPjet.direction (1,0) (by simp)
      apply hd.mono le_rfl
      rw [pow_succ]
      have hD0 : 0 ≤ (2^J*C)^j*D := hPjet.nonneg
      nlinarith
    | some i =>
      have ha := ((hA i).mono (show J-(j+1) ≤ J by omega) le_rfl).neg
      have hp := hPjet.mono (show J-(j+1) ≤ J-j by omega) le_rfl
      have hh := ha.mul hp
      apply hh.mono le_rfl
      have he : (2:ℝ)^(J-(j+1)) ≤ 2^J := pow_le_pow_right₀ (by norm_num) (by omega)
      have hD0 := hp.nonneg
      calc
        _ ≤ 2^J*C*((2^J*C)^j*D) := by gcongr
        _ = _ := by rw [pow_succ]; ring

end
end IsingBulk.Tail
