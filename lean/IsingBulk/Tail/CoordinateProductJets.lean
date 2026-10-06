import IsingBulk.Analysis.JetsTermPullback
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Exact real-coordinate Leibniz words on an open regular chart. Splits are
constructed with multiplicity; no analytic-cutoff assumption is used. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set Filter
open scoped ContDiff Topology

variable {N : ℕ}

def cutoffWordSplits : List (Fin N) → List (List (Fin N) × List (Fin N))
  | [] => [([],[])]
  | i::l => (cutoffWordSplits l).flatMap (fun p => [(i::p.1,p.2),(p.1,i::p.2)])

theorem cutoffWordSplits_length (l : List (Fin N)) :
    (cutoffWordSplits l).length=2^l.length := by
  induction l with
  | nil => simp [cutoffWordSplits]
  | cons i l ih =>
    simp [cutoffWordSplits,List.length_flatMap,ih,pow_succ,mul_comm]

theorem cutoffWordSplits_orders (l : List (Fin N))
    (p : List (Fin N) × List (Fin N)) (hp : p ∈ cutoffWordSplits l) :
    p.1.length+p.2.length=l.length := by
  induction l generalizing p with
  | nil =>
    have he : p=([],[]) := by simpa only [cutoffWordSplits,List.mem_singleton] using hp
    simp [he]
  | cons i l ih =>
    obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
    have hlen := ih q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> simp only [List.length_cons] <;> omega

theorem coordinate_cutoffJet_contDiffAt (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (cutoffJet l f) x := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem coordinate_deriv_product (f g : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (q : Fin N) :
    fderiv ℝ (fun y => f y*g y) x (Pi.single q 1) =
      fderiv ℝ f x (Pi.single q 1)*g x + f x*fderiv ℝ g x (Pi.single q 1) := by
  change fderiv ℝ (f*g) x (Pi.single q 1)=_
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem coordinate_deriv_list_sum {ι : Type*} (L : List ι)
    (F : ι → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    (hF : ∀ i ∈ L, DifferentiableAt ℝ (F i) x) (q : Fin N) :
    DifferentiableAt ℝ (fun y => (L.map (fun i => F i y)).sum) x ∧
    fderiv ℝ (fun y => (L.map (fun i => F i y)).sum) x (Pi.single q 1) =
      (L.map (fun i => fderiv ℝ (F i) x (Pi.single q 1))).sum := by
  induction L with
  | nil => simp [differentiableAt_const]
  | cons a L ih =>
    obtain ⟨hL,he⟩ := ih (fun i hi => hF i (by simp [hi]))
    have ha := hF a (by simp)
    simp only [List.map_cons,List.sum_cons]
    refine ⟨ha.fun_add hL,?_⟩
    change fderiv ℝ (F a+(fun y => (L.map (fun i => F i y)).sum)) x (Pi.single q 1)=_
    rw [(ha.hasFDerivAt.add hL.hasFDerivAt).fderiv,add_apply,he]

theorem list_split_sum {ι : Type*} (L : List ι) (f g : ι → ℝ) :
    (L.map (fun i => f i+g i)).sum=(L.flatMap (fun i => [f i,g i])).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.sum_append,ih,List.sum_nil]; ring

theorem cutoffJet_product_word (l : List (Fin N)) (f g : (Fin N → ℝ) → ℝ)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) :
    ∀ x ∈ U, cutoffJet l (fun y => f y*g y) x =
      ((cutoffWordSplits l).map (fun p => cutoffJet p.1 f x*cutoffJet p.2 g x)).sum := by
  induction l with
  | nil => intro x hx; simp [cutoffWordSplits,cutoffJet]
  | cons i l ih =>
    intro x hx
    have he : cutoffJet l (fun y => f y*g y) =ᶠ[𝓝 x]
        (fun y => ((cutoffWordSplits l).map (fun p => cutoffJet p.1 f y*cutoffJet p.2 g y)).sum) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).mono (fun y hy => ih y hy)
    change fderiv ℝ (cutoffJet l (fun y => f y*g y)) x (Pi.single i 1)=_
    rw [he.fderiv_eq]
    have hfd (p : List (Fin N) × List (Fin N)) : DifferentiableAt ℝ (cutoffJet p.1 f) x :=
      (coordinate_cutoffJet_contDiffAt p.1 f x (hf x hx)).differentiableAt (by simp)
    have hgd (p : List (Fin N) × List (Fin N)) : DifferentiableAt ℝ (cutoffJet p.2 g) x :=
      (coordinate_cutoffJet_contDiffAt p.2 g x (hg x hx)).differentiableAt (by simp)
    rw [(coordinate_deriv_list_sum (cutoffWordSplits l)
      (fun p y => cutoffJet p.1 f y*cutoffJet p.2 g y) x
      (fun p _ => (hfd p).fun_mul (hgd p)) i).2]
    simp_rw [coordinate_deriv_product _ _ x (hfd _) (hgd _)]
    rw [list_split_sum]
    simp only [cutoffWordSplits,List.map_flatMap,List.map_cons,List.map_nil,cutoffJet]


theorem cutoffJet_append_word (l k : List (Fin N)) (f : (Fin N → ℝ) → ℝ) :
    cutoffJet (l++k) f=cutoffJet l (cutoffJet k f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append,cutoffJet,ih]

theorem cutoffJet_finset_sum {ι : Type*} (s : Finset ι) (l : List (Fin N))
    (F : ι → (Fin N → ℝ) → ℝ) {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hF : ∀ i ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ (F i) x) :
    ∀ x ∈ U, cutoffJet l (fun y => ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, cutoffJet l (F i) x := by
  induction l with
  | nil => intro x hx; rfl
  | cons q l ih =>
    intro x hx
    have he : cutoffJet l (fun y => ∑ i ∈ s, F i y) =ᶠ[𝓝 x]
        (fun y => ∑ i ∈ s, cutoffJet l (F i) y) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).mono (fun y hy => ih y hy)
    have hd (i : ι) (hi : i ∈ s) : DifferentiableAt ℝ (cutoffJet l (F i)) x :=
      (coordinate_cutoffJet_contDiffAt l (F i) x (hF i hi x hx)).differentiableAt (by simp)
    change fderiv ℝ (cutoffJet l (fun y => ∑ i ∈ s, F i y)) x (Pi.single q 1)=_
    rw [he.fderiv_eq,(HasFDerivAt.fun_sum (fun i hi => (hd i hi).hasFDerivAt)).fderiv]
    simp only [sum_apply,cutoffJet]


end
end IsingBulk.Tail
