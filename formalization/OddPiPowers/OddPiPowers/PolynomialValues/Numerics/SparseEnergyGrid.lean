module

public import OddPiPowers.PolynomialValues.Numerics.SpatialQuadrature

/-! Dense signed residuals consist of band endpoints and jumps on the
coarser density grid. Their forward and reversed polynomials can be
evaluated directly on this sparse support. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def sparse125 {A : Type*} [Zero A] (f : ℕ → A) (i : ℕ) := if i%125=0 then f (i/125) else 0

theorem sum_sparse125 {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    (∑ i ∈ range 80001, sparse125 f i)=∑ j ∈ range 641, f j := by
  rw [← sum_full_stripes,sum_eq_single 0]
  · simp [sparse125,stripeCount]
  · intro r hr h0
    apply sum_eq_zero
    intro k _
    simp [sparse125,(stripe_position (mem_range.mp hr) k).1,h0]
  · simp

theorem sparse125_reflect {i : ℕ} (hi : i<80001) (f : ℕ → ℤ) :
    sparse125 f (80000-i)=sparse125 (fun j => f (640-j)) i := by
  unfold sparse125
  by_cases hm : i%125=0
  · have h : (80000-i)%125=0 := by omega
    simp only [h,hm,if_true,show (80000-i)/125=640-i/125 by omega]
  · have h : (80000-i)%125≠0 := by omega
    simp [h,hm]

theorem sparse125_pack (b : ℤ) (f : ℕ → ℤ) :
    packedSum b 80001 (sparse125 f)=packedSum (b^125) 641 f := by
  let g (j : ℕ) := f j*(b^125)^j
  calc
    _ = ∑ i ∈ range 80001, sparse125 g i := by
      apply sum_congr rfl
      intro i _
      by_cases h : i%125=0
      · simp only [sparse125,h,if_true,g,← pow_mul,show 125*(i/125)=i by omega]
      · simp [sparse125,h]
    _ = _ := sum_sparse125 g

def treeWord (b : ℤ) (f : ℕ → ℤ) (s : ℕ) : ℕ → ℤ
  | 0 => f s
  | d+1 =>
    let m := 2^d
    treeWord b f s d+treeWord b f (s+m) d*b^m

theorem treeWord_eq (b : ℤ) (f : ℕ → ℤ) (s d : ℕ) :
    treeWord b f s d=packedSum b (2^d) (fun j => f (s+j)) := by
  induction d generalizing s with
  | zero => simp [treeWord,packedSum]
  | succ d ih =>
    rw [treeWord,ih,ih,show 2^(d+1)=2^d+2^d by rw [pow_succ]; omega,packedSum_append]
    simp only [Nat.add_assoc]

def coarseWord (b : ℤ) (f : ℕ → ℤ) := treeWord b (fun j => if j<641 then f j else 0) 0 10

theorem coarseWord_eq (b : ℤ) (f : ℕ → ℤ) : coarseWord b f=packedSum b 641 f := by
  rw [coarseWord,treeWord_eq,show 2^10=641+383 by decide,packedSum_append]
  simp only [Nat.zero_add]
  have hz : packedSum b 383 (fun j => if 641+j<641 then f (641+j) else 0)=0 := by
    apply (packedSum_congr (c := fun _ => 0) (fun i _ => if_neg (by omega))).trans
    simp [packedSum]
  rw [hz,zero_mul,add_zero]
  exact packedSum_congr (fun i hi => if_pos hi)

def pointJump (p : ℕ) (v : ℤ) (i : ℕ) := if i=p then v else 0

theorem pointJump_word (b : ℤ) {n p : ℕ} (hp : p<n) (v : ℤ) :
    packedSum b n (pointJump p v)=v*b^p := by
  simp [packedSum,pointJump,ite_mul,Finset.mem_range.mpr hp]

theorem pointJump_norm {n p : ℕ} (hp : p<n) (v : ℤ) :
    (∑ i ∈ range n, |pointJump p v i|)=|v| := by
  simp [pointJump,apply_ite abs,Finset.mem_range.mpr hp]

theorem pointJump_reflect {n p i : ℕ} (hi : i<n) (hp : p<n) (v : ℤ) :
    pointJump p v (n-1-i)=pointJump (n-1-p) v i := by
  unfold pointJump
  split_ifs <;> first | rfl | omega

def bandJumps (ws : List ℕ) (i : ℕ) : ℤ :=
  (ws.map fun w => pointJump (40000-4*w) 100000 i-pointJump (40000+4*w) 100000 i).sum

def bandJumpWord (b : ℤ) (ws : List ℕ) : ℤ :=
  (ws.map fun w => 100000*(b^(40000-4*w)-b^(40000+4*w))).sum

theorem bandJumpWord_eq (b : ℤ) (ws : List ℕ) (h : ∀ w∈ws, w≤10000) :
    bandJumpWord b ws=packedSum b 80001 (bandJumps ws) := by
  induction ws with
  | nil => simp [bandJumpWord,bandJumps,packedSum]
  | cons w ws ih =>
    have hw := h w (by simp)
    change 100000*(b^(40000-4*w)-b^(40000+4*w))+bandJumpWord b ws=_
    rw [ih (fun j hj => h _ (List.mem_cons_of_mem _ hj))]
    change _=packedSum b 80001 (fun i => (pointJump (40000-4*w) 100000 i-pointJump (40000+4*w) 100000 i)+bandJumps ws i)
    rw [packedSum_add,packedSum_sub,pointJump_word b (by omega),pointJump_word b (by omega)]
    ring

theorem bandJumps_reflect (ws : List ℕ) (h : ∀ w∈ws, w≤10000) {i : ℕ} (hi : i<80001) :
    bandJumps ws (80000-i) = -bandJumps ws i := by
  induction ws with
  | nil => simp [bandJumps]
  | cons w ws ih =>
    have hw := h w (by simp)
    change pointJump (40000-4*w) 100000 (80000-i)-pointJump (40000+4*w) 100000 (80000-i)+bandJumps ws (80000-i)=
      -(pointJump (40000-4*w) 100000 i-pointJump (40000+4*w) 100000 i+bandJumps ws i)
    rw [pointJump_reflect (n := 80001) hi (by omega),pointJump_reflect (n := 80001) hi (by omega),
      ih (fun j hj => h _ (List.mem_cons_of_mem _ hj)),
      show 80001-1-(40000-4*w)=40000+4*w by omega,show 80001-1-(40000+4*w)=40000-4*w by omega]
    ring

end PiPolynomialValues
