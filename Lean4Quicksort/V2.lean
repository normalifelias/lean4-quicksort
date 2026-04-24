/-
  - Sliced (naming: sllo / slhi for unpartitioned functions; lo mid hi fin for dnf) Bounds: always the first index of their area => Upper bounds are exclusive!
-/


/- functions -/

def pivotselect2 [Ord α] [ToString α]
  (arr : Vector α size) (lo hi : Nat)
  (hlo : lo ≥ 0) (hhi : hi ≤ size) (hlohi : lo < hi)
  : α :=
  if hi - lo ≤ 1 then arr[lo] else
  let p1 := arr[lo]
  let p2 := arr[lo + (hi - lo)/2]
  let p3 := arr[hi - 2]

  let le := fun a b => compare a b != .gt

  if le p1 p2 then
    if le p2 p3 then p2
    else if le p1 p3 then p3
    else p1
  else
    if le p1 p3 then p1
    else if le p2 p3 then p3
    else p2


def dnfhelper2 [Ord α] [ToString α]
  (arr : Vector α size) (pvt : α) (eq unproc fin_unproc : Nat) (sllo slhi : Nat)
  (heq : 0 ≤ eq) (heq_unproc : eq ≤ unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hslhi : fin_unproc < slhi)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size} :=
  /-
  if unproc > fin_unproc then
    (arr, eq, fin_unproc + 1)
  else
  -/
    match compare (arr[unproc]'(by omega)) pvt with
    | .lt =>
      if hfin : unproc ≥ fin_unproc then ⟨((arr.swap unproc eq (by omega) (by omega)), eq + 1, fin_unproc + 1), (by simp; omega)⟩ else
      dnfhelper2 (arr.swap unproc eq (by omega) (by omega)) pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .gt =>
      if hfin : unproc ≥ fin_unproc then ⟨((arr.swap unproc fin_unproc (by omega) (by omega)), eq, fin_unproc), (by simp; omega)⟩ else
      dnfhelper2 (arr.swap unproc fin_unproc (by omega) (by omega)) pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .eq =>
      if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc + 1), (by simp; omega)⟩ else
      dnfhelper2 arr pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


def dnf2 [Ord α] [ToString α]-- wrapper
  (arr : Vector α size) (pvt : α) (sllo slhi : Nat)
  (hlo : 0 ≤ sllo) (hlohi : sllo < slhi) (hhi : slhi ≤ size)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size} :=
  --dbg_trace s!"pvt: {pvt}, sllo: {sllo}, slhi: {slhi}"
  dnfhelper2 arr pvt sllo sllo (slhi - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

-- add theorem : If pvt is in arr, then mid < hi, not only mid ≤ hi => termination proof fpr quicksorthelper2?
/- main algorithm -/

partial def quicksorthelper2 [Ord α] [ToString α]
  (arr : Vector α  size) (sllo slhi : Nat)
  (hsllo : 0 ≤ sllo) (hslloslhi : sllo ≤ slhi) (hslhi : slhi ≤ size)
  : Vector α size :=

  if hfin : slhi - sllo ≤ 1 then arr else
  --dbg_trace s!"Array: {arr.toArray}"
  let pvt : α := pivotselect2 arr sllo slhi (by omega) (by omega) (by omega)
  let ⟨(arr_parted, mid, hi), ⟨h1, h2, h3⟩⟩ := dnf2 arr pvt sllo slhi (by omega) (by omega) (by omega)

  --if mid - sllo > slhi - hi then --worth it?

    let arr_half_sorted := quicksorthelper2 arr_parted hi slhi (by omega) (by omega) (by omega)
    quicksorthelper2 arr_half_sorted sllo mid (by omega) (by omega) (by omega)

  /-else

    let arr_half_sorted := quicksorthelper2 arr_parted sllo mid
    quicksorthelper2 arr_half_sorted hi slhi-/


def Array.quicksort2 [Ord α] [ToString α] --wrapper
  (arr : Array α)
  : Array α :=

  (quicksorthelper2 arr.toVector 0 arr.size (by decide) (by omega) (by omega)).toArray



def Vector.quicksort2 [Ord α] [ToString α] {size} (arr : Vector α size) : Vector α size:=
  quicksorthelper2 arr 0 size (by decide) (by omega) (by omega)

/- testing -/

def demoArray2 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval! (Array.quicksort2 (Array.range 32)) == demoArray2.qsort -- is sorted:
