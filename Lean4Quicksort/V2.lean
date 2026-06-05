/-
  - Sliced (naming: sllo / slhi for unpartitioned functions; lo mid hi fin for dnf) Bounds: always the first index of their area => Upper bounds are exclusive!
-/


/- functions -/

def qinsertionSort [Ord α]
  (arr : Vector α size) (lo hi i : Nat)
  (hlohi : lo < hi) (hhi : hi ≤ size)
  (hilo : lo ≤ i) (hihi : i ≤ hi)
  : Vector α size :=

  if hfin : i = hi then arr else

  let rec movedown [Ord α] (arr : Vector α size) (j : Nat) (hjlo : lo ≤ j) (hjhi : j < hi) : Vector α size :=

    if hfin : j = lo then arr else

    if compare (arr[j]) (arr[j - 1]) = .lt then

      movedown (arr.swap j (j - 1)) (j - 1) (by omega) (by omega)

    else arr

  qinsertionSort (movedown arr i (by omega) (by omega)) lo hi (i + 1) (by omega) (by omega) (by omega) (by omega)


def pivotselect2 [Ord α]
  (arr : Vector α size) (lo hi : Nat)
  (hhi : hi ≤ size) (hlohi : lo < hi)
  : α :=

  let p1 := arr[lo]
  let p2 := arr[lo + (hi - lo)/2]
  let p3 := arr[hi - 1]

  let le := fun a b => compare a b != .gt

  if le p1 p2 then
    if le p2 p3 then p2
    else if le p1 p3 then p3
    else p1
  else
    if le p1 p3 then p1
    else if le p2 p3 then p3
    else p2


def pivotselect3 [Ord α]
  (arr : Vector α size) (lo hi : Nat)
  (hhi : hi ≤ size) (hlohi : lo < hi)
  : {idx : Nat // lo ≤ idx ∧ idx < hi} :=

  let p1 := arr[lo]
  let p2 := arr[lo + (hi - lo)/2]
  let p3 := arr[hi - 1]

  let le := fun a b => compare a b != .gt

  if le p1 p2 then
    if le p2 p3 then ⟨lo + (hi - lo)/2, (by omega)⟩
    else if le p1 p3 then ⟨hi - 1, (by omega)⟩
    else ⟨lo, (by omega)⟩
  else
    if le p1 p3 then ⟨lo, (by omega)⟩
    else if le p2 p3 then ⟨hi - 1, (by omega)⟩
    else ⟨lo + (hi - lo)/2, (by omega)⟩


def dnfhelper3 [Ord α]
  (arr : Vector α size) (eq unproc fin_unproc : Nat) (sllo slhi : Nat)
  (heq_unproc : eq < unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hfin_unproc_slhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1) (hslhi : slhi ≤ size)


  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=
  /-
  if unproc > fin_unproc then
    (arr, eq, fin_unproc + 1)
  else
  -/
    match compare arr[unproc] arr[eq] with
    | .lt =>
      if hfin : unproc ≥ fin_unproc then ⟨((arr.swap unproc eq (by omega) (by omega)), eq + 1, fin_unproc + 1), (by simp; omega)⟩ else
      dnfhelper3 arr  (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .gt =>
      if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc), (by simp; omega)⟩ else
      if compare arr[fin_unproc] arr[unproc] = .gt then dnfhelper3 arr  eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)  else
      dnfhelper3 (arr.swap unproc fin_unproc (by omega) (by omega))  eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .eq =>
      if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc + 1), (by simp; omega)⟩ else
      dnfhelper3 arr  eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


-- IDEA: Carry index of pvt instead of pvt itself => already proven that pvt ∈ arr!

def dnfhelper2 [Ord α]
  (arr : Vector α size) (pvt : α) (eq unproc fin_unproc : Nat) (sllo slhi : Nat)
  (heq_unproc : eq ≤ unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hslhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size} :=
  /-
  if unproc > fin_unproc then
    (arr, eq, fin_unproc + 1)
  else
  -/
    match compare (arr[unproc]) pvt with
    | .lt =>
      if hfin : unproc ≥ fin_unproc then ⟨((arr.swap unproc eq (by omega) (by omega)), eq + 1, fin_unproc + 1), (by simp; omega)⟩ else
      if compare arr[eq] arr[unproc] = .lt then dnfhelper2 arr pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
      dnfhelper2 (arr.swap unproc eq (by omega) (by omega)) pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .gt =>
      if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc), (by simp; omega)⟩ else
      if compare arr[fin_unproc] arr[unproc] = .gt then dnfhelper2 arr pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
      dnfhelper2 (arr.swap unproc fin_unproc (by omega) (by omega)) pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .eq =>
      if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc + 1), (by simp; omega)⟩ else
      dnfhelper2 arr pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


def dnfhelper4 [Ord α]
  (arr : Vector α size) (pvt eq unproc fin_unproc : Nat) (sllo slhi : Nat)
  (heq_unproc : eq ≤ unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hfin_unproc_slhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1) (hslhi : slhi ≤ size)
  (hpvt_sllo : sllo ≤ pvt) (hpvt_slhi : pvt < slhi) (hpvt_eq : eq ≤ pvt) (hpvt_fin_unproc : pvt ≤ fin_unproc)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  match hcmp : compare (arr[unproc]) (arr[pvt]) with
  | .lt =>
    if hfin : unproc ≥ fin_unproc then ⟨((arr.swap unproc eq), eq + 1, fin_unproc + 1), by simp; sorry⟩ else
    if hpvt : eq = pvt then dnfhelper4 (arr.swap unproc eq) unproc (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by sorry) (by omega) else
    if compare (arr[eq]) (arr[unproc]) = .lt then dnfhelper4 arr pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    dnfhelper4 (arr.swap unproc eq) pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .gt =>
    if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc), by simp; sorry⟩ else
    if hpvt : fin_unproc = pvt then dnfhelper4 (arr.swap unproc fin_unproc) unproc eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    if compare (arr[fin_unproc]) (arr[unproc]) = .gt then dnfhelper4 arr pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    else dnfhelper4 (arr.swap unproc fin_unproc) pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .eq =>
    if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc + 1), by simp; omega⟩ else
    dnfhelper4 arr pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)



def dnf3 [Ord α] -- wrapper
  (arr : Vector α size) (pvt : Nat) (sllo slhi : Nat)
  (hlohi : slhi - sllo > 1) (hhi : slhi ≤ size)
  (hpvt : sllo ≤ pvt ∧ pvt < slhi)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=
  --dbg_trace s!"pvt: {pvt}, sllo: {sllo}, slhi: {slhi}"
  dnfhelper3 (arr.swap pvt sllo) sllo (sllo+1) (slhi - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


def dnf2 [Ord α] -- wrapper
  (arr : Vector α size) (pvt : α) (sllo slhi : Nat)
  (hlohi : slhi - sllo > 1) (hhi : slhi ≤ size)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size} :=
  --dbg_trace s!"pvt: {pvt}, sllo: {sllo}, slhi: {slhi}"
  dnfhelper2 arr pvt sllo sllo (slhi - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


def dnf4 [Ord α]
  (arr : Vector α size) (pvt : Nat) (sllo slhi : Nat)
  (hlohi : slhi - sllo > 1) (hhi : slhi ≤ size)
  (hpvt : sllo ≤ pvt ∧ pvt < slhi)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  dnfhelper4 arr pvt sllo sllo (slhi - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)







def dnfstage2 [Ord α]
  (arr : Vector α size) (pvt eq unproc fin_unproc : Nat) (sllo slhi : Nat)
  (heq_unproc : eq < unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hfin_unproc_slhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1) (hslhi : slhi ≤ size)
  (hpvt_sllo : sllo ≤ pvt) (hpvt_slhi : pvt < slhi) (hpvt_eq : eq ≤ pvt) (hpvt_fin_unproc : pvt ≤ fin_unproc)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  match compare arr[unproc] arr[pvt] with
  | .lt =>
    if hfin : unproc ≥ fin_unproc then ⟨((arr.swap unproc eq), eq + 1, fin_unproc + 1), by simp; omega⟩ else
    if hpvt : eq = pvt then dnfstage2 (arr.swap unproc eq) unproc (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    if compare (arr[eq]) (arr[unproc]) = .lt then dnfstage2 arr pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    dnfstage2 (arr.swap unproc eq) pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .gt =>
    if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc), by simp; omega⟩ else
    if hpvt : fin_unproc = pvt then dnfstage2 (arr.swap unproc fin_unproc) unproc eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    if compare (arr[fin_unproc]) (arr[unproc]) = .gt then dnfstage2 arr pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    else dnfstage2 (arr.swap unproc fin_unproc) pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .eq =>
    if hfin : unproc ≥ fin_unproc then ⟨(arr, eq, fin_unproc + 1), by simp; omega⟩ else
    dnfstage2 arr pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)





def dnfstage1 [Ord α]
  (arr : Vector α size) (pvt eq unproc fin_unproc : Nat) (sllo slhi : Nat)
  (heq_unproc : eq ≤ unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hfin_unproc_slhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1) (hslhi : slhi ≤ size)
  (hpvt_sllo : sllo ≤ pvt) (hpvt_slhi : pvt < slhi) (hpvt_unproc : unproc ≤ pvt) (hpvt_fin_unproc : pvt ≤ fin_unproc)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  if hpvt : unproc = pvt then
    if hfin : fin_unproc = unproc then ⟨(arr, eq, fin_unproc + 1), by simp; omega⟩
    else dnfstage2 arr pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  else match compare arr[unproc] arr[pvt] with
  | .lt =>
    --if hfin : fin_unproc ≤ unproc then ⟨(arr.swap eq unproc, eq + 1, fin_unproc + 1), by simp; omega⟩ else
    dnfstage1 (arr.swap eq unproc) pvt (eq+1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .gt =>
    if hfin : fin_unproc = unproc then ⟨(arr, eq, fin_unproc), by simp; omega⟩ else
    if hfin2 : fin_unproc - unproc = 1 then ⟨(arr.swap unproc fin_unproc, eq, fin_unproc), by simp; omega⟩ else
    if hpvt2 : pvt = fin_unproc then dnfstage2 (arr.swap unproc pvt) unproc eq (unproc + 1) (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    dnfstage1 (arr.swap unproc fin_unproc) pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .eq =>
    dnfstage2 arr pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


def dnfstaged [Ord α]
  (arr : Vector α size) (pvt : Nat) (sllo slhi : Nat)
  (hlohi : slhi - sllo > 1) (hhi : slhi ≤ size)
  (hpvt : sllo ≤ pvt ∧ pvt < slhi)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  dnfstage1 arr pvt sllo sllo (slhi - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)



















-- add theorem : If pvt is in arr, then mid < hi, not only mid ≤ hi => termination proof fpr quicksorthelper2?
/- main algorithm -/

def quicksorthelper2 [Ord α]
  (arr : Vector α  size) (sllo slhi : Nat)
  (hsllo : 0 ≤ sllo) (hslloslhi : sllo ≤ slhi) (hslhi : slhi ≤ size)
  : Vector α size :=

  if hfin : slhi - sllo ≤ 1 then arr else
  if slhi - sllo ≤ 16 then qinsertionSort arr sllo slhi (sllo + 1) (by omega) (by omega) (by omega) (by omega) else
  --dbg_trace s!"Array: {arr.toArray}"
  /-let pvt : α := pivotselect2 arr sllo slhi (by omega) (by omega)
  let ⟨(arr_parted, mid, hi), ⟨h1, h2, h3⟩⟩ := dnf2 arr pvt sllo slhi (by omega) (by omega)-/
  let pvt := pivotselect3 arr sllo slhi (by omega) (by omega)
  let ⟨(arr_parted, mid, hi), ⟨h1, h2, h3⟩⟩ := (dnfstaged arr pvt sllo slhi (by omega) (by omega) (by omega))

  --if mid - sllo > slhi - hi then --worth it?
    have hterm : slhi - hi < slhi - sllo := by simp only [] at h1 h2 h3; omega
    let arr_half_sorted := quicksorthelper2 arr_parted hi slhi (by omega) (by omega) (by omega)
    have hterm2 : mid - sllo < slhi - sllo := by simp only [] at h1 h2 h3; omega
    quicksorthelper2 arr_half_sorted sllo mid (by omega) (by omega) (by omega)

  /-else

    let arr_half_sorted := quicksorthelper2 arr_parted sllo mid
    quicksorthelper2 arr_half_sorted hi slhi-/
termination_by slhi - sllo

def Array.quicksort2 [Ord α]  --wrapper
  (arr : Array α)
  : Array α :=

  (quicksorthelper2 arr.toVector 0 arr.size (by decide) (by omega) (by omega)).toArray



def Vector.quicksort2 [Ord α]  {size} (arr : Vector α size) : Vector α size:=
  quicksorthelper2 arr 0 size (by decide) (by omega) (by omega)

/- testing -/

def demoArray2 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval! (Array.quicksort2 demoArray2) == demoArray2.qsort -- is sorted:
