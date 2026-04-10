/-
  - Sliced (naming: sllo / slhi for unpartitioned functions; lo mid hi fin for dnf) Bounds: always the first index of their area => Upper bounds are exclusive!
-/


/- functions -/

def pivotselect2 [Ord α]
  (arr : Vector α size) (lo hi : Nat)
  : α :=

  let p1 := arr[lo]'sorry
  let p2 := arr[lo + (hi - lo)/2]'sorry
  let p3 := arr[hi - 1]'sorry

  let le := fun a b => compare a b != .gt

  if le p1 p2 then
    if le p2 p3 then p2
    else if le p1 p3 then p3
    else p1
  else
    if le p1 p3 then p1
    else if le p2 p3 then p3
    else p2


partial def dnfhelper2 [Ord α]
  (arr : Vector α size) (pvt : α) (eq unproc fin_unproc : Nat)
  : Vector α size × Nat × Nat :=

  if unproc > fin_unproc then
    (arr, eq, fin_unproc + 1)
  else

    match compare (arr[unproc]'sorry) pvt with
    | .lt => dnfhelper2 (arr.swap unproc eq sorry sorry) pvt (eq + 1) (unproc + 1) fin_unproc
    | .gt => dnfhelper2 (arr.swap unproc fin_unproc sorry sorry) pvt eq unproc (fin_unproc - 1)
    | .eq => dnfhelper2 arr pvt eq (unproc + 1) fin_unproc


def dnf2 [Ord α] -- wrapper
  (arr : Vector α size) (pvt : α) (lo hi : Nat)
  : Vector α size × Nat × Nat :=

  dnfhelper2 arr pvt lo lo (hi - 1)


/- main algorithm -/

partial def quicksorthelper2 [Ord α]
  (arr : Vector α  size) (sllo slhi : Nat)
  : Vector α size :=

  if slhi - sllo ≤ 1 then arr else

  let pvt := pivotselect2 arr sllo slhi--arr[sllo]'sorry
  let (arr_parted, mid, hi) := dnf2 arr pvt sllo slhi

  --if mid - sllo > slhi - hi then --worth it?

    let arr_half_sorted := quicksorthelper2 arr_parted hi slhi
    quicksorthelper2 arr_half_sorted sllo mid

  /-else

    let arr_half_sorted := quicksorthelper2 arr_parted sllo mid
    quicksorthelper2 arr_half_sorted hi slhi-/


def quicksort2 [Ord α] -- wrapper?
  (arr : Array α)
  : Array α :=

  (quicksorthelper2 arr.toVector 0 arr.size).toArray

--missing: Vector.qsort

/- testing -/

def demoArray2 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval (quicksort2 demoArray2) == demoArray2.qsort -- is sorted:
