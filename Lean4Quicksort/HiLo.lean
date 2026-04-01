/- functions -/

-- pivotselect: select a pivot using the median of start, middle, and end of the array
-- pivotsplit: divide array into smaller than, equal to, or greater than a pivot

def pivotselect [Ord α]
  (arr : Array α) (lo hi : Nat)
  : α :=

    let p1 := arr[lo]'sorry
    let p2 := arr[(hi+lo)/2]'sorry
    let p3 := arr[hi]'sorry

    let le := fun a b => compare a b != .gt

    if le p1 p2 then
      if le p2 p3 then p2
      else if le p1 p3 then p3
      else p1
    else
      if le p1 p3 then p1
      else if le p2 p3 then p3
      else p2


partial def dnfhelper [Ord α]
  (arr : Array α) (i j k : Nat) (pvt : α)
  : Array α × Nat × Nat :=

  if j <= k then
    match compare (arr[j]'sorry) pvt with

    | .lt =>
      let arr := arr.swap i j sorry sorry
      dnfhelper arr (i+1) (j+1) k pvt

    | .gt =>
        if h : k = 0 then
          (arr, i, j)
        else
          let arr := arr.swap j k sorry sorry
          dnfhelper arr i j (k-1) pvt

    | .eq =>
      dnfhelper arr i (j+1) k pvt

  else (arr, i, j)


/- wrappers -/

def dnf [Ord α]
  (arr : Array α) (lo hi : Nat) (pvt : α)
  : Array α × Nat × Nat :=

  dnfhelper arr lo lo hi pvt


/- main algorithm + wrapper -/

partial def quicksortHelper [Ord α]
  (arr : Array α) (tasks : List (Nat × Nat))
  : Array α :=

  match tasks with
  | [] => arr
  | (lo, hi) :: rest =>

    if hi <= lo then
      quicksortHelper arr rest
    else

      let pvt := pivotselect arr lo hi
      let (arr, lt, gt) := dnf arr lo hi pvt

      let nt := (lo, lt-1) :: (gt, hi) :: rest
      quicksortHelper arr nt


def quicksort [Ord α]
  (arr : Array α)
  : Array α :=

  quicksortHelper arr ([(0, arr.size-1)])


/- testing -/

def demoArray1 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval quicksort demoArray1 -- return array:
#eval (quicksort demoArray1) == demoArray1.insertionSort -- is sorted:

def demoArray2 : Array String := #["Byte", "Gamma", "%", "Alpha", "·", "Beta", "Uranium", "$", "Aaron", "Xenon", "G", "e", "f(x)", "Über", "×"]
#eval quicksort demoArray2 -- return array:
#eval (quicksort demoArray2) == demoArray2.insertionSort -- is sorted:

--Version 2: Sliced (naming: sllo / slhi for unpartitioned functions; lo mid hi fin for dnf) (Bounds: always the first index of their area => Upper bounds are exclusive!)

def pivotselect2 [Ord α] (arr : Vector α size) (sllo slhi : Nat) : α :=
  let p1 := arr[sllo]'sorry
  let p2 := arr[sllo + (slhi - sllo)/2]'sorry
  let p3 := arr[slhi - 1]'sorry

  let le := fun a b => compare a b != .gt

  if le p1 p2 then
    if le p2 p3 then p2
    else if le p1 p3 then p3
    else p1
  else
    if le p1 p3 then p1
    else if le p2 p3 then p3
    else p2


partial def dnfhelper2 [Ord α] (arr : Vector α size) (pvt : α) (eq unproc fin_unproc : Nat) : Vector α size × Nat × Nat :=
  if unproc > fin_unproc then (arr, eq, fin_unproc + 1) else
  match compare (arr[unproc]'sorry) pvt with
  | .lt => dnfhelper2 (arr.swap unproc eq sorry sorry) pvt (eq + 1) (unproc + 1) fin_unproc
  | .gt => if fin_unproc = 0 then (arr, 0, 1) else
           dnfhelper2 (arr.swap unproc fin_unproc sorry sorry) pvt eq unproc (fin_unproc - 1)
  | .eq => dnfhelper2 arr pvt eq (unproc + 1) fin_unproc

def dnf2 [Ord α] (arr : Vector α size) (pvt : α) (sllo slhi : Nat) : Vector α size × Nat × Nat :=
  dnfhelper2 arr pvt sllo sllo (slhi - 1)

partial def quicksorthelper2 [Ord α] (arr : Vector α  size) (sllo slhi : Nat) : Vector α size :=
  if slhi - sllo ≤ 1 then arr else
  let pvt := pivotselect2 arr sllo slhi--arr[sllo]'sorry
  let (arr_parted, mid, hi) := dnf2 arr pvt sllo slhi
  --if hi - mid = slhi -sllo then arr_parted else ???
  if mid - sllo > slhi - hi then
    let arr_half_sorted := quicksorthelper2 arr_parted hi slhi
    quicksorthelper2 arr_half_sorted sllo mid
  else
    let arr_half_sorted := quicksorthelper2 arr_parted sllo mid
    quicksorthelper2 arr_half_sorted hi slhi

def quicksort2 [Ord α] (arr : Array α) : Array α :=
  (quicksorthelper2 arr.toVector 0 arr.size).toArray

#eval quicksort2 (demoArray1 ++ demoArray1) -- return array:
#eval (quicksort2 demoArray1) == demoArray1.insertionSort -- is sorted:
