/- functions -/

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
      dnfhelper (arr.swap i j sorry sorry) (i+1) (j+1) k pvt

    | .gt =>
      dnfhelper (arr.swap j k sorry sorry) i j (k-1) pvt

    | .eq =>
      dnfhelper arr i (j+1) k pvt

  else (arr, i, j)


def dnf [Ord α] -- wrapper
  (arr : Array α) (lo hi : Nat) (pvt : α)
  : Array α × Nat × Nat :=

  dnfhelper arr lo lo hi pvt


/- main algorithm -/

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


def quicksort [Ord α] -- wrapper
  (arr : Array α)
  : Array α :=

  quicksortHelper arr ([(0, arr.size-1)])


/- testing -/

def demoArray : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval (quicksort demoArray) == demoArray.qsort -- is sorted:
