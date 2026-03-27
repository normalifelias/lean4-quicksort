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


partial def pivotsplitHelper [Ord α]
  (arr lt gt : Array α) (ind hi eq : Nat) (pvt : α)
  : Array α × Nat × Array α :=

  if h: ind > hi then
    (lt, eq, gt)

  else
    let x := arr[ind]'sorry
    match compare x pvt with
    | .lt => pivotsplitHelper arr (lt.push x) gt (ind+1) hi eq pvt
    | .eq => pivotsplitHelper arr lt gt (ind+1) hi (eq+1) pvt
    | .gt => pivotsplitHelper arr lt (gt.push x) (ind+1) hi eq pvt


/- wrappers -/

def pivotsplit [Ord α]
  (arr : Array α) (lo hi : Nat) (pvt : α)
  : Array α × Nat × Array α :=

  pivotsplitHelper arr #[] #[] lo hi 0 pvt


/- main algorithm + wrapper -/

partial def quicksortHelper [Ord α]
  (arr : Array α) (tasks : List (Nat × Nat))
  : Array α :=

  match tasks with
  | [] => arr
  | (lo, hi) :: rest =>

    let pre := arr.extract 0 lo
    let post := arr.extract (hi+1) arr.size

    if hi-lo < 28 then
      let ts := arr.extract lo (hi+1)

      let lt := fun a b => compare a b == .lt
      let srt := ts.insertionSort lt

      let na := pre ++ srt ++ post

      quicksortHelper na rest

    else
      let pvt := pivotselect arr lo hi
      let (lt, eq, gt) := pivotsplit arr lo hi pvt

      let na := pre ++ lt ++ Array.replicate eq pvt ++ gt ++ post
      let nt := (lo, (lo+lt.size-1)) :: ((lo+lt.size+eq), hi) :: rest

      quicksortHelper na nt


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
