/- datatypes and structures -/

-- Todo: differentiate tasks between unsorted numbers and finished numbers

inductive Todo (α : Type)
| Sort : Array α → Todo α
| Push : Nat -> α → Todo α


/- functions -/

-- pivotselect: select a pivot using the median of start, middle, and end of the array
-- pivotsplit: divide array into smaller than, equal to, or greater than a pivot

def pivotselect [Ord α] (arr : Array α) : Option (α) :=

  if h : arr.size = 0 then
    none
  else if arr.size < 3 then
    some arr[0]
  else

    let size := arr.size
    let half := size/2

    let p1 := arr[0]
    let p2 := arr[half]
    let p3 := arr[size - 1]

    let le := fun a b => compare a b != .gt

    if le p1 p2 then
      if le p2 p3 then some p2
      else if le p1 p3 then some p3
      else some p1
    else
      if le p1 p3 then some p1
      else if le p2 p3 then some p3
      else some p2


def pivotsplitHelper [Ord α] (i eq : Nat) (arr lt gt : Array α) (pvt : α) : Array α × Nat × Array α :=

  if h : i >= arr.size then
    (lt, eq, gt)
  else

    let x := arr[i]

    match compare x pvt with
    | .lt => pivotsplitHelper (i+1) eq arr (lt.push x) gt pvt
    | .eq => pivotsplitHelper (i+1) (eq+1) arr lt gt pvt
    | .gt => pivotsplitHelper (i+1) eq arr lt (gt.push x) pvt

termination_by arr.size - i



/- wrappers -/

def pivotsplit [Ord α] (arr : Array α) (pvt : α): Array α × Nat × Array α :=

  pivotsplitHelper 0 0 arr #[] #[] pvt


/- main algorithm + wrapper -/

-- quicksort: uses a Todo list and pivotsplit/select to progress through list and sort an array

partial def quicksortHelper [Ord α] (todos : List (Todo α)) (acc : Array α) : Array α :=

  match todos with
  | [] => acc
  | inst :: rest =>

    match inst with
    | Todo.Push n x => quicksortHelper rest (acc.append (Array.replicate n x))
    | Todo.Sort arr =>

      match pivotselect arr with
      | none => quicksortHelper rest acc
      | some pvt =>

        let (lt, eq, gt) := pivotsplit arr pvt
        let new := Todo.Sort lt :: Todo.Push eq pvt :: Todo.Sort gt :: rest

        quicksortHelper new acc


def quicksort [Ord α] (arr : Array α) :=

  let acc : Array α := (Array.mkEmpty arr.size)

  quicksortHelper [Todo.Sort arr] acc


/- testing -/

def demoArray1 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval quicksort demoArray1 -- return array:
#eval (quicksort demoArray1) == demoArray1.insertionSort -- is sorted:

def demoArray2 : Array String := #["Byte", "Gamma", "%", "Alpha", "·", "Beta", "Uranium", "$", "Aaron", "Xenon", "G", "e", "f(x)", "Über", "×"]
#eval quicksort demoArray2 -- return array:
#eval (quicksort demoArray2) == demoArray2.insertionSort -- is sorted:
