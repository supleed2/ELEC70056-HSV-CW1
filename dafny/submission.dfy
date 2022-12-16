// Dafny coursework tasks
// Autumn term, 2022
//
// Authors: John Wickerson

method countsquares(n:nat) returns (result:nat)
  ensures result == (n * (n + 1) * (2 * n + 1)) / 6;
{
  var i := 0;
  result := 0;
  while i < n
    invariant 0 <= i <= n;
    decreases n - i;
    invariant result == (i * (i + 1) * (2 * i + 1)) / 6;
  {
    i := i + 1;
    result := result + i * i;
  }
}

method countsquares2(n:nat) returns (result:nat)
  ensures result == (n * (n + 1) * (2 * n + 1)) / 6;
{
  var i := n;
  result := 0;
  while i > 0
    invariant 0 <= i <= n;
    decreases i;
    invariant result == ((n * (n + 1) * (2 * n + 1)) / 6) - ((i * (i + 1) * (2 * i + 1)) / 6);
  {
    result := result + i * i;
    i := i - 1;
  }
}

// countsquares was easier to verify than countsquares2 as the loop invariant
// was the same as the post-condition of the function, as the value of result
// after each loop iteration is simply the result of the function call with a
// smaller input value n.

predicate sorted(A:array<int>)
  reads A;
{
  forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}

method binarysearch_between(A:array<int>, v:int, lo:int, hi:int) returns (result:bool)
  requires sorted(A);
  requires 0 <= lo <= hi <= A.Length;
  decreases hi - lo;
  ensures (exists j :: lo <= j < hi && A[j] == v) <==> result;
{
  if lo == hi {
    return false;
  }
  var mid:int := (lo + hi) / 2;
  if v == A[mid] {
    return true;
  }
  if v < A[mid] {
    result := binarysearch_between(A, v, lo, mid);
  }
  if v > A[mid] {
    result := binarysearch_between(A, v, mid+1, hi);
  }
}

method binarysearch(A:array<int>, v:int) returns (result:bool)
  requires sorted(A);
  ensures (exists j :: 0 <= j < A.Length && A[j] == v) <==> result;
{
  result := binarysearch_between(A, v, 0, A.Length); // call with lo and hi to cover full array
}

method binarysearch_iter(A:array<int>, v:int) returns (result:bool)
  requires sorted(A);
  ensures (exists j :: 0 <= j < A.Length && A[j] == v) <==> result;
{
  result := false;
  var lo := 0;
  var hi := A.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= A.Length;
    invariant forall j :: (0 <= j < lo || hi <= j < A.Length) ==> A[j] != v;
    decreases hi - lo;
  {
    var mid := (lo + hi) / 2;
    if A[mid] > v {
      hi := mid;
    } else if A[mid] < v {
      lo := mid + 1;
    } else {
      return true;
    }
  }
}

method partition(A:array<int>, lo:int, hi:int) returns (pivot:int)
  requires 0 <= lo < hi <= A.Length;
  ensures 0 <= lo <= pivot < hi <= A.Length;
  requires hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi];
  ensures  hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi];
  requires 0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k];
  ensures  0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k];
  ensures forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k];
  ensures forall k :: lo <= k < pivot ==> A[k] < A[pivot];
  ensures forall k :: pivot < k < hi ==> A[pivot] <= A[k];
  modifies A;
{
  pivot := lo;
  var i := lo+1;
  while i < hi
    invariant 0 <= lo <= pivot < i <= hi;
    invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k];
    invariant forall k :: (lo <= k < pivot) ==> A[k] < A[pivot];
    invariant forall k :: (pivot < k < i)   ==> A[pivot] <= A[k];
    invariant hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi];
    invariant 0  < lo       ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k];
  {
    if A[i] < A[pivot] {
      var j := i-1;
      var tmp := A[i];
      A[i] := A[j];
      while pivot < j
        invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k];
        invariant forall k :: (pivot < k <= i)  ==> A[pivot] <= A[k];
        invariant forall k :: (lo <= k < pivot) ==> A[k] < A[pivot];
        invariant A[pivot] > tmp;
        invariant hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi];
        invariant 0  < lo       ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k];
      {
        A[j+1] := A[j];
        j := j-1;
      }
      A[pivot+1] := A[pivot];
      A[pivot] := tmp;
      pivot := pivot+1;
    }
    i := i+1;
  }
}

predicate sorted_between(A: array<int>, lo: int, hi: int)
  reads A;
  requires 0 <= lo <= hi <= A.Length;
{
  forall m, n :: lo <= m < n < hi ==> A[m] <= A[n]
}

method quicksort_between(A:array<int>, lo:int, hi:int)
  requires 0 <= lo <= hi <= A.Length;
  requires hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi];
  ensures  hi < A.Length ==> forall k :: lo <= k < hi ==> A[k] < A[hi];
  requires 0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k];
  ensures  0 < lo ==> forall k :: lo <= k < hi ==> A[lo-1] <= A[k];
  ensures forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k];
  // old(A[k]) evaluates to the value of A[k] on entry to the method, so this
  // checkes that only values in A[lo..hi] can be modified by this method
  ensures sorted_between(A, lo, hi);
  modifies A;
  decreases hi - lo;
{
  if lo+1 >= hi { return; }
  var pivot := partition(A, lo, hi);
  quicksort_between(A, lo, pivot);
  quicksort_between(A, pivot+1, hi);
}

method quicksort(A:array<int>)
  modifies A;
  ensures sorted(A);
{
  quicksort_between(A, 0, A.Length);
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], A[4], A[5], A[6], "\n";
  quicksort(A);
  print "After:  ", A[0], A[1], A[2], A[3], A[4], A[5], A[6], "\n";
}
