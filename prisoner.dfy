
method benda(L:array<int>, v0:int, v1:int) returns (x:int, y:int)
  // Do no change these.
  requires L != null;
  requires forall i::0 <= i < L.Length ==> 0 <= L[i] < L.Length; // in range
  requires forall i,j::0 <= i < j < L.Length ==> L[i] != L[j]; // distinct
  requires v0 !in L[..] && v1 !in L[..] && v0 != v1;
  modifies L;
  ensures forall j::0 <= j < L.Length ==> L[j] == j; // everyone is switched back
  ensures x == v0 && y == v1; // extras are also switched back
{
  var i;
  i,x,y := 0,v0,v1;
  while (i < L.Length)
  
    // You must provide appropriate loop invariants here
	// For each loop executed, one disjoint cycle is solved. <-- Self Noted
	// After each loop executed, values of array L are same. <-- Self Noted
	//invariant forall j::0 <= j < L.Length ==> 0 <= L[j] < L.Length;
	// Two extra bodies have not swapped their minds in the loop directly. <-- Self Noted
	//invariant x != v1 && y != v0;
	// invariant can be related to set z
	
    {       
    if (L[i] != i) { // if mind of i does not match with body i
      x,L[i] := L[i],x; // swap mind between i and x
	  
      x := cycle(L,i,x,(set z | i < z < L.Length && L[z] != z));

      y,L[x] := L[x],y; // swap minds between y and x
      x,L[x] := L[x],x; // put mind of x back to its body
      y,L[i] := L[i],y; // swap minds between y and i 
    }
    i := i+1;
  }

  // If the two extras are switched at the end, switch back.
  if (x != v0) {
    x,y := y,x;
  } 
}

method cycle(L:array<int>, i:int, a:int, s:set<int>) returns (x:int)
  
  // You must provide appropriate pre-conditions here.
  modifies L;
  decreases s;
  requires L != null;
  requires i >=0;
  requires i < L.Length;
  requires a in s;
  requires s == (set z | i < z < L.Length && L[z] != z);
   
  // You must provide appropriate post-conditions here.
  ensures x >=0;
  ensures x < L.Length;
  ensures (L[x] != i) ==> (L[x] == x);
{ 
  x := a;
  if (L[x] != i) { // mind and body do not match.
    x,L[x] := L[x],x;
    x := cycle(L,i,x,s-{a});
  }
}

method Main()
{
  var a:= new int[5];
  a[0],a[1],a[2],a[3],a[4]:= 3,2,1,4,0;
  var x,y:= benda(a, a.Length, a.Length + 1);
  print a[..]," ",x," ",y,"\n";
}