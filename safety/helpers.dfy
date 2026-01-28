predicate LessThan(v1: Vector, v2: Vector)
requires v1.Keys == v2.Keys
{
  && (forall p <- v1.Keys :: v1[p] <= v2[p])
  && (exists p <- v1.Keys :: v1[p] < v2[p])
}

predicate LessThanEq(v1: Vector, v2: Vector)
requires v1.Keys == v2.Keys
{
  && (forall p <- v1.Keys :: v1[p] <= v2[p])
}

predicate LessThanEqSrc(v1: Vector, v2: Vector, src: Process)
requires v1.Keys == v2.Keys
{
  && (forall p <- v1.Keys | p != src :: v1[p] <= v2[p])
}

predicate LessThanEq2(v1: Vector, v2: map<(Process, Process), nat>, p: Process, q: Process)
requires forall r <- v1.Keys :: (p, r) in v2.Keys
{
  && (forall r <- v1.Keys | r != q :: v1[r] <= v2[(p,r)])
}


method getMaxVector(v1: Vector, v2: Vector)
returns (maxV: Vector)
requires v1.Keys == v2.Keys
ensures maxV.Keys == v1.Keys
ensures forall p <- v1.Keys :: if v1[p] > v2[p] then maxV[p] == v1[p] else maxV[p] == v2[p]
{
  maxV := map p <- v1.Keys :: 0;
  var keys := v1.Keys;

  while keys != {} 
    decreases |keys|
    invariant keys <= v1.Keys
    invariant maxV.Keys == v1.Keys
    invariant forall p <- v1.Keys - keys :: if v1[p] > v2[p] then maxV[p] == v1[p] else maxV[p] == v2[p]
    {
      var q :| q in keys;
      if v1[q] > v2[q] {
        maxV := maxV[q := v1[q]];
      } else {
        maxV := maxV[q := v2[q]];
      }
      keys := keys - {q};
    }
}

method getMaxVector2(v1: Vector, v2: Vector)
returns (maxV: Vector)
requires v1.Keys == v2.Keys
ensures maxV.Keys == v1.Keys == v2.Keys
ensures forall p <- maxV.Keys :: (maxV[p] == v1[p] || maxV[p] == v2[p]) && (maxV[p] >= v1[p]) && (maxV[p] >= v2[p]) 
{
  maxV := map p <- v1.Keys :: 0;
  var keys := v1.Keys;

  while keys != {} 
    decreases |keys|
    invariant keys <= v1.Keys
    invariant maxV.Keys == v1.Keys
    invariant forall p <- v1.Keys - keys :: if v1[p] > v2[p] then maxV[p] == v1[p] else maxV[p] == v2[p]
    {
      var q :| q in keys;
      if v1[q] > v2[q] {
        maxV := maxV[q := v1[q]];
      } else {
        maxV := maxV[q := v2[q]];
      }
      keys := keys - {q};
    }
}

method getVCsMaxAtP(VCs: map<(Process, Process), nat>, v1: Vector, q:Process)
returns (maxV: map<(Process, Process), nat>)
requires forall r <- v1.Keys :: ((r, q) in VCs.Keys)
requires q in v1.Keys
ensures maxV.Keys == VCs.Keys
ensures forall p:Process :: (p,q) in maxV.Keys && p in v1.Keys ==> ((maxV[(p, q)] == v1[p] || maxV[(p, q)] == VCs[(p, q)]) && (maxV[(p, q)] >= v1[p]) && (maxV[(p, q)] >= VCs[(p, q)]))
{
  // maxV := map p <- v1.Keys :: 0;
  // var keys := v1.Keys;

  // while keys != {} 
  //   decreases |keys|
  //   invariant keys <= v1.Keys
  //   invariant maxV.Keys == v1.Keys
  //   invariant forall p <- v1.Keys - keys :: if v1[p] > v2[p] then maxV[p] == v1[p] else maxV[p] == v2[p]
  //   {
  //     var q :| q in keys;
  //     if v1[q] > v2[q] {
  //       maxV := maxV[q := v1[q]];
  //     } else {
  //       maxV := maxV[q := v2[q]];
  //     }
  //     keys := keys - {q};
  //   }
  maxV := VCs;
}

function maxx(n1: nat, n2: nat) : nat
{
  if n1 > n2 then  n1
  else n2
}



function vectorMax(v1: Vector, v2: Vector, p:Process) : Vector
requires v1.Keys == v2.Keys
{
  map i <- v1.Keys - {p} :: maxx(v1[i], v2[i])
}

function getPVectorFromMap(vectorMap: map<(Process, Process), nat>, keys:set<Process>, p: Process) : Vector
requires forall r <- keys :: ((p, r) in vectorMap.Keys)
requires p in keys
ensures forall q <- getPVectorFromMap(vectorMap, keys, p).Keys :: getPVectorFromMap(vectorMap, keys, p)[q] == vectorMap[(p,q)]
ensures  getPVectorFromMap(vectorMap, keys, p).Keys == keys
//ensures forall q <- v.Keys :: v[q] == vectorMap[(p,q)]
{
  map i: Process | i in keys :: vectorMap[(p,i)]
}

method test(s:System)
requires s.Valid()
{
  // s.delivered := s.delivered[(src, dst) := delivered[(src, dst)] + [m]];
}
