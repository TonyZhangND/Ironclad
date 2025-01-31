// TODO eliminate redundancy between these two libraries we've accreted.

module Collections__Maps2_s {

ghost function mapdomain<KT,VT>(m:map<KT,VT>) : set<KT>
{
  set k | k in m :: k
}

ghost function mapremove<KT,VT>(m:map<KT,VT>, k:KT) : map<KT,VT>
{
  map ki | ki in m && ki != k :: m[ki]
}

ghost predicate imaptotal<KT(!new),VT>(m:imap<KT,VT>)
{
  forall k {:trigger m[k]}{:trigger k in m} :: k in m
}
} 
